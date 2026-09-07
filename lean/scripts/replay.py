"""Portable, dependency-ordered replay of the publication source package.

This runner generates new evidence; it never treats a dry run as Lean checking.
Run on a compute node, not a cluster login node. No Slurm submission is hidden.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import source_layout


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def source_check(lean: Path) -> tuple[dict, dict]:
    source_layout.check(lean.parent)
    evidence = lean.parent/'evidence/verification'
    acceptance = read(evidence/'acceptance.json')
    order = read(evidence/'publication-build-order.json')
    modules = order['moduleOrder']
    if len(modules) != len(set(modules)) or len(modules) != acceptance['checkedModules']:
        raise ValueError('module inventory differs')
    seen = set()
    for module in modules:
        if not re.fullmatch(r'BerryEsseen(?:\.[A-Za-z][A-Za-z0-9_]*)+', module):
            raise ValueError('invalid module name')
        if any(d in modules and d not in seen for d in order['imports'][module]):
            raise ValueError('dependency order differs: '+module)
        seen.add(module)
    expected_axioms = {'propext', 'Classical.choice', 'Quot.sound'} | {
        t+'._native.native_decide.ax_1_1' for t in order['nativeTheorems'].values()}
    axioms = (evidence/'publication-axioms.txt').read_text().splitlines()
    if len(axioms) != len(expected_axioms) or set(axioms) != expected_axioms:
        raise ValueError('axiom inventory differs')
    return acceptance, order


def command(args: list[str], cwd: Path, *, env=None) -> str:
    return subprocess.check_output(args, cwd=cwd, env=env, text=True, encoding='utf-8').strip()


def replay(lean: Path, output: Path, jobs: int) -> dict:
    acceptance, order = source_check(lean)
    root = lean.parent
    internal = set(order['moduleOrder'])
    if jobs < 1:
        raise ValueError('jobs must be positive')
    version = command(['lake', 'env', 'lean', '--version'], root)
    if not version.startswith('Lean (version 4.29.1,'):
        raise ValueError('expected Lean 4.29.1, got '+version)
    # Only analytic external roots, not the historical 0.45 aggregate.
    external = sorted({d for ds in order['imports'].values() for d in ds if d not in internal})
    subprocess.run(['lake', 'build', *external], cwd=root, check=True)
    for package in read(root/'lake-manifest.json')['packages']:
        actual = command(['git', '-C', str(root/'.lake/packages'/package['name']), 'rev-parse', 'HEAD'], root)
        if actual != package['rev']:
            raise ValueError('dependency revision differs: '+package['name'])
    lake_environment = json.loads(command(['lake', 'env', sys.executable, '-c',
        'import json,os; print(json.dumps(dict(os.environ)))'], root))
    dependency_path = lake_environment['LEAN_PATH']
    lean_prefix = Path(command(['lake', 'env', 'lean', '--print-prefix'], root))
    lean_binary = lean_prefix/'bin'/('lean.exe' if os.name == 'nt' else 'lean')
    searches = [Path(p) if Path(p).is_absolute() else root/p for p in dependency_path.split(os.pathsep)]
    external_hashes = {}
    for module in external:
        relative = Path(*module.split('.')).with_suffix('.olean')
        path = next((p/relative for p in searches if (p/relative).is_file()), None)
        if path is None:
            raise ValueError('external object missing: '+module)
        external_hashes[module] = sha(path)
    identity = {'snapshotId':acceptance['snapshotId'], 'leanVersion':version,
                'sourceLayoutSha256':sha(root/'evidence/verification/source-layout.json'),
                'lakeManifestSha256':sha(root/'lake-manifest.json'), 'externalObjects':external_hashes}
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    identity_file = output/'identity.json'
    if identity_file.exists():
        if read(identity_file) != identity:
            raise ValueError('existing replay has different dependencies; choose a new output directory')
    else:
        identity_file.write_text(json.dumps(identity, indent=2, sort_keys=True)+'\n')
    for directory in ['lib','records','logs']:
        (output/directory).mkdir(exist_ok=True)
    env = dict(lake_environment, LEAN_PATH=str(output/'lib')+os.pathsep+dependency_path)
    # LEAN_PATH points at the source package's original dependency tree, not
    # at copied or downloaded native witnesses. Every missing module is rebuilt.
    done: dict[str, str] = {}
    pending = set(order['moduleOrder'])
    running: dict[cf.Future, str] = {}

    def build(module: str, imports: dict[str,str]) -> str:
        source = (lean/Path(*module.split('.'))).with_suffix('.lean')
        obj = (output/'lib'/Path(*module.split('.'))).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        record = output/'records'/(module+'.json')
        log = output/'logs'/(module+'.log')
        key = {'module':module, 'sourceSha256':sha(source), 'imports':imports}
        if record.exists():
            previous = read(record)
            if (all(previous.get(k) == v for k,v in key.items()) and
                obj.is_file() and sha(obj) == previous.get('oleanSha256') and
                log.is_file() and sha(log) == previous.get('logSha256') and previous.get('exitCode') == 0):
                return previous['oleanSha256']
            raise ValueError('invalid checkpoint: '+module)
        temp = obj.with_suffix('.olean.part')
        # Do not run another `lake env`: it would reconstruct LEAN_PATH and
        # could discard the newly built publication object directory.
        args = [str(lean_binary),'-j1','--tstack=32768','-R',str(lean),
                '-o',str(temp),str(source)]
        started = time.monotonic()
        with log.open('w', encoding='utf-8') as handle:
            result = subprocess.run(args, cwd=root, env=env, stdout=handle, stderr=subprocess.STDOUT)
        if result.returncode or not temp.is_file():
            raise RuntimeError('Lean failed for '+module+'; see '+str(log))
        text = log.read_text()
        if 'sorryAx' in text:
            raise RuntimeError('unaccepted sorryAx in '+module)
        temp.replace(obj)
        value = dict(key, oleanSha256=sha(obj), logSha256=sha(log), exitCode=0,
                     elapsedSeconds=time.monotonic()-started, command=args)
        record.write_text(json.dumps(value, sort_keys=True, indent=2)+'\n')
        return value['oleanSha256']

    with cf.ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            for module in order['moduleOrder']:
                if len(running) == jobs:
                    break
                if module not in pending:
                    continue
                deps = [d for d in order['imports'][module] if d in internal]
                if all(d in done for d in deps):
                    imports = {d:done[d] if d in internal else external_hashes[d]
                               for d in order['imports'][module]}
                    running[pool.submit(build,module,imports)] = module
                    pending.remove(module)
            if not running:
                raise RuntimeError('dependency scheduler stalled')
            completed, _ = cf.wait(running, return_when=cf.FIRST_COMPLETED)
            for future in completed:
                module = running.pop(future)
                done[module] = future.result()
                print(f'{len(done)}/{len(order["moduleOrder"])} {module}', flush=True)
    audit_log = (output/'logs/BerryEsseen.Verification.FinalAxiomAudit.log').read_text()
    lists = re.findall(r'depends on axioms:\s*\[([^\]]*)\]',audit_log,re.S)
    if len(lists) != 1:
        raise ValueError('missing or ambiguous final axiom output')
    actual = [x.strip().strip("'").removeprefix('BerryEsseen.') for x in lists[0].split(',')]
    expected = (root/'evidence/verification/publication-axioms.txt').read_text().splitlines()
    if len(actual) != len(expected) or set(actual) != set(expected):
        raise ValueError('final axiom set differs')
    receipt = dict(identity, status='PASS', checkedModules=len(done), nativeWitnesses=2407,
                   finalAxioms=sorted(actual), proofEvidence=False,
                   scope='Fresh portable Lean replay; separate manuscript and human-proof gates.')
    (output/'REPLAY_READY.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-sources', action='store_true', help='read-only; does not execute Lean')
    parser.add_argument('--build-dir', type=Path, default=Path('.runtime/replay'))
    parser.add_argument('--jobs', type=int, default=8)
    options = parser.parse_args()
    lean = Path(__file__).resolve().parents[1]
    if options.check_sources:
        acceptance, order = source_check(lean)
        print(json.dumps({'status':'PASS','scope':'source and inventory checks only',
                          'modules':len(order['moduleOrder']),'snapshotId':acceptance['snapshotId']}))
    else:
        replay(lean, options.build_dir, options.jobs)
