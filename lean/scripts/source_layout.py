"""Check a publication layout against the immutable executed source archive.

This is a source-transformation check, not a Lean replay. The archived source
must match its original manifest before the permitted transformation is applied.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile


ROOT = Path(__file__).resolve().parents[2]
EVIDENCE = ROOT / 'evidence/verification'
LAYOUT = ROOT / 'evidence/verification/source-layout.json'
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def transform(data: bytes, entry: dict, mapping: dict) -> bytes:
    """Only module imports, identifiers, include paths and comments may change.

    Quoted string contents are preserved, except include_str paths. In
    particular certificate topology strings and extraction markers are unchanged.
    Nested Lean comments and escaped quotes are handled explicitly.
    """
    text = data.decode('utf-8')
    # Module docstrings are replaced by a content-based module heading.
    if '/-!' in text:
        start = text.index('/-!')
        end = comment_end(text, start)
        text = text[:start] + '/-!\n# ' + entry['title'] + '\n-/'+text[end:]
    text = re.sub(r'(?m)^import (\S+)',
                  lambda m: 'import '+mapping['modules'].get(m[1],m[1]), text)
    def include(m):
        old = Path(entry['oldPath']).parent / m[1]
        old_key = (ROOT/'lean'/old).resolve().relative_to(ROOT/'lean').as_posix()
        target = ROOT/mapping.get('literalPaths',{}).get(old_key,'lean/'+old_key)
        base = (ROOT/entry['newPath']).parent.resolve()
        import os
        return 'include_str "'+Path(os.path.relpath(target,base)).as_posix()+'"'
    text = re.sub(r'include_str\s+"([^"]+)"',include,text)
    out=[]
    i=0
    while i<len(text):
        if text.startswith('/-',i):
            end=comment_end(text,i)
            comment=text[i:end]
            comment=comment.replace('Path 2','the first-absolute-moment bounds')
            comment=comment.replace('Path 1','the baseline bound')
            out.append(WORD.sub(lambda m:mapping['identifiers'].get(m[0],m[0]),comment))
            i=end
        elif text.startswith('--',i):
            end=text.find('\n',i)
            if end<0: end=len(text)
            out.append(text[i:end].replace('Path 2','the refined bound').replace('Path 1','the baseline bound'))
            i=end
        elif text[i]=="'" and (char:=re.match(r"'(?:\\.|[^'\\])'",text[i:])):
            out.append(char[0]); i+=len(char[0])
        elif text[i]=='"':
            end=i+1
            while end<len(text):
                if text[end]=='\\': end+=2
                elif text[end]=='"':
                    end+=1
                    break
                else: end+=1
            out.append(text[i:end]); i=end
        else:
            m=WORD.match(text,i)
            if m:
                out.append(mapping['identifiers'].get(m[0],m[0])); i=m.end()
            else:
                out.append(text[i]); i+=1
    return ''.join(out).encode('utf-8')


def comment_end(text: str,start: int) -> int:
    depth=1; i=start+2
    while i<len(text):
        if text.startswith('/-',i): depth+=1; i+=2
        elif text.startswith('-/',i):
            depth-=1; i+=2
            if depth==0: return i
        else: i+=1
    raise ValueError('unterminated Lean comment')


def check(root: Path=ROOT) -> dict:
    mapping=json.loads((root/'evidence/verification/source-layout.json').read_text(encoding='utf-8'))
    if len(set(mapping['modules'].values()))!=len(mapping['modules']):
        raise ValueError('module renaming is not one-to-one')
    receipt=json.loads((root/'evidence/verification/acceptance.json').read_text(encoding='utf-8'))
    archive=root/'evidence/subtree-final-evidence.tar.gz'
    if digest(archive.read_bytes())!=receipt['archiveSha256']:
        raise ValueError('executed source archive hash differs')
    manifest=dict(line.split('\t') for line in
                  (root/'evidence/verification/source-manifest.tsv').read_text().splitlines())
    if {p for p in manifest if p.startswith('Path2/')}!=set(mapping['files']):
        raise ValueError('relocation must cover exactly the original source manifest')
    for p,expected in manifest.items():
        if not p.startswith('Path2/') and digest((root/mapping.get('literalPaths',{}).get(p,'lean/'+p)).read_bytes())!=expected:
            raise ValueError('literal input changed: '+p)
    with tarfile.open(archive) as bundle:
        prefix='snapshots/'+receipt['snapshotId']+'/sources/'
        needed={v['archiveMember'] for v in mapping.get('baselineSources',{}).values()}
        members={member.name:bundle.extractfile(member).read()
                 for member in bundle if member.isfile() and member.name.endswith('.lean')
                 and (member.name.startswith(prefix) or member.name in needed)}
        archived={Path(name).name:data for name,data in members.items() if name.startswith(prefix)}
        for old,entry in mapping['files'].items():
            source=archived[Path(old).name]
            if digest(source)!=manifest[old]: raise ValueError('archived source differs: '+old)
            expected=transform(source,entry,mapping)
            actual=(root/entry['newPath']).read_bytes()
            if actual!=expected or digest(actual)!=entry['sha256']:
                raise ValueError('non-permitted source change: '+entry['newPath'])
    for old,expected in (line.split('\t') for line in
            (root/'evidence/verification/baseline-manifest.tsv').read_text().splitlines()):
        if old in mapping.get('baselineSources',{}):
            entry=mapping['baselineSources'][old]
            source=members[entry['archiveMember']]
            if digest(source)!=expected: raise ValueError('shared source archive differs: '+old)
            actual=(root/entry['newPath']).read_bytes()
            if actual!=transform(source,entry,mapping) or digest(actual)!=entry['sha256']:
                raise ValueError('non-permitted shared source change: '+entry['newPath'])
            continue
        if old in mapping.get('excludedBaseline',{}):
            if mapping['excludedBaseline'][old]!=expected:
                raise ValueError('retired source checksum differs: '+old)
            continue
        if old in mapping.get('literalPaths',{}):
            if digest((root/mapping['literalPaths'][old]).read_bytes())!=expected:
                raise ValueError('literal input changed: '+old)
            continue
        new=mapping['baselinePaths'].get(old,'lean/'+old)
        if digest((root/new).read_bytes())!=expected:
            raise ValueError('baseline source differs: '+new)
    modules={mapping['modules'][Path(old).stem] for old in mapping['files']}
    entries=[*mapping['files'].values(),*mapping.get('baselineSources',{}).values()]
    if mapping.get('baselineSources'):
        actual_files={p.relative_to(root).as_posix() for p in (root/'lean/BerryEsseen').rglob('*.lean')}
        if actual_files!={e['newPath'] for e in entries}:
            raise ValueError('unclassified or missing Lean module')
        baseline_names={line.split('\t')[0] for line in
                        (root/'evidence/verification/baseline-manifest.tsv').read_text().splitlines()}
        groups=[set(mapping[k]) for k in ['baselineSources','literalPaths','excludedBaseline','baselinePaths']]
        if set.union(*groups)!=baseline_names or sum(map(len,groups))!=len(baseline_names):
            raise ValueError('shared source classification is incomplete or overlapping')
    local_imports={}
    for entry in entries:
        text=(root/entry['newPath']).read_text(encoding='utf-8')
        module='.'.join(Path(entry['newPath']).relative_to('lean').with_suffix('').parts)
        local_imports[module]=re.findall(r'(?m)^import (\S+)',text)
        for imp in re.findall(r'(?m)^import (\S+)',text):
            if imp.startswith('BerryEsseen.') and not (root/'lean'/Path(*imp.split('.'))).with_suffix('.lean').exists():
                raise ValueError('unresolved local import: '+imp)
        for literal in re.findall(r'include_str\s+"([^"]+)"',text):
            if not ((root/entry['newPath']).parent/literal).is_file():
                raise ValueError('unresolved literal input: '+literal)
    if mapping.get('baselineSources'):
        checked=set(); active=set()
        def visit(module):
            if module not in local_imports or module in checked: return
            if module in active: raise ValueError('cyclic local imports: '+module)
            active.add(module)
            for dependency in local_imports[module]: visit(dependency)
            active.remove(module); checked.add(module)
        for module in local_imports: visit(module)
        reachable=set()
        def from_main(module):
            if module not in local_imports or module in reachable: return
            reachable.add(module)
            for dependency in local_imports[module]: from_main(dependency)
        from_main('BerryEsseen.Theorems.Bound04395')
        if any(m.startswith('BerryEsseen.Verification.') for m in reachable):
            raise ValueError('main theorem imports an auxiliary verification module')
        if any(not m.startswith('BerryEsseen.Verification.') for m in local_imports.keys()-reachable):
            raise ValueError('non-verification module is outside the main proof')
    order=json.loads((root/'evidence/verification/publication-build-order.json').read_text())
    original=json.loads((root/'evidence/verification/build-order.json').read_text())
    rename=lambda s: WORD.sub(lambda m:mapping['identifiers'].get(m[0],m[0]),s)
    mapped={
        'moduleOrder':[mapping['modules'][m] for m in original['moduleOrder']],
        'imports':{mapping['modules'][m]:[mapping['modules'].get(d,d) for d in ds]
                   for m,ds in original['imports'].items()},
        'nativeTheorems':{mapping['modules'][m]:rename(v)
                          for m,v in original['nativeTheorems'].items()},
        'finalRoots':[mapping['modules'][m] for m in original['finalRoots']]}
    if order!=mapped: raise ValueError('build order differs from mapped original inventory')
    if (root/'evidence/verification/publication-axioms.txt').read_text()!=rename(
            (root/'evidence/verification/final-axioms.txt').read_text()):
        raise ValueError('expected axiom inventory differs from mapped original audit')
    if set(order['moduleOrder'])!=modules: raise ValueError('new module inventory differs')
    seen=set()
    for module in order['moduleOrder']:
        if any(d in modules and d not in seen for d in order['imports'][module]):
            raise ValueError('invalid dependency order: '+module)
        seen.add(module)
    return {'status':'PASS','scope':'exact permitted source transformation; not a fresh Lean replay',
            'modules':len(modules),'sharedModules':len(mapping.get('baselineSources',{})),
            'literalInputs':len(mapping.get('literalPaths',{})),
            'originalSnapshot':receipt['snapshotId']}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(check()))
