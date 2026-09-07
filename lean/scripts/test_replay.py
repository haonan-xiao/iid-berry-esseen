"""Runner unit tests; the fake compiler is not mathematical evidence."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import replay as runner
import source_layout


class ReplayTests(unittest.TestCase):
    def test_namespaced_scheduler_and_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); lean=root/'lean'; evidence=root/'evidence/verification'
            evidence.mkdir(parents=True)
            modules=['BerryEsseen.Moments.Test','BerryEsseen.Verification.FinalAxiomAudit']
            for module in modules:
                source=(lean/Path(*module.split('.'))).with_suffix('.lean')
                source.parent.mkdir(parents=True,exist_ok=True)
                source.write_text('-- test fixture, not Lean proof\n')
            (root/'lake-manifest.json').write_text('{"packages":[]}')
            (evidence/'source-layout.json').write_text('{}')
            axioms=['Classical.choice','Quot.sound','propext']
            (evidence/'publication-axioms.txt').write_text('\n'.join(axioms)+'\n')
            order={'moduleOrder':modules,'imports':{modules[0]:[],modules[1]:[modules[0]]},'nativeTheorems':{}}
            calls=[]; output=root/'output'
            def fake_command(args,cwd,**kwargs):
                self.assertEqual(cwd,root)
                if args[-1]=='--version': return 'Lean (version 4.29.1, test-only)'
                if args[-1]=='--print-prefix': return str(root/'toolchain')
                return json.dumps({'LEAN_PATH':str(root/'deps'),'PATH':'test-only'})
            def fake_run(args,**kwargs):
                if '-o' in args:
                    self.assertEqual(args[1:3],['-j1','--tstack=32768'])
                    self.assertEqual(args[args.index('-R')+1],str(lean))
                    self.assertEqual(kwargs['cwd'],root)
                    module='.'.join(Path(args[-1]).relative_to(lean).with_suffix('').parts)
                    if module==modules[1]:
                        self.assertTrue((output/'records'/(modules[0]+'.json')).exists())
                        kwargs['stdout'].write('depends on axioms: ['+', '.join(axioms)+']\n')
                    else: kwargs['stdout'].write('fake compiler\n')
                    Path(args[args.index('-o')+1]).write_bytes(('fixture:'+module).encode())
                    calls.append(module)
                return type('Result',(),{'returncode':0})()
            with patch.object(runner,'source_check',return_value=({'snapshotId':'test-only'},order)), \
                 patch.object(runner,'command',fake_command),patch.object(runner.subprocess,'run',fake_run):
                self.assertEqual(runner.replay(lean,output,2)['checkedModules'],2)
                runner.replay(lean,output,2)
                self.assertEqual(calls,modules)
                (output/'lib/BerryEsseen/Moments/Test.olean').write_bytes(b'tampered')
                with self.assertRaisesRegex(ValueError,'invalid checkpoint'):
                    runner.replay(lean,output,2)


class TransformationTests(unittest.TestCase):
    def test_relocated_literal_input(self):
        entry={'oldPath':'Path2/Test.lean',
               'newPath':'lean/BerryEsseen/Certificates/Data/Test.lean', 'title':'Test'}
        mapping={'modules':{},'identifiers':{},
                 'literalPaths':{'BerryEsseen/Input.lean':'lean/certificate-data/finite/N01.lean.txt'}}
        actual=source_layout.transform(b'include_str "../BerryEsseen/Input.lean"',entry,mapping)
        self.assertEqual(actual,b'include_str "../../../certificate-data/finite/N01.lean.txt"')

    def test_shared_module_import_without_declaration_changes(self):
        entry={'oldPath':'BerryEsseen/Example.lean',
               'newPath':'lean/BerryEsseen/Probability/Example.lean','title':'Test'}
        mapping={'modules':{'BerryEsseen.Interface':'BerryEsseen.Probability.Definitions'},'identifiers':{}}
        original=b'import BerryEsseen.Interface\nnamespace BerryEsseen\ndef bound : Nat := 4395\nend BerryEsseen\n'
        actual=source_layout.transform(original,entry,mapping)
        self.assertEqual(actual,original.replace(b'import BerryEsseen.Interface',b'import BerryEsseen.Probability.Definitions'))

    def setUp(self):
        self.entry={'oldPath':'Path2/Test.lean','newPath':'lean/BerryEsseen/Moments/Test.lean','title':'Test'}
        self.mapping={'modules':{'OldModule':'BerryEsseen.Moments.Other'},'identifiers':{'path2Foo':'foo'}}

    def convert(self,text):
        return source_layout.transform(text.encode(),self.entry,self.mapping).decode()

    def test_import_and_identifier(self):
        self.assertEqual(self.convert('import OldModule\ndef path2Foo := 42\n'),
                         'import BerryEsseen.Moments.Other\ndef foo := 42\n')

    def test_strings_and_character_literals(self):
        text='def path2Foo := "path2Foo RZLL"\ndef c := \'"\'\n#check path2Foo\n'
        self.assertEqual(self.convert(text),'def foo := "path2Foo RZLL"\ndef c := \'"\'\n#check foo\n')

    def test_escaped_quote_character(self):
        text="def c := '\\\"'\n#check path2Foo\n"
        self.assertTrue(self.convert(text).endswith('#check foo\n'))

    def test_nested_comments(self):
        self.assertEqual(self.convert('/- a /- b -/ path2Foo -/\n#check path2Foo'),
                         '/- a /- b -/ foo -/\n#check foo')

    def test_proof_expression_unchanged(self):
        self.assertEqual(self.convert('theorem path2Foo : 2 + 3 = 5 := by norm_num'),
                         'theorem foo : 2 + 3 = 5 := by norm_num')

    def test_unterminated_comment(self):
        with self.assertRaises(ValueError): self.convert('/- unfinished')


if __name__=='__main__': unittest.main()
