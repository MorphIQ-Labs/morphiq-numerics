import copy
import io
from pathlib import Path
import tarfile
import tempfile
import tomllib
import unittest

from scripts.check_packages import bootstrap_manifest, check_archive, check_publishable, CRATES


class PackageTests(unittest.TestCase):
    def test_bootstrap_changes_only_the_publication_guard(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Cargo.toml'
            path.write_text('[package]\nname = "example"\npublish = false # intentional guard\n'
                            '[dependencies.arch]\nversion = "0.1.0"\noptional = true\n')
            before = tomllib.loads(path.read_text())
            bootstrap_manifest(path)
            before['package']['publish'] = True
            self.assertEqual(tomllib.loads(path.read_text()), before)
            bootstrap_manifest(path)
            self.assertEqual(tomllib.loads(path.read_text()), before)

    def test_unexpected_registry_selection_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Cargo.toml'
            for value in ('[]', '["crates-io"]', '["private"]'):
                path.write_text(f'[package]\nname = "example"\npublish = {value}\n')
                before = path.read_bytes()
                with self.subTest(value=value), self.assertRaises(ValueError):
                    bootstrap_manifest(path)
                self.assertEqual(path.read_bytes(), before)

    def test_only_the_two_release_crates_may_publish(self):
        good = dict(packages=[dict(name=n, publish=None) for n in CRATES] +
                             [dict(name='oracle', publish=[])])
        check_publishable(good)
        mutations = [good['packages'][:-2],
                     good['packages'] + [dict(name='extra', publish=None)],
                     good['packages'] + [dict(name='extra', publish=['crates-io'])]]
        for packages in mutations:
            with self.subTest(packages=packages), self.assertRaises(ValueError):
                check_publishable(dict(packages=packages))

    def test_package_integrity_rejects_missing_or_changed_distribution_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'LICENSE-MIT').write_text('MIT license fixture')
            (root / 'LICENSE-APACHE').write_text('Apache license fixture')
            notice = root / 'crates/morphiq-numerics/THIRD_PARTY_NOTICES.md'
            notice.parent.mkdir(parents=True)
            notice.write_text('required notice fixture')
            files = {
                'README.md': b'# Example\n[Contract](https://example.com/contract)\n',
                'LICENSE-MIT': (root / 'LICENSE-MIT').read_bytes(),
                'LICENSE-APACHE': (root / 'LICENSE-APACHE').read_bytes(),
                'THIRD_PARTY_NOTICES.md': notice.read_bytes(),
                'Cargo.toml': b'''[package]
name = "morphiq-numerics"
version = "0.1.0"
license = "MIT OR Apache-2.0"
readme = "README.md"
[package.metadata.docs.rs]
all-features = true
[dependencies.morphiq-numerics-arch]
version = "0.1.0"
optional = true
''',
            }
            archive = root / 'test.crate'
            def check(members):
                with tarfile.open(archive, 'w:gz') as handle:
                    for name, data in members.items():
                        info = tarfile.TarInfo('morphiq-numerics-0.1.0/' + name)
                        info.size = len(data)
                        handle.addfile(info, io.BytesIO(data))
                return check_archive(archive, 'morphiq-numerics', '0.1.0', root)
            self.assertEqual(check(files)['version'], '0.1.0')
            for name, contents in [('README.md', b'[Contract](../../docs/contract.md)'),
                                   ('LICENSE-MIT', b'wrong license'),
                                   ('THIRD_PARTY_NOTICES.md', b'missing attribution'),
                                   ('Cargo.toml', files['Cargo.toml'] + b'path = "../arch"\n'),
                                   ('Cargo.toml', files['Cargo.toml'] + b'[build-dependencies.tool]\nversion = "1"\n')]:
                broken = copy.deepcopy(files)
                broken[name] = contents
                with self.subTest(name=name, contents=contents), self.assertRaises(ValueError):
                    check(broken)
            del files['LICENSE-APACHE']
            with self.assertRaises(KeyError):
                check(files)


if __name__ == '__main__':
    unittest.main()
