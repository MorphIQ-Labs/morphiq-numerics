#!/usr/bin/env python3
"""Replay the generated erfcx table and tail evaluation certificates.

These certificates establish evaluation error conditional on their stated
EFT and exact-product hypotheses; they do not prove the full erfcx entry.
"""
import pathlib
import subprocess
import sys
import tempfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT/'formal/erfcx'
with tempfile.TemporaryDirectory() as tmp:
    subprocess.run([sys.executable,str(ROOT/'generators/erfcx/table_certificates.py'),
                    str(ROOT/'generators/erfcx/tables.out'),tmp],check=True)
    subprocess.run([sys.executable,str(ROOT/'generators/erfcx/tail_certificates.py'),tmp],check=True)
    generated = sorted(pathlib.Path(tmp).glob('*.g'))
    assert len(generated) == 208
    for src in generated:
        dst = OUT/src.name
        if '--check' in sys.argv:
            assert dst.read_text() == src.read_text(), f'{dst} differs'
        else:
            dst.parent.mkdir(parents=True,exist_ok=True)
            dst.write_text(src.read_text())
