#!/usr/bin/env python3
"""Replay erfcx fast and Q256 tables, including rustfmt's canonical layout.

Sollya 8.0 generates erfcx/tables.out; the separate certificates replay it.
Q256 constants are recomputed at 600 and 1000 bits and must agree exactly.
"""
import pathlib
import subprocess
import sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
GEN = ROOT / 'generators/erfcx'
OUT = ROOT / 'crates/morphiq-numerics/src/erfcx'

def rustfmt(text):
    return subprocess.run(['rustfmt','--edition','2024'],input=text,text=True,
                          check=True,capture_output=True).stdout

def main():
    fast = subprocess.run([sys.executable, str(GEN/'fast_tables.py'), str(GEN/'tables.out')],
                          capture_output=True,text=True,check=True).stdout
    code = (GEN/'accurate_tables.py').read_text()
    def accurate(precision):
        return subprocess.run([sys.executable,'-c', code.replace('mp.mp.prec = 600',f'mp.mp.prec = {precision}')],
                              capture_output=True,text=True,check=True).stdout
    acc = accurate(600)
    assert acc == accurate(1000), 'Q256 table precision instability'
    for name, text in [('tables.rs',fast),('accurate_tables.rs',acc)]:
        text = rustfmt(text)
        path = OUT/name
        if '--check' in sys.argv:
            assert path.read_text() == text, f'{name} differs'
        else: path.write_text(text)

if __name__ == '__main__': main()
