"""The interpreter that drives native timing is a pinned tool."""
from pathlib import Path
import platform

PIN = Path(__file__).resolve().parents[2]/'.cargo/python-version'


def require_pinned_python():
    expected, found = PIN.read_text().strip(), platform.python_version()
    if found != expected:
        raise SystemExit(f'Benchmark harness requires Python {expected} ({PIN}); found {found}')
