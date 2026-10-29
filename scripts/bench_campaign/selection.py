"""Select declared cells before observation/freeze; never alter the timing protocol."""
import hashlib
import json


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def reference(cell, platform):
    return cell['reference'] if platform == 'x86-linux' else cell['pair'][1]


def family(cell, platform):
    name = reference(cell, platform)
    if name.startswith('sleef_'):
        return 'sleef'
    return {'core_math_exp': 'core-math', 'libcerf_erfcx': 'libcerf',
            'scipy_ndtr': 'scipy', 'strong-control': 'control',
            'composed_cdf_passes': 'composition'}[name]


def validate_full(cells, platform):
    ids = [cell['id'] for cell in cells]
    if not ids or len(set(ids)) != len(ids):
        raise ValueError('Full matrix must have unique, nonempty cell IDs')
    required = 'required_parity' if platform == 'x86-linux' else 'parity_required'
    if not any(c[required] for c in cells):
        raise ValueError('Full matrix must contain required comparisons')
    if not {'core-math', 'sleef', 'libcerf', 'scipy'}.issubset({family(c, platform) for c in cells}):
        raise ValueError('Full matrix must include CORE-MATH, SLEEF, libcerf and SciPy comparisons')


def select(cells, platform, suite='full', primitives=(), backends=(), cell_ids=()):
    validate_full(cells, platform)
    filters = {'primitives': sorted(set(primitives)), 'backends': sorted(set(backends)), 'cell_ids': sorted(set(cell_ids))}
    if suite not in ('full', 'smoke', 'subset'):
        raise ValueError(f'Unknown suite: {suite}')
    if suite != 'subset' and any(filters.values()):
        raise ValueError('Filters require --suite subset; full and smoke have fixed coverage')
    if suite == 'subset' and not any(filters.values()):
        raise ValueError('Subset requires a primitive, backend or exact cell ID')
    if backends and platform != 'x86-linux':
        raise ValueError('ARM cells have no separate backend selector; use primitive or cell IDs')
    for name, requested, available in [
        ('primitive', primitives, {c['primitive'] for c in cells}),
        ('backend', backends, {c.get('backend') for c in cells}),
        ('cell ID', cell_ids, {c['id'] for c in cells}),
    ]:
        if set(requested) - available:
            raise ValueError(f'Unknown {name}: {sorted(set(requested) - available)}')
    if suite == 'smoke':
        # One ordinary 52-element comparison per canonical family, plus an x86
        # unchanged control. SLEEF and libcerf exercise public slice interfaces.
        chosen = []
        for owner, primitive, vector in [('core-math', 'exp', False), ('sleef', 'exp', True),
                                         ('libcerf', 'erfcx', True), ('scipy', 'cdf', False)] + (
                                         [('control', 'exp', False)] if platform == 'x86-linux' else []):
            matches = []
            for c in cells:
                if platform == 'x86-linux':
                    ordinary = c['population'] == 'ordinary' and c['backend'] == 'auto' and not c.get('cache_slots')
                    interface = c['kind'] == ('vector' if vector else 'scalar')
                else:
                    ordinary = c['bank'] == primitive + '-ordinary' and c['mode'] == 'throughput'
                    interface = c['pair'][0].endswith('_slice') == vector
                if ordinary and interface and c['length'] == 52 and c['primitive'] == primitive and family(c, platform) == owner:
                    matches.append(c)
            if len(matches) != 1:
                raise ValueError(f'Smoke preset expected one {owner}/{primitive} cell, found {len(matches)}')
            chosen.append(matches[0]['id'])
        selected = [c for c in cells if c['id'] in chosen]
    else:
        selected = [c for c in cells if (not primitives or c['primitive'] in primitives)
                    and (not backends or c['backend'] in backends)
                    and (not cell_ids or c['id'] in cell_ids)]
    if not selected:
        raise ValueError('Selection is empty; check intersecting filters')
    ids = [c['id'] for c in selected]
    required = 'required_parity' if platform == 'x86-linux' else 'parity_required'
    return {'schema': 1, 'platform': platform, 'suite': suite, 'filters': filters,
            'full_matrix_sha256': fingerprint(cells), 'full_cell_count': len(cells),
            'selected_ids': ids, 'excluded_ids': [c['id'] for c in cells if c['id'] not in ids],
            'selected_cell_count': len(ids), 'selected_required_count': sum(c[required] for c in selected),
            'timed_work_target_seconds': len(ids) * 10 * 2 * 2 * .6,
            'timed_work_note': 'Target timed work only, excluding warmups, calibration, preparation and observations; not an ETA.'}


def selected_cells(cells, plan):
    expected = select(cells, plan['platform'], plan['suite'], **plan['filters'])
    if plan != expected:
        raise ValueError('Selection receipt differs from its full matrix and declared filters')
    return [c for c in cells if c['id'] in plan['selected_ids']]
