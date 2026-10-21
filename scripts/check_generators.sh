#!/usr/bin/env sh
# Generator replay: every generator in generators/ that writes a committed
# fixture is rerun, and the fixture must match a fresh generation byte for
# byte, so a fixture can't drift from the generator that justifies it.
#
# Generators run in a virtual environment holding exactly
# generators/requirements.txt, installed by hash. A generator joins this list in
# the change that adds it. Their outputs are integer-exact, so they don't
# depend on the Python version.
set -eu
cd "$(dirname "$0")/.."

venv=target/generators-venv
if [ ! -x "$venv/bin/python" ]; then
  python3 -m venv "$venv"
fi
"$venv/bin/python" -m pip install --quiet --require-hashes -r generators/requirements.txt

generators="generators/interval_reference.py generators/random_streams_reference.py generators/box_muller_reference.py generators/xoshiro256_jump.py generators/exp_reference.py generators/ln_reference.py generators/exp_constants.py generators/exp_accurate_certificates.py generators/ln_constants.py generators/ln_certificates.py generators/ln1p_constants.py generators/ln1p_certificates.py generators/exp2_reference.py generators/log2_log10_reference.py generators/radix_constants.py generators/radix_certificates.py generators/expm1_reference.py generators/expm1_constants.py generators/expm1_certificates.py generators/sin_cos_reference.py generators/tan_reference.py generators/asin_reference.py generators/trig_reduction.py generators/trig_constants.py generators/trig_certificates.py generators/log_space_bounds.py generators/log_space_reference.py generators/log_norm_pdf_constants.py generators/log_norm_pdf_bounds.py generators/log_norm_pdf_reference.py generators/erfcx_constants.py generators/erfcx_reference.py generators/erfcx_certificates.py generators/erfcx_entry_tables.py generators/erfcx_quotient_bounds.py generators/erfcx_table_data.py generators/erfcx_accurate_data.py generators/erfcx_center_certificates.py generators/erfcx_table_analytic.py generators/normal_constants.py generators/normal_reference.py generators/normal_log_tail.py generators/normal_log_table.py"
for generator in $generators; do
  "$venv/bin/python" "$generator" --check
  echo "replayed: $generator"
done

# Every generator is listed above.
listed=$(echo "$generators" | wc -w | tr -d ' ')
present=$(ls generators/*.py | wc -l | tr -d ' ')
if [ "$present" -ne "$listed" ]; then
  echo "generators/ holds $present generators, but $listed are replayed" >&2
  exit 1
fi
echo "generators: OK"
