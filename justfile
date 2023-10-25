# Install with `cargo install just`
# Usage: `just --dotenv-filename /path/to/file.env <bench|gpu-bench>`
set dotenv-load

print-lurk-env:
  echo $LURK_PERF_CONFIG
  echo $LURK_RC

bench:
  print-lurk-env
  cargo criterion --bench fibonacci

gpu-bench:
  print-lurk-env
  cargo criterion --bench fibonacci

deploy-bench:
  print-lurk-env
  cargo criterion --bench fibonacci --message-format=json > ${{ github.sha }}.json
