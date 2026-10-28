#!/usr/bin/env bash
# Keep independent certificate compilations within a small runner's memory.
set -euo pipefail
lorentz_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$lorentz_root/lean"
lake build Lorentz.Counterexample Lorentz.CertificateNorms Lorentz.Plateau.SeedCertificate
for lorentz_family in Odd Even; do
  lorentz_prefix="Lorentz.Plateau.Certificates.$lorentz_family"
  lake build "${lorentz_prefix}Data"
  lake build "${lorentz_prefix}Recurrences"
  lake build "${lorentz_prefix}Slacks0" "${lorentz_prefix}Slacks1" "${lorentz_prefix}Slacks2"
  if [ "$lorentz_family" = Even ]; then
    lake build "${lorentz_prefix}Slacks3"
  fi
  lake build "${lorentz_prefix}Bounds" "${lorentz_prefix}CubicGrid"
  lake build "${lorentz_prefix}Contacts" "${lorentz_prefix}Asymmetry"
  lake build "${lorentz_prefix}Values"
  for lorentz_seed in 0 1 2; do
    lake build "${lorentz_prefix}Seed${lorentz_seed}"
  done
  if [ "$lorentz_family" = Even ]; then
    lake build "${lorentz_prefix}Seed3"
  fi
done
lake build
