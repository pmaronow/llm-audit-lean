#!/usr/bin/env bash
# Resource provisioning for the disposable GitHub-hosted Ubuntu proof runner.
# Never run this on a workstation or a self-hosted runner.
set -euo pipefail

if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_OS:-}" != Linux || "${RUNNER_ENVIRONMENT:-}" != github-hosted ]]; then
  echo "Resource provisioning requires a disposable GitHub-hosted Linux runner." >&2
  exit 1
fi

swap_gib="${CI_SWAP_GIB:-24}"
if [[ ! "$swap_gib" =~ ^(1[6-9]|2[0-9]|3[0-2])$ ]]; then
  echo "CI_SWAP_GIB must be an integer from 16 through 32." >&2
  exit 1
fi
build_reserve_gib=25
swap_path="${RUNNER_TEMP:?RUNNER_TEMP is required}/llm-audit-proof.swap"

echo "Available disk before reclaiming unused runner SDKs:"
df -h "$RUNNER_TEMP"
# Keep Python, Node, all C/C++ toolchains and the rest of the tool cache. These
# individually named SDKs are not used by this Lean/Python verification job.
unused_sdks=(
  /usr/local/lib/android
  /usr/share/dotnet
  /opt/ghc
  /usr/local/.ghcup
  /usr/share/swift
  /opt/swift
  /opt/hostedtoolcache/CodeQL
  /opt/hostedtoolcache/go
  /opt/hostedtoolcache/Go
  /usr/local/go
  /usr/lib/jvm
  /opt/hostedtoolcache/Java_Temurin-Hotspot_jdk
)
for sdk in "${unused_sdks[@]}"; do
  if [[ -e "$sdk" || -L "$sdk" ]]; then
    sudo du -sh "$sdk"
    sudo rm -rf -- "$sdk"
  fi
done

available_bytes=$(df -B1 --output=avail "$RUNNER_TEMP" | tail -n 1 | tr -d ' ')
fitting_swap_gib=$((available_bytes / (1024 * 1024 * 1024) - build_reserve_gib))
if (( fitting_swap_gib < 16 )); then
  required_bytes=$(((16 + build_reserve_gib) * 1024 * 1024 * 1024))
  echo "Insufficient runner disk: ${available_bytes} bytes free; need at least ${required_bytes} bytes for 16 GiB swap plus ${build_reserve_gib} GiB toolchain/cache/build headroom." >&2
  exit 1
fi
if (( fitting_swap_gib < swap_gib )); then
  echo "Measured disk capacity selects ${fitting_swap_gib} GiB swap instead of the preferred ${swap_gib} GiB, retaining ${build_reserve_gib} GiB build headroom."
  swap_gib=$fitting_swap_gib
fi
if [[ -e "$swap_path" || -L "$swap_path" ]]; then
  echo "Refusing to replace an existing swap path: $swap_path" >&2
  exit 1
fi

# Keep existing swap enabled. This separate file remains active for all later
# steps and is discarded with the ephemeral VM; no host configuration is edited.
sudo install -m 600 /dev/null "$swap_path"
sudo fallocate -l "${swap_gib}G" "$swap_path"
sudo mkswap "$swap_path"
sudo swapon "$swap_path"
active_bytes=$(sudo swapon --show=NAME,SIZE --bytes --noheadings | awk -v path="$swap_path" '$1 == path {print $2}')
expected_bytes=$((swap_gib * 1024 * 1024 * 1024))
page_bytes=$(getconf PAGESIZE)
if [[ ! "$active_bytes" =~ ^[0-9]+$ ]] || (( active_bytes < expected_bytes - page_bytes || active_bytes > expected_bytes )); then
  echo "The requested swap file was not activated at its expected size." >&2
  exit 1
fi
echo "Proof-runner resources after provisioning:"
free -h
df -h "$RUNNER_TEMP"
