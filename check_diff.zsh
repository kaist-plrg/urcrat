#!/bin/zsh

# Usage: ./compare_rust_projects.zsh /path/to/project1 /path/to/project2

set -e

if [[ $# -ne 2 ]]; then
  echo "Usage: $0 <dir1> <dir2>"
  exit 1
fi

DIR1=$1
DIR2=$2

if [[ ! -d "$DIR1" || ! -d "$DIR2" ]]; then
  echo "Error: Both arguments must be valid directories"
  exit 1
fi

# Ensure difftastic is installed
if ! command -v difft &> /dev/null; then
  echo "[*] difftastic (difft) not found. Installing with cargo..."
  cargo install difftastic
fi

echo "[*] Forcing formatting of all .rs files..."
find "$DIR1" -name '*.rs' -exec rustfmt --config-path rustfmt.toml {} +
find "$DIR2" -name '*.rs' -exec rustfmt --config-path rustfmt.toml {} +

echo ""
echo "[*] Comparing .rs files..."

TMP1=$(mktemp)
TMP2=$(mktemp)

# Compare each .rs file in DIR1
find "$DIR1" -type f -name '*.rs' | while read -r file1; do
  rel_path="${file1#$DIR1/}"
  file2="$DIR2/$rel_path"

  if [[ -f "$file2" ]]; then
    tr -s '[:space:]' ' ' < "$file1" > "$TMP1"
    tr -s '[:space:]' ' ' < "$file2" > "$TMP2"

    if ! cmp -s "$TMP1" "$TMP2"; then
      echo ""
      echo "=== Difference in $rel_path ==="
      difft "$file1" "$file2" || true
      echo "================================="
    fi
  else
    echo ">>> Missing in $DIR2: $rel_path"
  fi
done

# Check for extra .rs files in DIR2
find "$DIR2" -type f -name '*.rs' | while read -r file2; do
  rel_path="${file2#$DIR2/}"
  file1="$DIR1/$rel_path"
  if [[ ! -f "$file1" ]]; then
    echo ">>> Missing in $DIR1: $rel_path"
  fi
done

echo ""
echo "[*] Comparison complete."
