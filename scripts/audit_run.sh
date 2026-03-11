#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  audit_run.sh <repo_path_to_audit> <export_path>

Arguments:
  repo_path_to_audit  Path to the git repository to audit.
  export_path         Directory where artifacts will be copied.

What this script does:
  1) Runs the same audit checks as PNT-Aristotle/audit_run.sh on the target repo.
  2) Creates repo/report.txt if missing, then appends this run's terminal output.
  3) Copies report.txt, generated diff_*.patch, and changed files (from git diff) to export_path.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

if [[ "$#" -ne 2 ]]; then
  usage
  exit 1
fi

REPO_INPUT="$1"
EXPORT_INPUT="$2"

if [[ ! -d "$REPO_INPUT" ]]; then
  echo "❌ repo path does not exist: $REPO_INPUT"
  exit 1
fi

if [[ ! -d "$EXPORT_INPUT" ]]; then
  mkdir -p "$EXPORT_INPUT"
fi

REPO_PATH=$(cd "$REPO_INPUT" && pwd)
EXPORT_PATH=$(cd "$EXPORT_INPUT" && pwd)

if ! git -C "$REPO_PATH" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "❌ not a git repository/worktree: $REPO_PATH"
  exit 1
fi

have_rg=0
if command -v rg >/dev/null 2>&1; then
  have_rg=1
fi

filter_lean_files() {
  if [[ "$have_rg" -eq 1 ]]; then
    rg -N '\.lean$' || true
  else
    grep -E '\.lean$' || true
  fi
}

report_new_forbidden_tokens_from_diff() {
  awk '
    BEGIN {
      file = ""
      line_no = 0
      found = 0
    }

    /^\+\+\+ b\// {
      file = substr($0, 7)
      next
    }

    /^@@ / {
      if (match($0, /\+[0-9]+(,[0-9]+)?/)) {
        added = substr($0, RSTART + 1, RLENGTH - 1)
        split(added, parts, ",")
        line_no = parts[1]
      }
      next
    }

    /^\+/ && $0 !~ /^\+\+\+/ {
      content = substr($0, 2)
      if (content ~ /(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)/) {
        printf "%s:%d: %s\n", file, line_no, content
        found = 1
      }
      line_no++
      next
    }

    /^-/ && $0 !~ /^---/ {
      next
    }

    {
      if ($0 !~ /^diff --git / && $0 !~ /^index / && $0 !~ /^--- /) {
        line_no++
      }
    }

    END {
      if (found == 0) {
        exit 0
      }
    }
  '
}

filter_import_changes() {
  if [[ "$have_rg" -eq 1 ]]; then
    rg '^\+import |^\-import ' || true
  else
    grep -E '^\+import |^\-import ' || true
  fi
}

copy_changed_files() {
  local src_repo="$1"
  local changed_list="$2"
  local dest_root="$3"

  mkdir -p "$dest_root"

  while IFS= read -r rel_path; do
    [[ -z "$rel_path" ]] && continue

    if [[ -f "$src_repo/$rel_path" ]]; then
      mkdir -p "$dest_root/$(dirname "$rel_path")"
      cp -p "$src_repo/$rel_path" "$dest_root/$rel_path"
      echo "copied changed file: $rel_path"
    else
      echo "skipped (missing/deleted): $rel_path"
    fi
  done <<< "$changed_list"
}

cd "$REPO_PATH"

REPORT_FILE="$REPO_PATH/report.txt"
if [[ ! -f "$REPORT_FILE" ]]; then
  touch "$REPORT_FILE"
fi

exec > >(tee -a "$REPORT_FILE") 2>&1

echo
RUN_STAMP=$(date +"%Y-%m-%d %H:%M:%S" 2>/dev/null || echo "unknown_time")
echo "========== AUDIT RUN START: $RUN_STAMP =========="
echo "repo: $REPO_PATH"
echo "export path: $EXPORT_PATH"

if [[ "$have_rg" -ne 1 ]]; then
  echo "ℹ️ rg not found; using grep fallback"
fi

echo
echo "== git status =="
git status --porcelain

CHANGED_TRACKED_FILES=$( { git diff --name-only; git diff --name-only --cached; } | sort -u || true )
CHANGED_LEAN=$(printf '%s\n' "${CHANGED_TRACKED_FILES:-}" | filter_lean_files)

echo
echo "== changed lean files =="
echo "${CHANGED_LEAN:-<none>}"

if [[ -n "${CHANGED_LEAN:-}" ]]; then
  mapfile -t CHANGED_LEAN_ARRAY <<< "$CHANGED_LEAN"

  echo
  echo "== new forbidden tokens vs HEAD in changed lean files (sorry/admit/axiom) =="
  NEW_FORBIDDEN=$(git diff --unified=0 HEAD -- "${CHANGED_LEAN_ARRAY[@]}" | report_new_forbidden_tokens_from_diff || true)
  if [[ -n "${NEW_FORBIDDEN:-}" ]]; then
    printf '%s\n' "$NEW_FORBIDDEN"
  else
    echo "✅ none found"
  fi

  echo
  echo "== import changes in changed lean files =="
  for f in "${CHANGED_LEAN_ARRAY[@]}"; do
    echo "---- $f ----"
    git diff --unified=0 -- "$f" | filter_import_changes || echo "(no import changes)"
  done
fi

echo
echo "== report.txt =="
if [[ -f "$REPORT_FILE" ]]; then
  echo "✅ found report.txt at:"
  echo "report.txt"
  echo
  echo "---- report.txt (first 120 lines) ----"
  sed -n '1,120p' "$REPORT_FILE"
else
  echo "❌ report.txt missing"
fi

echo
echo "== save git diff (tracked files only) =="
stamp=$(date +"%Y%m%d_%H%M%S" 2>/dev/null || echo "unknown_time")
out="diff_${stamp}.patch"
git diff HEAD > "$out"

if [[ -s "$out" ]]; then
  echo "✅ saved patch: $out"
  echo "== patch stat =="
  git diff --stat HEAD
else
  echo "ℹ️ no tracked changes; patch file is empty: $out"
fi

echo
echo "== copy artifacts to export path =="
repo_name=$(basename "$REPO_PATH")
artifact_dir="$EXPORT_PATH/audit_${repo_name}_${stamp}"
mkdir -p "$artifact_dir"

cp -p "$REPORT_FILE" "$artifact_dir/report.txt"
cp -p "$out" "$artifact_dir/$out"

CHANGED_FOR_COPY=$(git diff --name-only HEAD || true)
printf '%s\n' "$CHANGED_FOR_COPY" > "$artifact_dir/changed_files.list"

mkdir -p "$artifact_dir/changed_files"
copy_changed_files "$REPO_PATH" "$CHANGED_FOR_COPY" "$artifact_dir/changed_files"

echo "✅ copied artifacts to: $artifact_dir"
echo "  - report.txt"
echo "  - $out"
echo "  - changed_files.list"
echo "  - changed_files/"

echo "========== AUDIT RUN END =========="
