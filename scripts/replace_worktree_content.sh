#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  replace_worktree_content.sh SOURCE_DIR TARGET_WORKTREE [--dry-run] [--allow-dirty]

Description:
  Replaces TARGET_WORKTREE contents with SOURCE_DIR contents while preserving
  TARGET_WORKTREE's git worktree metadata.

Options:
  --dry-run      Show what would change without modifying files.
  --allow-dirty  Allow running even if TARGET_WORKTREE has uncommitted changes.

Examples:
  replace_worktree_content.sh \
    /ryu/xinjie/aristotle/sorry_exp3/PNT-Aristotle-exp3_aristotle \
    /ryu/xinjie/PNT-Aristotle-exp3

  replace_worktree_content.sh ./new-version ./PNT-Aristotle-exp3 --dry-run
EOF
}

if [[ $# -lt 2 ]]; then
  usage
  exit 1
fi

SOURCE_DIR="$1"
TARGET_DIR="$2"
shift 2

DRY_RUN=0
ALLOW_DIRTY=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run)
      DRY_RUN=1
      ;;
    --allow-dirty)
      ALLOW_DIRTY=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      usage
      exit 1
      ;;
  esac
  shift
done

if [[ ! -d "$SOURCE_DIR" ]]; then
  echo "Source directory does not exist: $SOURCE_DIR" >&2
  exit 1
fi

if [[ ! -d "$TARGET_DIR" ]]; then
  echo "Target directory does not exist: $TARGET_DIR" >&2
  exit 1
fi

if [[ "$SOURCE_DIR" == "$TARGET_DIR" ]]; then
  echo "Source and target must be different directories." >&2
  exit 1
fi

SOURCE_DIR="$(cd "$SOURCE_DIR" && pwd -P)"
TARGET_DIR="$(cd "$TARGET_DIR" && pwd -P)"

if ! git -C "$TARGET_DIR" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "Target is not a git working tree: $TARGET_DIR" >&2
  exit 1
fi

TARGET_COMMON_GIT_DIR="$(git -C "$TARGET_DIR" rev-parse --git-common-dir)"

if [[ ! -e "$TARGET_DIR/.git" ]]; then
  echo "Target does not contain .git linkage metadata, refusing to continue." >&2
  exit 1
fi

if [[ $ALLOW_DIRTY -eq 0 ]] && [[ -n "$(git -C "$TARGET_DIR" status --porcelain)" ]]; then
  echo "Target has uncommitted changes. Commit/stash first, or rerun with --allow-dirty." >&2
  exit 1
fi

echo "Source: $SOURCE_DIR"
echo "Target: $TARGET_DIR"
echo "Target common git dir: $TARGET_COMMON_GIT_DIR"

RSYNC_ARGS=(
  -a
  --delete
  --exclude=.git
  --exclude=.git/
)

if [[ $DRY_RUN -eq 1 ]]; then
  RSYNC_ARGS+=(--dry-run --itemize-changes)
  echo "Running in dry-run mode (no files will be modified)."
fi

rsync "${RSYNC_ARGS[@]}" "$SOURCE_DIR/" "$TARGET_DIR/"

if [[ $DRY_RUN -eq 0 ]]; then
  echo
  echo "Sync complete. Worktree metadata was preserved."
  echo "Review changes with:"
  echo "  git -C '$TARGET_DIR' status"
  echo "  git -C '$TARGET_DIR' diff --stat"
fi
