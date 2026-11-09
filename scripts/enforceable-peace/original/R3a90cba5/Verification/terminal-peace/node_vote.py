"""Call one installed terminal-peace verifier over the guarded ComputeNode transport."""

from __future__ import annotations

import argparse
import json
from pathlib import Path, PurePosixPath
import shlex
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "ComputeNode/mac"))
from pcnode import Config, Node


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("node-config", "resource-state"):
        parser.add_argument("--" + name, type=Path, required=True)
    for name in ("member", "release", "python", "lean"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    release, lean = PurePosixPath(args.release), PurePosixPath(args.lean)
    if not release.is_absolute() or not lean.is_absolute() or args.timeout <= 0:
        parser.error("release and Lean paths must be absolute, with a positive timeout")
    node = Node(Config.load(args.node_config), args.resource_state)
    command = [args.python, "-B", str(release / "repo/Lean/scripts/terminal_peace_anchor.py"),
               "vote", "--policy", str(release / "policy.json"), "--member", args.member,
               "--key", str(release / "anchor.key"), "--fence", str(release / "fence.sqlite"),
               "--library", str(release / "lib"), "--timeout", str(args.timeout)]
    argument = json.dumps(json.load(sys.stdin), separators=(",", ":"), allow_nan=False)
    shell = f"export PATH={shlex.quote(str(lean.parent))}:\"$PATH\"\n"
    shell += shlex.join(command) + " <<'PEACE_INPUT'\n" + argument + "\nPEACE_INPUT\n"
    sys.stdout.buffer.write(node.wsl(shell, args.timeout + 15, allow_probe=False))


if __name__ == "__main__":
    main()
