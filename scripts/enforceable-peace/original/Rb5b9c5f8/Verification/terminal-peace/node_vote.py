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
    parser.add_argument("--replicated", action="store_true", help="consume the signed replica protocol")
    parser.add_argument("--fence-dir", help="independent key and fence directory for a new identity")
    parser.add_argument("--native-release", help="existing policy and Lean library installation")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    release, lean = PurePosixPath(args.release), PurePosixPath(args.lean)
    fence = PurePosixPath(args.fence_dir) if args.fence_dir else release
    native = PurePosixPath(args.native_release) if args.native_release else release
    if any(not path.is_absolute() for path in (release, lean, fence, native)) or args.timeout <= 0:
        parser.error("release and Lean paths must be absolute, with a positive timeout")
    node = Node(Config.load(args.node_config), args.resource_state)
    scripts = release / "repo/Lean/scripts"
    common = ["--policy", str(native / "policy.json"), "--library", str(native / "lib"),
              "--timeout", str(args.timeout)]
    identity = ["--member", args.member, "--key", str(fence / "anchor.key"), "--fence", str(fence / "fence.sqlite")]
    if args.replicated:
        command = [args.python, "-B", str(scripts / "terminal_peace_online.py"), *common, "node", *identity]
    else:
        command = [args.python, "-B", str(scripts / "terminal_peace_anchor.py"), "vote", *common, *identity]
    argument = json.dumps(json.load(sys.stdin), separators=(",", ":"), allow_nan=False)
    shell = f"export PATH={shlex.quote(str(lean.parent))}:\"$PATH\"\n"
    shell += shlex.join(command) + " <<'PEACE_INPUT'\n" + argument + "\nPEACE_INPUT\n"
    if args.replicated:
        # Keep the verifier's typed refusal and its process exit distinct from transport failure.
        result = node._run_remote(node.remote_argv("bash", "-s"), input=shell.encode(),
                                  capture_output=True, timeout=args.timeout + 15, allow_probe=False)
        sys.stdout.buffer.write(result.stdout)
        sys.stderr.buffer.write(result.stderr)
        raise SystemExit(result.returncode)
    sys.stdout.buffer.write(node.wsl(shell, args.timeout + 15, allow_probe=False))


if __name__ == "__main__":
    main()
