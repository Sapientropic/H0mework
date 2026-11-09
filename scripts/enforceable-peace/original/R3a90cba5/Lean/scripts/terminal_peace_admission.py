"""Pin terminal-peace transport authorization to the original journal head."""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from terminal_peace_worker import HEAD, IDENTIFIER, SOURCE, _digest, _unique_keys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "Verification/public-audit/network"))
from crypto import digest, verify


OWNER = "terminal-peace-owner-input/v1"
VOTE = "terminal-peace-native-vote/v1"
GITHASH = re.compile(r"[0-9a-f]{40}\Z")
INVALID_PROOF = (InvalidSignature, ValueError, TypeError, KeyError, AttributeError)


def _key(value):
    if not isinstance(value, str) or not HEAD.fullmatch(value):
        raise ValueError("invalid terminal-peace public key")
    return Ed25519PublicKey.from_public_bytes(bytes.fromhex(value))


class Admission:
    def __init__(self, path: Path, version: str, compiler: str):
        policy = json.loads(path.read_text(), object_pairs_hook=_unique_keys)
        if (not isinstance(policy, dict)
                or set(policy) != {"source", "version", "compiler", "checkpoint", "owner", "members"}
                or policy["source"] != SOURCE or policy["version"] != version
                or not GITHASH.fullmatch(compiler) or policy["compiler"] != compiler):
            raise ValueError("terminal-peace admission has a different source or compiler")
        cut = policy["checkpoint"]
        if (not isinstance(cut, dict) or set(cut) != {"cursor", "head"}
                or type(cut["cursor"]) is not int or cut["cursor"] < 0
                or not isinstance(cut["head"], str) or not HEAD.fullmatch(cut["head"])):
            raise ValueError("invalid terminal-peace checkpoint")
        keys = policy["members"]
        if (not isinstance(keys, dict) or len(keys) != 4
                or any(not IDENTIFIER.fullmatch(name) or not isinstance(key, str) for name, key in keys.items())
                or len(set(keys.values())) != 4
                or policy["owner"] in keys.values()):
            raise ValueError("terminal peace requires four distinct verifier keys and an independent owner")
        self.identity = _digest(policy)
        self.checkpoint = cut
        self.owner = _key(policy["owner"])
        self.members = {name: _key(key) for name, key in keys.items()}

    def bind(self, current):
        if {"cursor": current.cursor, "head": current.head} != self.checkpoint:
            raise ValueError("terminal-peace admission requires the exact committed checkpoint")

    def authorization(self, request):
        return {"policy": self.identity, "request": request}

    def authorize(self, request, owner):
        if verify(self.owner, OWNER, owner) != self.authorization(request):
            raise ValueError("terminal-peace authorization does not match this input")

    def accepts_owner(self, request, proof):
        try:
            self.authorize(request, proof["owner"])
        except INVALID_PROOF:
            return False
        return True

    def point(self, current, owner, next_current):
        return {"policy": self.identity, "parent": current.reply(),
                "authorization": digest(owner), "next": next_current.reply()}

    def required(self, current):
        return 4 if current.cursor == self.checkpoint["cursor"] else 3

    def verify_step(self, current, request, next_current, proof):
        if set(proof) != {"owner", "record", "votes"} or proof["record"] != next_current.record:
            raise ValueError("terminal-peace certificate does not match the native result")
        owner, votes = proof["owner"], proof["votes"]
        self.authorize(request, owner)
        if (current.cursor < self.checkpoint["cursor"] or not isinstance(votes, dict)
                or not self.required(current) <= len(votes) <= 4 or not votes.keys() <= self.members.keys()):
            raise ValueError("terminal-peace quorum unavailable")
        point = self.point(current, owner, next_current)
        for name, receipt in votes.items():
            if verify(self.members[name], VOTE, receipt) != point:
                raise ValueError("terminal-peace vote has a different original parent or result")


def compiler_revision(root: Path, timeout: float) -> str:
    return subprocess.check_output(["lean", "--githash"], cwd=root, text=True, timeout=timeout).strip()
