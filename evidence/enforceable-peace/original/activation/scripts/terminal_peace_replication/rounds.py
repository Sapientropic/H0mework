"""Role-specific evidence for an unresolved handoff at one original parent."""

from dataclasses import dataclass, field
from itertools import combinations


OWNER = "terminal-peace-ordered-input/v1"
DECISION = "terminal-peace-outgoing-decision/v1"
READY = "terminal-peace-incoming-replay/v1"
STAGE = "terminal-peace-retained-handoff/v1"
NO_DECISION = "terminal-peace-no-outgoing-decision/v1"
NO_READY = "terminal-peace-no-incoming-replay/v1"
ORDER = "terminal-peace-resolve-original-handoff/v1"


@dataclass
class Evidence:
    votes: dict = field(default_factory=dict)
    ready: dict = field(default_factory=dict)
    no_decision: dict = field(default_factory=dict)
    no_ready: dict = field(default_factory=dict)
    order: dict | None = None


def final_authorization(intent):
    history = intent.get("rounds", [])
    return history[-1]["order"] if history else intent["owner"]


def request_id(intent):
    body = final_authorization(intent)["body"]
    return body["id"] if intent.get("rounds") else body["request"]["id"]


def possible_completion(outgoing, incoming, no_decision, no_ready):
    """Give an exact completion compatible with the seals and each roster's fault budget."""
    old, new = set(outgoing), set(incoming)
    for group in combinations(sorted(old), 3):
        forced = (set(group) & no_decision) | (new & no_ready)
        if len(forced & old) <= 1 and len(forced & new) <= 1:
            return {"outgoing": list(group), "incoming": sorted(new), "faults_required": sorted(forced)}
    return None
