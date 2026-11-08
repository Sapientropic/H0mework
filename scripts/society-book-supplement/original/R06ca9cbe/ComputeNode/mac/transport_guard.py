"""Per-node circuit breaker shared by processes on this control machine.

Only an SSH disconnect or transport timeout trips the breaker. Healthy operations
hold no long-lived lock; after a failure, one leased probe may reopen the circuit.
Epochs merge simultaneous failures and prevent an old result from undoing a hold.
"""
from __future__ import annotations

import argparse
import contextlib
import dataclasses
import fcntl
import hashlib
import json
import subprocess
import time
import uuid
from pathlib import Path

PROBE_TIMEOUT = 15
BACKOFF_SECONDS = 60
FAILURE_LIMIT = 3


class TransportFailure(ConnectionError):
    """SSH disconnected before the remote command could report its own outcome."""


class TransportBlocked(RuntimeError):
    def __init__(self, state: dict):
        self.state = state
        super().__init__(f"node transport {state['phase']}: {state.get('last_error', '')}")


def is_transport_failure(error: BaseException) -> bool:
    return (isinstance(error, (ConnectionError, subprocess.TimeoutExpired))
            or isinstance(error, subprocess.CalledProcessError) and error.returncode == 255)


@dataclasses.dataclass(frozen=True)
class Ticket:
    epoch: int
    probe: str = ""
    previous: str = "healthy"


class TransportGuard:
    def __init__(self, root: Path, identity: dict, *, clock=None):
        self.identity = identity
        self.clock = clock or time.time
        tag = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()[:16]
        self.path = root / f"{tag}.json"
        self.lock_path = root / f"{tag}.lock"

    @contextlib.contextmanager
    def _locked(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.lock_path.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if self.path.exists():
                state = json.loads(self.path.read_text())
                if state["identity"] != self.identity:
                    raise ValueError("transport control identity mismatch")
            else:
                state = {"identity": self.identity, "phase": "healthy", "epoch": 0, "failures": 0}
            yield state

    def _save(self, state: dict) -> None:
        state["updated_at"] = self.clock()
        temporary = self.path.with_suffix(f".{uuid.uuid4().hex}.tmp")
        temporary.write_text(json.dumps(state, indent=2) + "\n")
        temporary.replace(self.path)

    def snapshot(self) -> dict:
        with self._locked() as state:
            return dict(state)

    def acquire(self, *, allow_probe: bool = True, force_probe: bool = False) -> Ticket:
        with self._locked() as state:
            now, phase = self.clock(), state["phase"]
            if phase == "healthy" and not force_probe:
                return Ticket(state["epoch"])
            if phase == "probing" and now < state["probe_until"]:
                raise TransportBlocked(dict(state))
            if phase == "probing":
                phase = state["probe_previous"]
                state.update(phase=phase, epoch=state["epoch"] + 1)
                self._clear_probe(state)
                self._save(state)
            if not force_probe and (not allow_probe or phase == "hold"
                                    or now < state.get("retry_at", 0)):
                raise TransportBlocked(dict(state))
            # A crashed probe loses its lease. Its late result cannot own the next one.
            previous = phase
            state.update(phase="probing", epoch=state["epoch"] + 1,
                         probe=uuid.uuid4().hex, probe_until=now + PROBE_TIMEOUT + 15,
                         probe_previous=previous)
            self._save(state)
            return Ticket(state["epoch"], state["probe"], previous)

    @staticmethod
    def _owns(state: dict, ticket: Ticket) -> bool:
        return (state["epoch"] == ticket.epoch
                and (state["phase"] == "probing" and state.get("probe") == ticket.probe
                     if ticket.probe else state["phase"] == "healthy"))

    @staticmethod
    def _clear_probe(state: dict) -> None:
        for key in ("probe", "probe_until", "probe_previous"):
            state.pop(key, None)

    def success(self, ticket: Ticket, evidence: dict | None = None) -> bool:
        with self._locked() as state:
            if not self._owns(state, ticket):
                return False
            if ticket.probe:
                state.update(phase="healthy", epoch=state["epoch"] + 1, failures=0,
                             recovered_at=self.clock(), last_probe=evidence or {})
                for key in ("retry_at", "last_error", "hold_reason", "last_probe_error"):
                    state.pop(key, None)
                self._clear_probe(state)
                self._save(state)
            return True

    def failure(self, ticket: Ticket, error: BaseException) -> None:
        if not is_transport_failure(error):
            self.abandon_probe(ticket, error)
            return
        with self._locked() as state:
            if not self._owns(state, ticket):
                return
            failures = state["failures"] + 1
            phase = "hold" if failures >= FAILURE_LIMIT or ticket.previous == "hold" else "backoff"
            state.update(phase=phase, epoch=state["epoch"] + 1, failures=failures,
                         last_error=repr(error)[:500], failed_at=self.clock(),
                         retry_at=self.clock() + BACKOFF_SECONDS * 2 ** min(failures - 1, 4))
            self._clear_probe(state)
            self._save(state)

    def abandon_probe(self, ticket: Ticket, error: BaseException) -> None:
        """Bad script/output is not a transport failure and cannot add to its count."""
        if not ticket.probe:
            return
        with self._locked() as state:
            if not self._owns(state, ticket):
                return
            state.update(phase=ticket.previous, epoch=state["epoch"] + 1,
                         last_probe_error=repr(error)[:500], retry_at=self.clock() + BACKOFF_SECONDS)
            self._clear_probe(state)
            self._save(state)

    def hold(self, reason: str) -> dict:
        with self._locked() as state:
            state.update(phase="hold", epoch=state["epoch"] + 1, hold_reason=reason,
                         last_error=reason)
            self._clear_probe(state)
            self._save(state)
            return dict(state)


def main() -> None:
    from pcnode import Config, Node

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("action", choices=("status", "hold", "recover"))
    parser.add_argument("--reason", default="manual hold")
    parser.add_argument("--min-free-gib", type=float, default=1.0)
    args = parser.parse_args()
    if not 0 <= args.min_free_gib < float("inf"):
        parser.error("--min-free-gib must be finite and nonnegative")
    config = Config.load(args.config)
    node = Node(config, Path(config.transport_control_dir).parent / "health-probe")
    if args.action == "hold":
        node.guard.hold(args.reason)
    elif args.action == "recover":
        try:
            node.recover_transport(min_free_bytes=int(args.min_free_gib * (1 << 30)))
        except Exception as error:
            print(json.dumps({"error": str(error), "transport": node.guard.snapshot()}, indent=2))
            raise SystemExit(1)
    print(json.dumps(node.guard.snapshot(), indent=2))


if __name__ == "__main__":
    main()
