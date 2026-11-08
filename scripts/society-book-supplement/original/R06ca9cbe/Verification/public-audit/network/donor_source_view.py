"""A cumulative donor view over the original paid, committed native prefix.

The old base worker's memory is not reconstructed. Only the authenticated past
is memoized; each new donor input still goes through the original native reader.
"""
import json
from pathlib import Path

from crypto import digest
import donor_arrival_live as donor
import donor_paid_prefix
import energy
from productive_owner_request import history
from source_semantics import Engine as OriginalEngine, Incomplete
import source_readiness

SCHEMA = 'original-paid-donor-view/v1'


class Engine(OriginalEngine):
    def __init__(self, config):
        self.authority = config
        self.view = config['donor_history']
        if (set(self.view) != {'schema', 'producer', 'prefix', 'evidence', 'evidence_sha256', 'proofs', 'proofs_sha256'} or
                self.view['schema'] != SCHEMA or self.view['producer'] not in config['ha']['trust']['members']):
            raise ValueError('DONOR_HISTORY_PROFILE')
        for kind in ('evidence', 'proofs'):
            if source_readiness.sha(Path(self.view[kind])) != self.view[kind+'_sha256']:
                raise ValueError('DONOR_HISTORY_ARTIFACT')
        self.evidence = json.loads(Path(self.view['evidence']).read_text())
        self.proofs = json.loads(Path(self.view['proofs']).read_text())
        self.boundary = None
        super().__init__(config['semantic'])

    def close(self):
        super().close()
        self.boundary = None

    def sync(self, rows, deadline=None):
        try:
            if self.boundary is None:
                self.boundary = donor_paid_prefix.consume(self.authority, rows, self.evidence, self.proofs)
                if self.boundary['prefix'] != self.view['prefix']:
                    raise Incomplete('DONOR_HISTORY_PREFIX')
                self.count = self.boundary['prefix']['seq']; self.head = self.boundary['prefix']['head']
            if self.count > len(rows) or rows[self.count-1][2] != self.head:
                raise Incomplete('DONOR_HISTORY_MOVED')
            history(self.authority, rows)
            context = self.config['governance_context']
            for seq, previous, head, raw in rows[self.count:]:
                if seq != self.count+1 or previous != self.head:
                    raise Incomplete('PREFIX_CHAIN')
                event = json.loads(raw)['body']
                donor.guard(context, rows[:self.count], event)
                if event['type'] == donor.ACTION:
                    # No paid result exists for this new cumulative input.
                    donor.expected(context, rows[:self.count], event, native=True)
                elif event['type'] != 'rotation':
                    raise Incomplete('DONOR_CURRENT_SOURCE_REQUIRED')
                self.count = seq; self.head = head
        except (Incomplete, ValueError, KeyError, TypeError) as problem:
            self.close()
            if isinstance(problem, Incomplete):
                raise
            raise Incomplete('DONOR_HISTORY_DATA') from problem

    def check(self, rows, message):
        if message['body']['type'] not in {donor.ACTION, 'rotation'}:
            raise Incomplete('DONOR_CURRENT_SOURCE_REQUIRED')
        return super().check(rows, message)

    def status(self):
        reader = energy._readers.get(digest(self.config['governance_context']['donor']))
        backend = reader.status()['backend'] if reader is not None else None
        return dict(prefix=dict(seq=self.count, head=self.head), descriptor=self.descriptor, backend=backend,
                    source_view=dict(kind=SCHEMA, boundary=self.view['prefix'],
                                     donor_descriptor=self.config['governance_context']['donor']['descriptor']))
