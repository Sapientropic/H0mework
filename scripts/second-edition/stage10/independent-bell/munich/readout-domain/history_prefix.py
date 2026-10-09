"""Predictable full-history laws consumed by the original four e-processes.

A law is sealed before the next raw outcome is consumed.  Count forecasters,
mixture weights and threshold remain those of the original static consumers.
The source producer owns normalization, history measurability and the shared
hardware model; a numerical probability box does not certify those facts.
"""
from fractions import Fraction as Q
import hashlib
import json

import interval_prefix as primary
import history_interval_prefix_independent as independent


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def _model(value):
    if type(value) is not dict or not value:
        raise ValueError('one fixed source model record required')
    return _canonical(value)


class _HistoryPrefixes:
    def __init__(self, model_record):
        self.model = _model(model_record)
        self.pending = None
        self.count = 0
        self.past = hashlib.sha256()
        self.predictions = hashlib.sha256()
        self.last_prediction = None
        self.checker = None

    def predict(self, table, *, model_record, parent_history):
        if self.pending is not None:
            raise ValueError('consume the sealed law before generating its successor')
        if _model(model_record) != self.model:
            raise ValueError('hardware source changed within the same history')
        if type(parent_history) is not dict or not parent_history:
            raise ValueError('source-generated parent history record required')
        row = self.validate(table)
        records = [{'context': list(key), 'q': [list(map(str, pair)) for pair in row[key]]}
                   for key in primary.CONTEXTS]
        seal = _canonical({'ordinal': self.count+1, 'prior_trial_bits_sha256': self.past.hexdigest(),
                           'source_model': json.loads(self.model), 'parent_history': parent_history,
                           'probability_enclosures': records})
        self.pending = seal
        return hashlib.sha256(seal.encode()).hexdigest()

    def observe(self, trial):
        if self.pending is None:
            raise ValueError('predict from the past before consuming the next outcome')
        self._verify_consumed_history()
        if type(getattr(trial, 'row', None)) is not int or trial.row != self.count+1:
            raise ValueError('next original ordered trial required')
        bits = tuple(getattr(trial, field, None) for field in ('h', 'a', 'b', 'x', 'y'))
        primary._bits(bits, 5)
        sealed = json.loads(self.pending)
        table = {tuple(item['context']): tuple(tuple(map(Q, pair)) for pair in item['q'])
                 for item in sealed['probability_enclosures']}
        result = self._consume(table, trial)
        self.predictions.update(self.pending.encode()+b'\n')
        self.past.update(bytes(bits))
        self.last_prediction, self.pending = sealed, None
        self.count += 1
        return result

    def _verify_consumed_history(self):
        if self.checker is None:
            if self.count != 0:
                raise ValueError('unsealed underlying engine history')
            return
        value = self.checker.result()
        if value['trials'] != self.count or value['trial_bit_sequence_sha256'] != self.past.hexdigest():
            raise ValueError('unsealed underlying engine history')

    def result(self):
        if self.pending is not None or self.checker is None or not self.count:
            raise ValueError('complete nonempty consumed history required')
        self._verify_consumed_history()
        value = self.checker.result()
        value.pop('probability_table_sha256', None)
        return {**value, 'schema': self.schema,
                'predictable_law_sequence_sha256': self.predictions.hexdigest(),
                'source_model_sha256': hashlib.sha256(self.model.encode()).hexdigest(),
                'last_prediction': self.last_prediction,
                'dynamic_denominators_consumed': True,
                'law_sealed_before_outcome_consumption': True,
                'count_forecasters_and_original_mixture_preserved': True,
                'history_measurability_source_proof_required': True,
                'quantum_source_binding_verified': False,
                'actual_hardware_uniquely_identified': False,
                'controller_advance': False}


class HistoryPrefixChecker(_HistoryPrefixes):
    schema = 'stage10-history-interval-prefix/v1'
    validate = staticmethod(primary.probability_table)

    def __init__(self, model_record, precision=80):
        super().__init__(model_record)
        self.precision = precision

    def _consume(self, table, trial):
        if self.checker is None:
            self.checker = primary.IntervalPrefixChecker(table, self.precision)
        self.checker.table = table
        return self.checker.step(trial.h, trial.a, trial.b, trial.x, trial.y)


class HistoryPrefixes(_HistoryPrefixes):
    schema = 'stage10-history-interval-prefix-independent/v1'

    def __init__(self, model_record, bits=240, *, allow_zero_lower=False):
        if type(allow_zero_lower) is not bool:
            raise ValueError('allow_zero_lower must be boolean')
        super().__init__(model_record)
        self.bits = bits
        self.allow_zero_lower = allow_zero_lower

    def validate(self, table):
        return independent.probability_table(table, allow_zero_lower=self.allow_zero_lower)

    def _consume(self, table, trial):
        if self.checker is None:
            self.checker = independent.IntervalPrefixes(
                table, self.bits, allow_zero_lower=self.allow_zero_lower)
        self.checker.q = table
        return self.checker.step(trial)
