import copy
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

import detector_fiber_verify as consumer


def fixture():
    rebuilt={**consumer.science.scope(),'runs':[{'run':'control','domain':[1,2]}],
             'individual_hardware_constraints_checked':8,'click_polarity_branches_checked':64}
    primary={**rebuilt,'schema':'stage10-munich-detector-fiber-primary/v1','version':consumer.science.VERSION,
             'status':'generated_whole_cs_micro_hardware_constraints'}
    checked={**rebuilt,'schema':'stage10-munich-detector-fiber-independent/v1','version':consumer.science.VERSION,
             'status':'certified_whole_cs_micro_hardware_constraints'}
    return primary,checked,rebuilt


class DetectorEvidenceTests(unittest.TestCase):
    def test_same_exact_whole_cs_domain_is_consumed(self):
        self.assertEqual(consumer.validate(*fixture()),fixture()[2])

    def test_actually_unique_or_new_budget_lookalike_rejected(self):
        for key in ('actual_hardware_uniquely_identified','click_polarity_selected','new_confidence_budget_spent',
                    'all_legal_atomic_effects_pulse_realized'):
            primary,checked,rebuilt=fixture(); checked[key]=True
            with self.subTest(key=key),self.assertRaises(ValueError): consumer.validate(primary,checked,rebuilt)

    def test_lost_role_or_polynomial_coordinate_rejected(self):
        for change in ({'runs':[]},{'click_polarity_branches_checked':32},{'individual_hardware_constraints_checked':True}):
            primary,checked,rebuilt=fixture(); checked.update(change)
            with self.assertRaises(ValueError): consumer.validate(primary,checked,rebuilt)

    def test_new_execution_or_event_access_rejected(self):
        for field in ('trial_event_files_read','new_numerical_forward_executions'):
            primary,checked,rebuilt=fixture(); checked[field]=1
            with self.assertRaises(ValueError): consumer.validate(primary,checked,rebuilt)

    def test_receipt_override_and_tamper(self):
        report={'schema':consumer.SCHEMA,'evidence_valid':True,'actual_hardware_uniquely_identified':False}
        with tempfile.TemporaryDirectory() as directory,patch.object(consumer,'generate',return_value=report):
            path=Path(directory)/'receipt.json'; path.write_text(json.dumps(report))
            self.assertEqual(consumer.consume(path),report)
            path.write_text(json.dumps(dict(report,actual_hardware_uniquely_identified=True)))
            with self.assertRaises(ValueError): consumer.consume(path)

    def test_nonmatching_receipt_identity_rejected(self):
        primary,checked,rebuilt=fixture(); checked['schema']='stage10-lookalike/v1'
        with self.assertRaises(ValueError): consumer.validate(primary,checked,rebuilt)


if __name__=='__main__': unittest.main()
