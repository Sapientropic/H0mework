import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import pulse_realization_verify as consumer


class PulseEvidenceTests(unittest.TestCase):
    def test_scope_never_selects_actual_or_shared_detector_identity(self):
        scope=consumer.science.scope()
        self.assertIs(scope['per_role_detector_model_required'],True)
        self.assertIs(scope['actual_hardware_uniquely_identified'],False)
        self.assertIs(scope['shared_detector_identity_certified'],False)

    def test_invalid_result_or_input_shape_rejected(self):
        with self.assertRaises(ValueError): consumer.validate({'schema':'lookalike'},{},{})

    def test_location_override_and_source_scope_tamper(self):
        report={'schema':consumer.SCHEMA,'evidence_valid':True,**consumer.science.scope()}
        with tempfile.TemporaryDirectory() as folder,patch.object(consumer,'generate',return_value=report):
            path=Path(folder)/'receipt.json'; path.write_text(json.dumps(report))
            self.assertEqual(consumer.consume(path),report)
            path.write_text(json.dumps(dict(report,actual_hardware_uniquely_identified=True)))
            with self.assertRaises(ValueError): consumer.consume(path)

    def test_same_response_does_not_pay_distinct_physical_fibre(self):
        rows=[{'id':'a','response':{'p_bright':['4/5','4/5'],'p_dark':['1/10','1/10']}}]
        # A source witness with an independently known legal effect is enough
        # for these mathematical controls; no pulse solver or events are used.
        primitive={'alice':[{'mu':'0','u':'1/2','z':'0'}]*2,'bob':[{'mu':'0','u':'0','z':'1/2'}]*2}
        witness={'runs':[{'run':name,'primitive':primitive} for name in consumer.parent.RUNS]}
        result=consumer.science.realizations(rows,witness,'primary')
        self.assertTrue(result['physical_pulse_image_joint_domain_nonempty_certified'])
        self.assertFalse(result['same_law_distinct_physical_responses_certified'])
        self.assertEqual(consumer.science.realizations(rows,witness,'independent'),result)

    def test_distinct_qualified_response_restores_the_identical_source(self):
        rows=[{'id':'a','response':{'p_bright':['4/5','4/5'],'p_dark':['1/10','1/10']}},
              {'id':'b','response':{'p_bright':['9/10','9/10'],'p_dark':['1/10','1/10']}}]
        primitive={'alice':[{'mu':'0','u':'1/2','z':'0'}]*2,'bob':[{'mu':'0','u':'0','z':'1/2'}]*2}
        witness={'runs':[{'run':name,'primitive':primitive} for name in consumer.parent.RUNS]}
        result=consumer.science.realizations(rows,witness,'primary')
        self.assertTrue(result['same_law_distinct_physical_responses_certified'])
        self.assertEqual(consumer.science.realizations(rows,witness,'independent'),result)

    def test_target_probability_table_not_admitted_as_primitive(self):
        rows=[{'id':'a','response':{'p_bright':['4/5','4/5'],'p_dark':['1/10','1/10']}}]
        point={'mu':'0','u':'1/2','z':'0','target_q':['1/4']}
        primitive={'alice':[point]*2,'bob':[point]*2}
        witness={'runs':[{'run':name,'primitive':primitive} for name in consumer.parent.RUNS]}
        with self.assertRaises(ValueError): consumer.science.realizations(rows,witness,'primary')


if __name__=='__main__': unittest.main()
