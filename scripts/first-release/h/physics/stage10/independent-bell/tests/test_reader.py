import io
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from reader import parse_rows


HEADER = "synthetic schema header\r\ninput/output labels\r\n\r\n"


class ReaderTests(unittest.TestCase):
    def test_raw_columns_order_and_terminal_newline(self):
        rows = list(parse_rows(io.StringIO(HEADER + "0, 1, 1, -1\r\n1,-1,0,1")))
        self.assertEqual([(r['a'],r['b'],r['x'],r['y']) for r in rows],
                         [(0,1,1,-1),(1,0,-1,1)])
        self.assertEqual([r['source_line'] for r in rows], [4,5])
        self.assertEqual([r['herald'] for r in rows], [1,1])

    def test_all_outcomes_and_settings_are_retained(self):
        expected = [(a,b,x,y) for a in (0,1) for b in (0,1)
                    for x in (-1,1) for y in (-1,1)]
        text = HEADER + '\n'.join(f'{a},{x},{b},{y}' for a,b,x,y in expected)
        rows = list(parse_rows(io.StringIO(text)))
        self.assertEqual([(r['a'],r['b'],r['x'],r['y']) for r in rows],expected)

    def test_packed_fpga_codes_are_not_reinterpreted(self):
        with self.assertRaises(ValueError):
            list(parse_rows(io.StringIO(HEADER + "2,1,0,1")))

    def test_bad_record_aborts_instead_of_selecting(self):
        for record in ("0,0,1,1", "0,1,1,1,0", "", "0,1,1,nan", "0.5,1,0,1"):
            with self.subTest(record=record), self.assertRaises(ValueError):
                list(parse_rows(io.StringIO(HEADER + record + '\n')))

    def test_header_is_required(self):
        with self.assertRaises(ValueError):
            list(parse_rows(io.StringIO('one line\n')))


if __name__ == "__main__":
    unittest.main()
