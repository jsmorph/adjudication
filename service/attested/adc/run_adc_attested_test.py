import argparse
import importlib.util
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).with_name("run-adc-attested.py")
SPEC = importlib.util.spec_from_file_location("run_adc_attested", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class CasePacketTest(unittest.TestCase):
    def test_stage_uses_installed_adc(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            complaint = root / "complaint.md"
            complaint.write_text("# Complaint\n", encoding="utf-8")
            args = argparse.Namespace(
                adc_bin="/opt/carve/adc",
                out_dir=root,
                complaint=str(complaint),
                dev_host="dev",
                aws_region="us-east-2",
                input_prefix="s3://bucket/input",
            )
            commands = []

            def run_command(command, **_kwargs):
                commands.append(command)
                if command[0] == args.adc_bin:
                    (root / MODULE.CASE_PACKET_OBJECT).write_bytes(b"packet")
                    (root / MODULE.CASE_PACKET_MANIFEST_OBJECT).write_bytes(b"manifest")

            with (
                mock.patch.object(MODULE, "run_command", side_effect=run_command),
                mock.patch.object(MODULE, "ssh"),
                mock.patch.object(MODULE, "remove_remote_tmp", return_value=None),
            ):
                MODULE.stage_case_packet(args, "run-1", root / "progress.log")

            self.assertEqual(
                commands[0],
                [
                    "/opt/carve/adc",
                    "case-packet",
                    "--complaint",
                    str(complaint),
                    "--packet",
                    str(root / MODULE.CASE_PACKET_OBJECT),
                    "--manifest",
                    str(root / MODULE.CASE_PACKET_MANIFEST_OBJECT),
                ],
            )
            self.assertEqual(args.case_packet, MODULE.CASE_PACKET_OBJECT)
            self.assertEqual(args.case_manifest, MODULE.CASE_PACKET_MANIFEST_OBJECT)


if __name__ == "__main__":
    unittest.main()

