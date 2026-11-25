from pathlib import Path
import tempfile
import unittest

from documents import DefinitionError, discover, parse_document, relative_path


class DocumentTests(unittest.TestCase):
    def parse(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.md"
            path.write_text(text, encoding="utf-8")
            return parse_document(path)

    def test_scenario_sources_and_step_settings_stay_separate(self):
        cases = self.parse('''```toml scenario
id = "edit"
scope = "module"
name = "Example"
```
```ref
initial
```
```toml step
id = "before"
expect = "accept"
entry = "alternate.ref"
```
```ref file=alternate.ref
alternate
```
```toml step
id = "after"
expect = "reject"
```
```ref
changed
```
''')
        self.assertEqual(len(cases), 1)
        case = cases[0]
        self.assertTrue(case.scenario)
        self.assertEqual([source.text for source in case.sources], ["initial\n"])
        self.assertEqual([step.config["id"] for step in case.steps], ["before", "after"])
        self.assertEqual(case.steps[0].sources[0].path, "alternate.ref")
        self.assertEqual(case.steps[1].sources[0].text, "changed\n")
        self.assertNotIn("entry", case.steps[1].config)

    def test_invalid_documents_are_rejected_before_execution(self):
        case = '```toml case\nid="example"\nscope="module"\nexpect="accept"\n```\n'
        source = '```ref\nsource\n```\n'
        examples = [
            (case + source + case + source, "duplicate case id"),
            (case + source + source, "source file written twice"),
            (case + '```ref file=../outside.ref\nsource\n```\n', "path must stay inside"),
            (case + '```ref\nsource\n', "unclosed code fence"),
            (case.replace('expect="accept"', 'unknown=true') + source, "unknown fields"),
            ('```toml step\nid="step"\nexpect="accept"\n```\n', "step requires a scenario"),
            (case, "test has no initial sources"),
        ]
        for text, error in examples:
            with self.subTest(error=error), self.assertRaisesRegex(DefinitionError, error):
                self.parse(text)

    def test_paths_must_be_relative_and_stay_inside_the_case(self):
        for path in ["/outside.ref", "../outside.ref", "src/../../outside.ref", "src\\test.ref", ""]:
            with self.subTest(path=path), self.assertRaises(DefinitionError):
                relative_path(path, "source")
        self.assertEqual(str(relative_path("src/root.ref", "source")), "src/root.ref")

    def test_discovery_ignores_readmes_and_deduplicates_documents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "README.md").write_text("Test instructions\n", encoding="utf-8")
            path = root / "cases.md"
            path.write_text('''```toml case
id = "example"
scope = "module"
expect = "accept"
```
```ref
source
```
''', encoding="utf-8")
            cases = discover([root, path])
            self.assertEqual(len(cases), 1)
            self.assertEqual(cases[0].config["id"], "example")


if __name__ == "__main__":
    unittest.main()
