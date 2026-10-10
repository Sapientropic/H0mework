from pathlib import Path
import ast,difflib,hashlib,json

ROOT=Path(__file__).resolve().parents[3]
BASE=Path(__file__).resolve().parent

def sha(raw):return hashlib.sha256(raw).hexdigest()

helper=r'''
def _private_owner_tuple_literals(text: str, masked: str):
    """Recognize the observed paired provider binding and its singleton lookup."""
    namespace = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
    flow = re.compile(
        r"\blet\s+member\s*:=\s*id\.getId\s+"
        r"let\s*\(\s*owner\s*,\s*namespaceName\s*\)\s*←(?P<arms>.*?)"
        r"\blet\s+wanted\s*:=\s*namespaceName\s*\+\+\s*member\s+"
        r"let\s+candidates\s*:=\s*\(\s*←\s*getEnv\s*\)\.constants\.toList\.filter\s+"
        r"fun\s*\(\s*name\s*,\s*_\s*\)\s*=>\s*name\.toString\.startsWith\s+owner\s*&&\s*"
        r"privateToUserName\s+name\s*==\s*wanted\s+"
        r"match\s+candidates\s+with\s*\|\s*\[\s*\(\s*name\s*,\s*_\s*\)\s*\]\s*=>\s*"
        r'(?:logInfo\s+m!"[ \t]*;\s*)?return\s+mkConst\s+name\s*'
        r'\|\s*_\s*=>\s*throwError\s*"[ \t]*', re.DOTALL)
    arms = re.compile(
        r"\s*if\s+member\s*==\s*`(?P<member1>" + namespace + r")\s+then\s+pure\s*\(\s*"
        r'(?P<owner1>"[ \t]*)\s*,\s*`(?P<namespace1>' + namespace + r")\s*\)\s*"
        r"else\s+if\s+member\s*==\s*`(?P<member2>" + namespace + r")\s+then\s+pure\s*\(\s*"
        r'(?P<owner2>"[ \t]*)\s*,\s*`(?P<namespace2>' + namespace + r")\s*\)\s*"
        r'else\s+throwError\s*"[ \t]*\s*')
    found = []
    for binding in flow.finditer(masked):
        branch = arms.fullmatch(binding['arms'])
        if (branch is None or branch['namespace1'] != branch['namespace2']
                or branch['member1'] == branch['member2']):
            continue
        for group in ('owner1', 'owner2'):
            begin = binding.start('arms') + branch.start(group)
            original_literal = re.match(r'"(?:\\.|[^"\\])*"', text[begin:])
            if original_literal is None:
                continue
            literal = original_literal[0]
            end = begin + len(literal)
            # This binding has exact module owners, each ending before its index.
            if re.fullmatch(r'"_private\.' + namespace + r'\."', literal):
                found.append((begin, end, literal))
    return found

'''
source=ROOT/'tools/source_view.py';raw=source.read_text()
marker='def rewrite_private_owner_strings(text: str, rewrites, *, reverse: bool = False) -> str:\n'
assert raw.count(marker)==1
candidate=raw.replace(marker,helper+marker)
needle='''    edits = []
    for owner, spans in matches.items():
'''
assert candidate.count(needle)==1
candidate=candidate.replace(needle,'''    for begin, end, literal in _private_owner_tuple_literals(text, masked):
        if literal in literals:
            owner, suffix = literals[literal]
            matches[owner].append((begin, end, suffix))
    edits = []
    for owner, spans in matches.items():
''')
ast.parse(candidate)
(BASE/'source_view-candidate.py').write_text(candidate)
(BASE/'source_view.diff').write_text(''.join(difflib.unified_diff(raw.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile='a/tools/source_view.py',tofile='b/tools/source_view.py')))
write=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
write(BASE/'tool-candidate-identity.json',{'source':'tools/source_view.py','base_sha256':sha(raw.encode()),'candidate_sha256':sha(candidate.encode()),'public_applied':False,'schema_unchanged':True})
print(json.dumps({'candidate':str((BASE/'source_view-candidate.py').resolve()),'sha256':sha(candidate.encode()),'public_applied':False}))
