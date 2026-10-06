"""Check the closed constructor language before loading a prediction producer."""
import ast
import inspect

IMPORTS = {('dataclasses', 'dataclass'), ('fractions', 'Fraction')}
FORBIDDEN = {'open', 'input', 'eval', 'exec', 'compile', 'globals', 'locals', 'vars',
             'getattr', 'setattr', 'delattr', 'dir', 'help', 'breakpoint', '__import__',
             'memoryview', 'os', 'sys', 'io', 'socket', 'subprocess', 'pathlib', 'importlib',
             'environ', 'stdin', 'argv', 'getenv'}
BUILTINS = {'int', 'str', 'bool', 'isinstance', 'ZeroDivisionError', 'TypeError',
            'False', 'True', 'None'}


def certify_constructor(source):
    tree = ast.parse(source)
    imported = set()
    definitions = set()
    stored = set()
    loads = set()
    entry = None
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            raise ValueError('nonwhitelisted_import')
        if isinstance(node, ast.ImportFrom):
            if node.level or any((node.module, alias.name) not in IMPORTS or alias.asname
                                 for alias in node.names):
                raise ValueError('nonwhitelisted_import')
            imported.update(alias.name for alias in node.names)
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            definitions.add(node.name)
            if node.name == 'build_prediction':
                entry = node
        if isinstance(node, ast.arg):
            stored.add(node.arg)
        if isinstance(node, ast.Name):
            if node.id in FORBIDDEN:
                raise ValueError('resource_capability:' + node.id)
            if isinstance(node.ctx, ast.Store):
                stored.add(node.id)
            if isinstance(node.ctx, ast.Load):
                loads.add(node.id)
        if isinstance(node, ast.Attribute) and node.attr.startswith('_'):
            raise ValueError('reflective_attribute')
        if isinstance(node, (ast.Global, ast.Nonlocal, ast.AsyncFunctionDef, ast.Await,
                             ast.Yield, ast.YieldFrom)):
            raise ValueError('external_or_mutable_control')
        if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex, bytes)):
            raise ValueError('inexact_or_binary_literal')
    if entry is None or any((entry.args.posonlyargs, entry.args.args, entry.args.kwonlyargs,
                             entry.args.vararg, entry.args.kwarg, entry.args.defaults,
                             entry.args.kw_defaults)):
        raise ValueError('constructor_not_nullary')
    unknown = loads - imported - definitions - stored - BUILTINS
    if unknown:
        raise ValueError('unbound_resource_or_name:' + ','.join(sorted(unknown)))
    module_statements = (ast.ImportFrom, ast.FunctionDef, ast.ClassDef)
    for node in tree.body:
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
            continue
        if not isinstance(node, module_statements):
            raise ValueError('module_execution_outside_closed_definitions')
    return {'status': 'closed_constructor_language', 'empirical_arguments': 0,
            'external_resources': 0, 'floating_literals': 0,
            'allowed_imports': sorted(name for name in imported)}


def require_nullary(constructor):
    if inspect.signature(constructor).parameters:
        raise ValueError('constructor_signature_changed')
