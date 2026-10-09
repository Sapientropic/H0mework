#!/usr/bin/env python3
"""Replay focused actual original literal source feed and finite clock energy budgets certification from a certified prerequisite overlay."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,tempfile,subprocess
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--prerequisite-overlay',type=Path,help='Read-only previously certified preparation prerequisite modules')
 parser.add_argument('--check-bindings-only',action='store_true',help='Only check current source bindings, without recompilation')
 args=parser.parse_args()
 receipt=json.loads((HERE/'canonical_preparation_serialized_source_certification.json').read_text())
 for file,digest in receipt['production_sha256'].items():
  assert sha(ROOT/file)==digest,('SOURCE_DRIFT',file)
 for row in receipt['source_scratch_parity']:
  assert sha(ROOT/row['source'])==row['source_sha256'],('FROZEN_SCRATCH_DRIFT',row['source'])
 if args.check_bindings_only:
  inventory=json.loads((HERE/'canonical_preparation_serialized_source_sources.json').read_text())
  for module,row in inventory.items():
   assert sha(ROOT/row['file'])==row['sha256'],('DEPENDENCY_DRIFT',module)
  print('PASS current production and prerequisite source bindings; no kernel replay requested')
  return
 if args.prerequisite_overlay is None:
  parser.error('--prerequisite-overlay is required for kernel replay')
 spec=importlib.util.spec_from_file_location('original_verify',HERE/'verify_lean.py')
 verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
 with tempfile.TemporaryDirectory(prefix='native-closed-audit-') as name:
  overlay=Path(name);verify.mirror_directory(overlay,args.prerequisite_overlay.resolve(),Path())
  for entry in overlay.iterdir():
   if entry.is_symlink():
    try:
     target=entry.resolve(strict=True)
    except FileNotFoundError:
     entry.unlink()
     continue
    entry.unlink();entry.symlink_to(target,target_is_directory=target.is_dir())
  # Dependency objects may contain nested namespace links; split them only inside this replay mirror.
  namespace=overlay/'SaturationMonoid';cached=args.prerequisite_overlay.resolve()/'SaturationMonoid'
  if namespace.is_symlink():namespace.unlink();namespace.mkdir()
  for folder,_,files in os.walk(cached,followlinks=True):
   for filename in files:
    source=Path(folder)/filename;target=namespace/source.relative_to(cached)
    if source.exists() and not target.exists():
     if target.is_symlink():target.unlink()
     target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(source.resolve(strict=True))
  def focused(source,output,env):
   args=['lake','env','sh','-c','export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"','clock-pole-replay',str(overlay),'-j1','--trust=0','-DwarningAsError=true','--root='+str(source.parent)]
   if output:
    if output.is_symlink():output.unlink()
    args+=['-o',str(output)]
   subprocess.run(args+[str(source)],cwd=ROOT/'Lean',env=env,check=True)
  env=os.environ.copy();env['ALPHA_SERIALIZED_SOURCE_OUTPUT']=str(overlay/'closure.json')
  generated=overlay/'private-generated'
  subprocess.run(['uv','run','--offline','--with','sympy==1.14.0','python',str(HERE/'canonical_preparation_serialized_source_generate.py'),'--output-directory',str(generated)],cwd=ROOT,check=True)
  for stem in ['SerializedCodec','SerializedAsset','SerializedConsumer']:
   module='CanonicalPreparation'+stem
   focused((HERE if stem=='SerializedCodec' else generated)/(module+'.lean'),overlay/(module+'.olean'),env)
  focused(HERE/'AuditCanonicalPreparationSerializedSource.lean',None,env)
  closure=json.loads((overlay/'closure.json').read_text())
  inventory=json.loads((HERE/'canonical_preparation_serialized_source_sources.json').read_text())
  project_modules={module for decl,module in closure['project']}
  assert project_modules==set(inventory), 'MODULE_COVERAGE_DRIFT'
  for module,row in inventory.items():
   relative=Path(*module.split('.')).with_suffix('.lean')
   private=receipt['private_generated_sources']
   matches=[generated/(module+'.lean')] if module in private else [base/relative for base in [ROOT/'Lean',*verify.BARE_ROOTS,HERE/'em-identification'] if (base/relative).is_file()]
   assert len(matches)==1,('NON_UNIQUE_MODULE',module)
   assert (module in private or str(matches[0].relative_to(ROOT))==row['file']) and sha(matches[0])==row['sha256'],('DEPENDENCY_DRIFT',module)
  for field in ['owned','public_roots','nodes','opaque_all_read','axioms','anchors','consumers','actual_tests']:
   assert closure[field]==receipt['kernel'][field],('CLOSURE_DRIFT',field)
 print('PASS actual fixed3934/747 decoded source symbols and original ordered Bounds consumers: complete type/value closure, original source, actual consumer, controls and unique current module hashes')

if __name__=='__main__':main()
