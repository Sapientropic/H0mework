#!/usr/bin/env python3
"""Regenerate private fixed serialized proofs from the original gzip asset."""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent
BATCH='canonical_preparation_serialized_source_'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output-directory',type=Path,required=True);args=parser.parse_args()
 out=args.output_directory.resolve();out.mkdir(parents=True,exist_ok=True)
 receipt=json.loads((HERE/(BATCH+'certification.json')).read_text())
 for file,digest in receipt['production_sha256'].items():assert sha(ROOT/file)==digest,('PRODUCTION_DRIFT',file)
 expected=receipt['private_generation']['generated_sources_exactbytes']
 for name in ['read_asset.py','write_lean_asset.py','pole_witnesses.py','write_witness_terms.py','consumer-template.lean.in']:
  source=HERE/(BATCH+name);assert sha(source)==receipt['private_generation']['generators'][name]
  (out/name).write_bytes(source.read_bytes())
 # Root anchoring changes no parser, table, coefficient or proof generation.
 for name in ['read_asset.py','write_lean_asset.py','pole_witnesses.py','write_witness_terms.py']:
  source=(out/name).read_text();source=source.replace('ROOT=Path(__file__).resolve().parents[4]','ROOT=Path('+repr(str(ROOT))+')')
  import sys
  previous=sys.argv;sys.argv=[str(out/name)]+(['--all'] if name=='write_witness_terms.py' else [])
  try:exec(compile(source,str(out/name),'exec'),{'__file__':str(out/name),'__name__':'__main__'})
  finally:sys.argv=previous
 for name,digest in expected.items():assert sha(out/name)==digest,('REGENERATION_DRIFT',name)
 mapping={'Codec':'CanonicalPreparationSerializedCodec','SourceAsset':'CanonicalPreparationSerializedAsset'}
 for old,new in [('SourceAsset','CanonicalPreparationSerializedAsset'),('LiteralConsumer','CanonicalPreparationSerializedConsumer')]:
  text=(out/(old+'.lean')).read_text();text=re.sub(r'^import (\w+)$',lambda m:'import '+mapping.get(m[1],m[1]),text,flags=re.M)
  text=re.sub(r'^#print axioms .*\n','',text,flags=re.M);text='\n'.join(x.rstrip() for x in text.splitlines()).rstrip('\n')+'\n'
  destination=out/(new+'.lean');destination.write_text(text)
  expectedRow=receipt['private_generated_sources'][new];assert sha(destination)==expectedRow['sha256'],('NORMALIZED_REGEN_DRIFT',new)
 print('PASS exact private fixed-source proofs regenerated; no Lean gate replayed')
if __name__=='__main__':main()
