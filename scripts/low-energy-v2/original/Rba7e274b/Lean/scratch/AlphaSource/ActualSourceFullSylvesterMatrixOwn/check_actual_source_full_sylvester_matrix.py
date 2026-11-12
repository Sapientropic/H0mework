"""Check frozen source identity, production first hits and bounded complete audit evidence."""
from pathlib import Path
import hashlib,json,re,sys
ROOT=Path('runtime/Documents/Homework')
OWN=Path(__file__).resolve().parent
CONFIG=Path('runtime/storage/primary/Homework-runtime/audit-tmp/iqa-source-full-sylvester-matrix-certification/config.json')
EXPECTED='307116a8a45b8c5abeaba81074e7bd057f3f49f9e77624fed0e52ca122984f7e'
PROD=ROOT/'Verification/physics/low-energy-phenomenology/alpha-source/em-identification'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def verify(source_dir):
    assert sha(OWN/'candidate.json')==EXPECTED
    c=read(OWN/'candidate.json');cfg=read(CONFIG)
    co=OWN/(cfg['prefix']+'-cert-overlay');po=OWN/(cfg['prefix']+'-prod-cert-overlay')
    for node in c['nodes']:
        assert sha(Path(source_dir)/(node['module']+'.lean'))==node['source_sha256']
        assert sha(node['source'])==node['source_sha256']
        assert sha(node['object'])==node['object_sha256']
        assert sha(node['types'])==node['types_sha256']
        types=read(node['types'])
        assert len(types['declarations'])==node['all_owned']
    assert sha(c['parent_candidate'])==c['parent_candidate_sha256']
    for p,h in c['evidence'].items():assert sha(p)==h
    for r in read(po/'strict-compile.json'):
        assert r['exit']==0
        for flag in ['--trust=0','-j1','-DwarningAsError=true','-DElab.async=false']:assert flag in r['command']
    assert len(read(po/'strict-compile.json'))==3
    first=read(co/'production-first-hits.json');paths=(co/'lean-path.txt').read_text().strip().split(':')
    for module,hit in first.items():
        actual=next(Path(p)/(module+'.olean') for p in paths if (Path(p)/(module+'.olean')).exists())
        assert actual.resolve()==Path(hit['path']).resolve() and actual.parent.resolve()==po.resolve()
        assert sha(actual)==hit['sha256']
    a=read(co/'audit-compile.json');assert a['exit']==0
    j=read(co/'closure.json');assert len(j['public'])==22 and len(j['owned'])==55 and len(j['tests'])==8 and j['axioms']==3
    forbidden=r'alphaEMIntegerDenominator|alphaEMFromIntegerConstraint|gutWeakMixingInformationRatio|alphaStrongDisplayed|CODATA|experimentalAlpha|alphaTarget'
    assert not [x for x in j['project'] if re.search(forbidden,x[0],re.I)]
    expected=[ 'sourceInverse','jointResolvent','noetherReaderContact','rawReaderContact','dressedEulerObserver','sourceDressedUnit','sourceProfile','actualJoint_annihilated','jointPolynomial','compressionPolynomial']
    assert all(any(x.endswith('.'+n) for x in j['anchors']) for n in expected)
    assert 'unknown=0 unsafe=0 partial=0' in a['stdout']
    sources=[(OWN/(n+'.lean')).read_text() for n in cfg['sources']]
    assert not any(re.search(r'\b(sorry|admit|axiom|unsafe|partial)\b',s) for s in sources)
    assert not any(re.search(r'^import\s+(?:scratch\.|Lean\.scratch\.)',s,re.M) for s in sources)
    budgets={n:dict(re.findall(r'^set_option (maxHeartbeats|maxRecDepth|synthInstance.maxHeartbeats) (\d+)',s,re.M)) for n,s in zip(cfg['sources'],sources)}
    assert budgets[cfg['sources'][0]]=={'maxHeartbeats':'1000000','maxRecDepth':'8192','synthInstance.maxHeartbeats':'1000000'}
    assert budgets[cfg['sources'][1]]=={'maxHeartbeats':'1000000','maxRecDepth':'8192','synthInstance.maxHeartbeats':'200000'}
    return {'public':len(j['public']),'owned':len(j['owned']),'typed_consumers':len(j['tests']),'closure_nodes':j['nodes'],'opaque_all_read':j['opaque_read'],'axioms':j['axioms'],'source_local_budgets':budgets,'audit_budget':{'maxHeartbeats':12000000,'maxRecDepth':32768}}
def main():
    source_dir=Path(sys.argv[1]) if len(sys.argv)>1 else OWN
    facts=verify(source_dir)
    print(json.dumps({'status':'PASS_SOURCE_IDENTITY_AND_PRODUCTION_FIRST_COMPLETE_CLOSURE','candidate_sha256':EXPECTED,'source_dir':str(source_dir),'controller_advanced':False,'facts':facts},ensure_ascii=False))
if __name__=='__main__':main()
