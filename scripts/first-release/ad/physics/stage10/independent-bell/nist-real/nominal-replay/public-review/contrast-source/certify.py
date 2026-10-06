"""Fresh independent ct0001 certification; acceptance never rebuilds Lean or data."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / '.git').exists())
PROJECT = ROOT / 'Lean'
NOMINAL = HERE.parents[1]
FIBER = NOMINAL / 'observable-closure/full-statistical-fiber'
sys.path.insert(0, str(FIBER))
from phase_certify import ALLOWED, FORBIDDEN, digest, frozen, rel
from covariance_source_certify import header_imports, independent_registry_change

CONTRACT_FREEZE = '7ac7026c90c22153e4bbe69b0748fb491b4a40a7'
CHAIN = [NOMINAL/'gaussian-window/GaussianSource.lean',
         NOMINAL/'observable-closure/ObservableClosure.lean',
         NOMINAL/'observable-closure/ClosureConsumer.lean',
         HERE/'ContrastSource.lean', HERE/'ContrastConsumer.lean', HERE/'ContrastCertification.lean']
EXPECTED = dict(zip([p.name for p in CHAIN[:-1]], [
    '1dee783a0976a497139e64d4ef7278b203d56a0b119c84eea942bbb7846a10af',
    '10bd6d3abc3fa23d5a6672e3b7ecd2249624b29396d41e84ea2ebb39b2770c2f',
    'aeab3e4a50fc884e3dbdd6bb6a6d91711879a3b045fcbf54b9e315dd1580f9d2',
    '1ed871e69da8a15fa5f2852a465879df9dfe424997a3a6653b3a921567bfa0bb',
    '32f71db6aae1f7cde9f582bf4f06c5dd6a7c1cbd82871c21c3f1858f2e5c29a2']))
CLAIMS = {
    'source_generated_probability_law_all_N': True,
    'source_negative_CH_implies_original_binomial_threshold': True,
    'source_negative_CH_fixed_bet_expected_value_bound': True,
    'original_N5_readback_exact': True,
    'source_outcomes_positive_normalized_and_no_signaling': True,
    'contrast_and_correct_loss_event_identity_generated': True,
    'all_sixteen_local_assignments_certified_separately': True,
    'negative_CH_Gaussian_source_preserved': True,
    'statistical_rejection_is_logical_impossibility': False,
    'actual_source_epoch_or_hardware_identified': False,
    'new_stochastic_process_or_Ville_kernel': False,
    'new_infinite_Born_or_Gaussian_Gamma_bridge': False,
    'controller_advance': False,
}
SCOPES = {
    'source': 'original Snapshot physical fields; every natural N, legal local OR backgrounds and real angles',
    'generic_null': 'positive normalized no-signaling constant law with CH<=0; negative-CH quantum laws included',
    'settings': 'epsilon in [0,1); normalized four setting probabilities in [(1-epsilon)^2/4,(1+epsilon)^2/4]',
    'binomial': 'positive relevant mass gives weightedWin/(weightedWin+weightedLoss)<=original S4 threshold',
    'one_step': 'fixed p between threshold and 1; all other outcome multipliers equal 1; expected value in [0,1]',
    'local': 'sixteen Bool deterministic assignments; not the only admitted CH-null source class',
    'CI': 'no counts, alpha, confidence intervals, model fitting or empirical identities enter the proof',
    'controller': 'bounded subordinate source law; original root/visit10/whole-ledger/tick16-to17 unchanged',
}
PUBLIC = {'P23.ObservableClosure.ContrastSource.'+name for name in (
    'sourceLaw','source_per_pulse_bounds','window_positive','window_normalized',
    'window_marginal_A','window_marginal_B','window_five_readback','source_CH_readback',
    'contrast_CH_readback','loss_outcome_readback','sixteen_assignments_CH_nonpositive',
    'Consumer.threshold_closed_form','Consumer.weighted_ratio_bound','Consumer.relevant_success_bound',
    'Consumer.nonpositive_CH_one_step','Consumer.source_nonpositive_CH_one_step','Consumer.local_assignment_one_step')}


def owned_sources():
    return [*CHAIN,HERE/'criterion.md',HERE/'sources.json',HERE/'certify.py',HERE/'tests.py',HERE/'lsp-status.json',
            FIBER/'phase_certify.py',FIBER/'covariance_source_certify.py',
            PROJECT/'lean-toolchain',PROJECT/'lake-manifest.json']


def require(ok, message):
    if not ok:
        raise ValueError(message)


def source_closure(source_root, inventory=False):
    search = [HERE,NOMINAL/'observable-closure',NOMINAL/'gaussian-window',PROJECT,
              *sorted((PROJECT/'.lake/packages').glob('*')),Path(source_root),Path(source_root)/'lake']
    pending = [m for p in CHAIN for m in header_imports(p)]
    seen = {}
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        suffix = Path(*name.split('.')).with_suffix('.lean')
        path = next((p/suffix for p in search if (p/suffix).is_file()),None)
        require(path is not None,'unresolved CT semantic import: '+name)
        seen[name] = digest(path)
        pending.extend(header_imports(path))
    result = {'modules':len(seen),'source_binding_sha256':hashlib.sha256(json.dumps(seen,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
              'local_modules':sorted(n for n in seen if n in {p.stem for p in CHAIN}),
              'toolchain_source_root':source_root,'unresolved':[]}
    if inventory:
        result.update({'inventory':seen,'search_roots':[str(p.resolve()) for p in search]})
    return result


def parse_audit(log):
    match = re.search(r'CT_CERTIFIED declarations=(\d+) source_declarations=(\d+)',log)
    controls = re.search(r'CT_INDEPENDENT_CERTIFIED declarations=(\d+)',log)
    require(match is not None and controls is not None,'incomplete CT audit sentinel')
    out = {'candidate_declarations':int(match[1]),'source_declarations':int(match[2]),'independent_declarations':int(controls[1])}
    graphs = {}
    for role in ['primitive','background','source','contrast','consumer','success','local','bundle']:
        size = re.search(r'CT_GRAPH '+role+r'\|(\d+)',log)
        nodes = sorted(set(re.findall(r'CT_DEP '+role+r'\|([^\s]+)',log)))
        require(size is not None and int(size[1])==len(nodes),'incomplete CT dependency graph: '+role)
        graphs[role] = {'nodes':len(nodes),'sha256':hashlib.sha256('\n'.join(nodes).encode()).hexdigest(),
                        'project_declarations':[n for n in nodes if n.startswith('P23.')]}
    out['dependency_closure'] = graphs
    rows = re.findall(r'CT_(?:INDEPENDENT_)?AXIOMS ([^|\s]+)\|(?:#)?\[(.*?)\]',log,re.DOTALL)
    require(len(rows)==out['source_declarations']+out['independent_declarations'],'incomplete CT axiom inventory')
    axioms = {}
    for name, raw in rows:
        values = sorted(v.strip() for v in raw.split(',') if v.strip())
        require(set(values)<=ALLOWED,'unauthorized CT axiom: '+name)
        axioms[name] = values
    out['axiom_declarations_checked'] = len(rows)
    out['all_axiom_sets_sha256'] = hashlib.sha256(json.dumps(axioms,sort_keys=True).encode()).hexdigest()
    out['public_axioms'] = {n:a for n,a in axioms.items() if n in PUBLIC}
    require(set(out['public_axioms'])==PUBLIC,'missing exact CT public axioms')
    return out


def evidence_row(disabled=False):
    return {'schema':'p23-source-contrast-evidence/v1','disabled':disabled,'evidence_valid':False,
            **{key:False for key in CLAIMS}}


def fastconsume(certificate_path=None,disabled=False):
    result = evidence_row(disabled)
    if disabled:
        return result
    canonical = HERE/'certification.json'
    identity = frozen(canonical)
    data = canonical.read_bytes()
    require((canonical if certificate_path is None else Path(certificate_path)).read_bytes()==data,
            'CT override must be an immutable original-byte copy')
    cert = json.loads(data)
    require(cert.get('schema')=='p23-source-contrast-lean-certification/v1' and cert.get('status')=='certified'
            and cert.get('kernel_claims')==CLAIMS and cert.get('mouth_scope')==SCOPES
            and cert.get('authorized_axioms')==sorted(ALLOWED) and set(cert.get('public_mouths',[]))==PUBLIC,
            'CT exact source/constant-null scope changed')
    require(set(cert['bindings'])=={rel(p) for p in owned_sources()},'CT source inventory changed')
    for name, row in cert['bindings'].items():
        blob = subprocess.check_output(['git','show',row['commit']+':'+name],cwd=ROOT)
        require(hashlib.sha256(blob).hexdigest()==row['sha256'] and blob==(ROOT/name).read_bytes(),
                'CT source binding changed: '+name)
    lake = cert['historical_lake_binding']
    historical = subprocess.check_output(['git','show',lake['commit']+':Lean/lakefile.toml'],cwd=ROOT)
    require(hashlib.sha256(historical).hexdigest()==lake['sha256'],'CT historical Lake configuration changed')
    for row in json.loads((HERE/'sources.json').read_text())['inputs']:
        actual = hashlib.sha256(historical).hexdigest() if row['path']=='Lean/lakefile.toml' else digest(ROOT/row['path'])
        require(actual==row['sha256'],'CT contract context input changed: '+row['path'])
    focus = cert['focused_verification']
    require(focus['fresh_source_compilation'] is True and focus['trust_level']==0 and focus['warning_as_error'] is True
            and [c['source'] for c in focus['commands']]==[rel(p) for p in CHAIN]
            and all(c['exit_code']==0 for c in focus['commands']),'CT fresh strict evidence incomplete')
    audit = cert['source_audit']
    require(audit['axiom_declarations_checked']==audit['source_declarations']+audit['independent_declarations']
            and set(audit['public_axioms'])==PUBLIC and all(set(a)<=ALLOWED for a in audit['public_axioms'].values()),
            'CT complete Std3 summary changed')
    closure = cert['actual_import_closure']
    current = source_closure(closure['toolchain_source_root'],True)
    modules, search = current.pop('inventory'),current.pop('search_roots')
    require(current==closure,'CT complete semantic import source changed')
    registry = independent_registry_change(historical,(PROJECT/'lakefile.toml').read_bytes(),set(modules),search)
    result.update(CLAIMS)
    result.update({'evidence_valid':True,'certificate_sha256':identity['sha256'],'certificate_commit':identity['commit'],
                   'authorized_axioms':cert['authorized_axioms'],'public_mouths':cert['public_mouths'],
                   'lake_registry':registry,'new_source_or_solver_execution':False})
    return result


def certify(lsp_record):
    require(not (HERE/'certification.json').exists(),'CT first certificate already exists')
    require(lsp_record==json.loads((HERE/'lsp-status.json').read_text())
            and lsp_record['candidate_sha256']==EXPECTED['ContrastSource.lean']
            and lsp_record['consumer_sha256']==EXPECTED['ContrastConsumer.lean']
            and lsp_record['persistent_LSP_success_claimed'] is False,'CT LSP status source mismatch')
    bindings = {rel(p):frozen(p) for p in owned_sources()}
    for p in CHAIN[:-1]:
        require(digest(p)==EXPECTED[p.name],'CT candidate/source hash mismatch: '+p.name)
    for name in ['criterion.md','sources.json']:
        blob = subprocess.check_output(['git','show',CONTRACT_FREEZE+':'+rel(HERE/name)],cwd=ROOT)
        require(blob==(HERE/name).read_bytes(),'CT precompile contract changed')
    historical = subprocess.check_output(['git','show',CONTRACT_FREEZE+':Lean/lakefile.toml'],cwd=ROOT)
    historical_lake = {'commit':CONTRACT_FREEZE,'sha256':hashlib.sha256(historical).hexdigest()}
    for row in json.loads((HERE/'sources.json').read_text())['inputs']:
        actual = hashlib.sha256(historical).hexdigest() if row['path']=='Lean/lakefile.toml' else digest(ROOT/row['path'])
        require(actual==row['sha256'],'CT frozen context changed: '+row['path'])
    for p in CHAIN:
        require(FORBIDDEN.search(p.read_text()) is None,'CT local trust escape: '+rel(p))
        require(not any('scratch' in n for n in header_imports(p)),'CT scratch production import')
    env = json.loads(subprocess.check_output(['lake','env','python3','-c','import json,os;print(json.dumps(dict(os.environ)))'],cwd=PROJECT,text=True))
    source_root = str(Path(subprocess.check_output(['lean','--print-prefix'],cwd=PROJECT,env=env,text=True).strip())/'src/lean')
    complete = source_closure(source_root,True)
    modules, search = complete.pop('inventory'),complete.pop('search_roots')
    registry = independent_registry_change(historical,(PROJECT/'lakefile.toml').read_bytes(),set(modules),search)
    checks = []
    with tempfile.TemporaryDirectory(prefix='p23-ct-independent-certify-') as fresh:
        env['LEAN_PATH'] = fresh+os.pathsep+env.get('LEAN_PATH','')
        for p in CHAIN:
            command = ['lean','--trust=0','-DwarningAsError=true','--root='+str(p.parent),'-o',str(Path(fresh)/(p.stem+'.olean')),str(p)]
            run = subprocess.run(command,cwd=PROJECT,env=env,capture_output=True,text=True,timeout=300)
            log = run.stdout+run.stderr
            checks.append({'source':rel(p),'command':[c.replace(fresh,'${fresh_olean}') for c in command],
                           'exit_code':run.returncode,'log_sha256':hashlib.sha256(log.encode()).hexdigest()})
            print(p.name+' fresh trust0/werror exit='+str(run.returncode),flush=True)
            if run.returncode:
                Path('/tmp/p23-ct-last-error.log').write_text(log)
                print(log[-10000:],flush=True)
                raise RuntimeError('CT scoped independent gate failed: '+p.name)
            if p.name=='ContrastCertification.lean':
                Path('/tmp/p23-ct-certification.log').write_text(log)
                source_audit = parse_audit(log)
    require(all(digest(ROOT/n)==b['sha256'] for n,b in bindings.items()),'CT source changed during certification')
    require(source_closure(source_root)==complete,'CT semantic imports changed during certification')
    report = {'schema':'p23-source-contrast-lean-certification/v1','version':'p23-source-contrast-ct0001','status':'certified',
              'classification':'bounded subordinate source probability-law and exact statistic readout',
              'criterion_precompile_freeze':CONTRACT_FREEZE,'audit_preexecution_freeze':bindings[rel(HERE/'ContrastCertification.lean')]['commit'],
              'bindings':bindings,'historical_lake_binding':historical_lake,'actual_import_closure':complete,
              'lake_registry':registry,'authorized_axioms':sorted(ALLOWED),'public_mouths':sorted(PUBLIC),
              'kernel_claims':CLAIMS,'mouth_scope':SCOPES,'source_audit':source_audit,
              'focused_verification':{'fresh_source_compilation':True,'trust_level':0,'warning_as_error':True,'commands':checks,'lsp':lsp_record},
              'source_access':{'new_scientific_or_statistical_results_read':False,'new_solver_execution':False,'raw_event_records_read':0,'external_or_hardware_contact':False}}
    (HERE/'certification.json').write_text(json.dumps(report,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    Path('/tmp/p23-ct-certify-capsule.json').write_text(json.dumps({'schema':'p23-source-contrast-certify-capsule/v1','phase':'certify','verdict':'certified','kernel_claims':CLAIMS,'mouth_scope':SCOPES,'source_audit':source_audit,'certification_sha256':digest(HERE/'certification.json')},ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':'certified','source_declarations':source_audit['source_declarations'],'independent_declarations':source_audit['independent_declarations'],'import_modules':complete['modules'],'certificate_sha256':digest(HERE/'certification.json')}),flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check-only',action='store_true')
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--disabled',action='store_true')
    parser.add_argument('--lsp-record',type=Path)
    args = parser.parse_args()
    if args.check_only or args.disabled:
        print(json.dumps(fastconsume(args.certificate,args.disabled),ensure_ascii=False,indent=2))
    else:
        require(args.lsp_record is not None and args.certificate is None,'fresh CT certification requires exact LSP status record')
        certify(json.loads(args.lsp_record.read_text()))


if __name__=='__main__':
    main()
