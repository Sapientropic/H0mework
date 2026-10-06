"""Cut-free public family acceptance from immutable E and source-law certificates."""
from fractions import Fraction as F
from hashlib import sha256
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'.git').exists())
PUBLIC=HERE.parent
MW=PUBLIC/'multi-window'
CT=PUBLIC/'contrast-source'
BOOKS=['diag-02-54.xlsx','diag-03-43.xlsx','diag-19-45.xlsx','diag-xor1.xlsx','diag-xor2.xlsx','diag-xor3.xlsx']
PULSES={1:[6],3:[5,6,7],5:[4,5,6,7,8],7:[3,4,5,6,7,8,9],9:[2,3,4,5,6,7,8,9,10]}
SHEETS={1:'5',3:'456',5:'34567',7:'2345678',9:'123456789'}
FIELDS=('cut_free_public_family_source_signature_certified','full_run_counts_and_one_step_source_law_consumed')
FALSE_FIELDS=('hidden_cut_log_required','actual_hardware_identity_claimed','global_all_mask_family_rejected','original_CI_modified','controller_advance','new_stochastic_process_or_Ville_kernel','statistical_rejection_is_logical_impossibility')


def require(ok,message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).resolve().relative_to(ROOT).as_posix()


def frozen(path,commit=None):
    path=Path(path);name=relative(path)
    if commit is None:
        commit=subprocess.check_output(['git','log','-1','--format=%H','--',name],cwd=ROOT,text=True).strip()
    require(commit and subprocess.check_output(['git','show',commit+':'+name],cwd=ROOT)==path.read_bytes(),'unfrozen anytime source: '+name)
    return {'path':name,'commit':commit,'sha256':digest(path)}


def configuration():
    text=(HERE/'criterion.md').read_text()
    block=text.split('<!-- ANYTIME-SOURCE-FROZEN-BEGIN -->')[1].split('<!-- ANYTIME-SOURCE-FROZEN-END -->')[0]
    cfg=json.loads(block.split('```json')[1].split('```')[0])
    require(cfg['alpha']=='1/20' and cfg['epsilon']=='3/1000' and cfg['public_family_size']==24
            and cfg['spacelike_pulse_counts']==[1,3,5,7] and cfg['original_all_mask_family_size']==196602,'changed public family or alpha')
    bindings=[frozen(HERE/n) for n in ['criterion.md','sources.json','consume.py','tests.py']]
    for row in json.loads((HERE/'sources.json').read_text())['bindings']:
        require(digest(ROOT/row['path'])==row['sha256'],'anytime dependency source changed: '+row['path'])
    frozen(MW/'cross-verification.json',cfg['cross_first_commit'])
    frozen(CT/'certification.json',cfg['CT_first_commit'])
    return cfg,bindings


def source_law():
    spec=importlib.util.spec_from_file_location('p23_anytime_CT_fixed',CT/'certify.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    row=module.fastconsume()
    require(row['schema']=='p23-source-contrast-evidence/v1' and row['evidence_valid'] is True
            and all(row[k] is True for k in ['source_generated_probability_law_all_N',
              'source_negative_CH_implies_original_binomial_threshold','source_negative_CH_fixed_bet_expected_value_bound']),
            'source one-step law not certified')
    require(row['new_stochastic_process_or_Ville_kernel'] is False and row['actual_source_epoch_or_hardware_identified'] is False,'source authority scope changed')
    return row


def bound(Elo,family):
    require(Elo>0 and type(family) is int and family>0,'invalid E/family')
    return min(F(1),F(family)/Elo)


def signatures(inputs,cross,cfg):
    require(cross['schema']=='p23-public-multi-window-cross/v1' and cross['evidence_valid'] is True
            and cross['runs']==6 and cross['windows']==30 and cross['contrast_bets']==600,'incomplete fixed bet witness')
    require(inputs['settings_order']==['ab','ab_prime','a_prime_b','a_prime_b_prime']
            and inputs['outcomes_order']==['++','+0','0+','00'],'changed setting/outcome operation')
    books=inputs['diagnostic_workbooks'];require(len(books)==6 and {b['file'] for b in books}==set(BOOKS),'changed six-run family')
    entries=cross['local_count_review'];require(len(entries)==30,'missing full endpoint E')
    emap={(e['workbook'],e['N']):e for e in entries}
    require(len(emap)==30 and set(emap)=={(b,n) for b in BOOKS for n in PULSES},'duplicate or lookalike full endpoint')
    rows=[];aux=[]
    for book in books:
        require(len(book['groups'])==5,'missing public window')
        for g in book['groups']:
            require(not any(k in g for k in ['private_tau','cut_log','training_Nchi','actual_cutpoint_log']),'private cut input is forbidden')
            n=g['pulse_count'];require(n in PULSES and g['sheet']==SHEETS[n] and g['paper_pulse_numbers']==PULSES[n],'pulse mapping changed')
            counts=g['counts'];require(len(counts)==4 and all(len(r)==4 for r in counts)
              and all(type(x) is int and x>=0 for r in counts for x in r),'incomplete integer outcomes')
            exposure=sum(map(sum,counts))
            require(exposure==g['complete_trials_literal_count_sum'],'full endpoint exposure changed')
            if book['file']=='diag-xor3.xlsx':
                require(exposure==cfg['XOR3_complete_trials'],'old prefix substituted for complete run')
            W,L=counts[0][0],counts[1][1]+counts[2][2]+counts[3][0]
            e=emap[(book['file'],n)]
            require(e['wins']==W and e['losses']==L and e['four_window_spacelike_scope']==(n in [1,3,5,7]),'contrast count or Bell scope changed')
            lo,hi=F(e['e_value']['exact_lower']),F(e['e_value']['exact_upper'])
            require(0<lo<=hi,'invalid E directions')
            p1,p4,p24,pall=[bound(lo,m) for m in [1,4,24,196602]]
            require(F(e['single_anytime_p_upper'])==p1 and F(e['XOR3_four_window_p_upper'])==p4
                    and F(e['all_6_times_32767_p_upper'])==pall,'old family bound overwritten')
            row={'workbook':book['file'],'pulse_count':n,'paper_pulse_numbers':PULSES[n],
                 'complete_trials':exposure,'wins':W,'losses':L,'e_value':e['e_value'],
                 'single_anytime_p_upper':str(p1),'public_24_family_p_upper':str(p24),
                 'original_all_mask_family_p_upper':str(pall),'Bell_public_family_member':n in [1,3,5,7],
                 'public_24_family_rejects_nonpositive_CH_source':n in [1,3,5,7] and p24<F(cfg['alpha'])}
            if book['file']=='diag-xor3.xlsx':
                row['fixed_XOR3_four_window_p_upper']=str(p4)
            (rows if n in [1,3,5,7] else aux).append(row)
    require(len(rows)==24 and len(aux)==6,'incomplete retained public family')
    selected=next(r for r in rows if r['workbook']=='diag-xor3.xlsx' and r['pulse_count']==5)
    require(selected['wins']==6541 and selected['losses']==5898,'XOR3 source signature changed')
    require(F(selected['original_all_mask_family_p_upper'])==1,'old full-mask negative result changed')
    return rows,aux,selected


def generate():
    cfg,bindings=configuration();ct=source_law()
    inputs=json.loads((PUBLIC/'public-summaries/inputs.json').read_text())
    cross=json.loads((MW/'cross-verification.json').read_text())
    for b in inputs['diagnostic_workbooks']:
        require(digest(PUBLIC/'public-summaries'/b['file'])==b['sha256'],'original public workbook changed')
    rows,aux,selected=signatures(inputs,cross,cfg)
    rejected=selected['public_24_family_rejects_nonpositive_CH_source']
    return {'schema':'p23-anytime-public-source-evidence/v1','version':cfg['version'],'evidence_valid':True,
            **{key:True for key in FIELDS},**{key:False for key in FALSE_FIELDS},'disabled':False,
            'outcome':'PUBLIC_24_FAMILY_REJECTS_NONPOSITIVE_CH_SOURCE' if rejected else 'PUBLIC_24_FAMILY_DOES_NOT_REJECT_NONPOSITIVE_CH_SOURCE',
            'alpha':cfg['alpha'],'epsilon':cfg['epsilon'],'public_family_size':24,
            'selected_XOR3_N5':selected,'public_spacelike_family':rows,'auxiliary_N9':aux,
            'source_law':ct,'bindings':bindings,'fixed_bets':{'grid_powers':[1,20],'mixture_weight':'1/20','new_bet_optimization':False},
            'scope':{'null':'each past-conditional source law has CH<=0 and the declared setting bounds',
                     'endpoint':'complete run; arbitrary stopping is covered by fixed-bet Ville interpretation',
                     'selection':'six published runs times four named spacelike windows; unknown mask searches are not certified',
                     'no_trial_stationarity_or_iid_required':True,'actual_predeclaration_or_cut_history_certified':False,
                     'new_stochastic_process_kernel':False,'original_CI_modified':False,'retrospective':True}}


def consume(certificate_path=None,disabled=False):
    if disabled:
        return {'schema':'p23-anytime-public-source-evidence/v1','disabled':True,'evidence_valid':False,
                **{key:False for key in FIELDS},**{key:False for key in FALSE_FIELDS}}
    canonical=HERE/'certification.json';binding=frozen(canonical)
    require((canonical if certificate_path is None else Path(certificate_path)).read_bytes()==canonical.read_bytes(),'anytime override must be an immutable original-byte copy')
    report=json.loads(canonical.read_text());require(report==generate(),'anytime public family certificate mismatch')
    return {**report,'certificate_sha256':binding['sha256'],'certificate_commit':binding['commit']}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--create',action='store_true')
    parser.add_argument('--certificate',type=Path);parser.add_argument('--disabled',action='store_true')
    args=parser.parse_args()
    if args.create:
        require(args.certificate is None and not args.disabled and not (HERE/'certification.json').exists(),'first immutable anytime receipt required')
        report=generate();(HERE/'certification.json').write_text(json.dumps(report,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    else:
        report=consume(args.certificate,args.disabled)
    print(json.dumps({k:report[k] for k in ['schema','evidence_valid','disabled']}
        |({'outcome':report['outcome'],'selected_XOR3_N5':report['selected_XOR3_N5']} if report['evidence_valid'] else {}),ensure_ascii=False,indent=2))


if __name__=='__main__':
    main()
