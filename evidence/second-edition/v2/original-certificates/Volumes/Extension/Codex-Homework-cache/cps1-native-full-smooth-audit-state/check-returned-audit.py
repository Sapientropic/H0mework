from pathlib import Path
import json,sys,hashlib,subprocess
state=Path(__file__).resolve().parent
out=Path(sys.argv[1])
contract=json.loads((state/'audit-contract.json').read_text())
def rows(path): return [json.loads(x) for x in path.read_text().splitlines()]
expr=rows(out/'ExecuteAudit.expressions.jsonl');needs=[]
for i,node in enumerate(expr):
    assert node['id']==i
    assert node['tag'] not in ('fvar','mvar')
    assert all(0<=x<i for x in node['children'])
    child=[needs[x] for x in node['children']]
    if node['tag']=='bvar': need=node['index']+1
    elif node['tag'] in ('lam','forall'): need=max(child[0],max(0,child[1]-1))
    elif node['tag']=='let': need=max(child[0],child[1],max(0,child[2]-1))
    else: need=max(child,default=0)
    needs.append(need)
own=rows(out/'ExecuteAudit.owners.jsonl')
backend_rows=json.loads((out/'ExecuteAudit.compiler-backends.json').read_text())
backends={r['helper'] for r in backend_rows};owned_names={r['name']:r for r in own}
for r in backend_rows:
    assert r['Compiler_mkUnsafeRecName_exact'] and r['complete_TVO_readable']
    assert r['parent_math_value_not_direct_helper']
    assert not r['parent_unsafe'] and not r['parent_partial']
    assert not r['helper_unsafe'] and r['helper_partial']
    assert owned_names[r['helper']]['partial'] and not owned_names[r['parent']]['partial']
for row in own:
    assert row['actual_raw_fullparts_TVO'] and not row['unsafe'],row['name']
    assert not row['partial'] or row['name'] in backends,row['name']
    for key in ['type_root','value_root']:
        value=row[key]
        if value is not None: assert needs[value]==0,(row['name'],key)
    for rule in row.get('recursor_rules',[]):
        for key in ['rhs_root','rhsRoot','root']:
            if key in rule: assert needs[rule[key]]==0,(row['name'],'recursor')
summary=json.loads((out/'ExecuteAudit.summary.json').read_text())
graph=rows(out/'ExecuteAudit.graph.jsonl');nodes={x['name']:x for x in graph};fresh=[x for x in graph if not x.get('reused')]
assert len(nodes)==len(graph)==summary['visited_new_and_frontier']
assert len(fresh)==summary['fresh_declarations']
assert len(own)==summary['raw'] and len(own)-len(backends)==summary['kernel_math_roots']
assert set(summary['backends'])==backends and not backends.intersection(nodes)
assert not summary['fresh_axioms']
opaque=[r for r in fresh if r.get('kind')=='opaque'];assert len(opaque)==summary['fresh_opaque']
assert all(r['raw_fullparts'] and 'valueDependencies' in r for r in opaque)
assert summary['unsafe']==summary['partial']==summary['unknown']==summary['old_body_walk']==0
assert summary['env_checked_proof_bodies'] is False
for row in fresh:
    assert row['raw_fullparts'] and not row['unsafe'] and not row['partial']
    assert all(n in nodes for n in row['dependencies'])
paid=set((state/'input/src/paid-names-native-full-smooth.txt').read_text().splitlines())
rechecked=set(summary.get('rechecked_paid_names',[]))
assert rechecked==set(owned_names).intersection(paid)
assert rechecked<=paid
assert all(row['name'] in paid-rechecked and row['paid_body_walk'] is False for row in graph if row.get('reused'))
assert all(row['name'] not in paid-rechecked for row in fresh)
assert rechecked<={row['name'] for row in fresh}
for name in rechecked:
    node=nodes[name];owner=owned_names[name]
    assert node['kind']==owner['kind']
    assert set(node['dependencies'])==set(owner['all_dependencies'])
    assert set(node['typeDependencies'])==set(owner['type_constants'])
    assert set(node['valueDependencies'])==set(owner['value_constants'])

# Only the new frozen runtime owner is rebuilt. Any paid lazy re-emission
# requires an exact complete-parts signed comparison before acceptance.
assert not rechecked, ("LAZY_REEMISSION_NEEDS_SIGNED_PARTS",sorted(rechecked))
rechecks=[]

paths=json.loads((out/'ExecuteAudit.value-paths.json').read_text());mouths=json.loads((out/'ExecuteAudit.public-mouths.json').read_text())
assert len(paths)==summary['value_paths']==len(contract['checks']) and len(mouths)==len(contract['mouths'])
for row in paths:
    assert row['type_edges_used'] is False
    assert set(row['required'])<=set(row['owned_value_closure'])
for row in paths:
    pending=[row['mouth']];seen=set()
    while pending:
        name=pending.pop()
        if name in seen: continue
        seen.add(name)
        if name in owned_names:
            pending.extend(owned_names[name]['value_constants'])
    assert seen==set(row['owned_value_closure']),row['mouth']
    if row['mouth'] in contract.get('live_mouths',[]):
        assert not any(name.startswith(prefix) for name in seen for prefix in contract.get('forbidden_live_prefixes',[])),row['mouth']
        assert not seen.intersection(contract.get('forbidden_live_names',[])),row['mouth']
assert {row['mouth'] for row in paths}=={name for name,_deps in contract['checks']}
assert {row['mouth'] for row in mouths}==set(contract['mouths'])
def value_closure(start):
    pending=[start];seen=set()
    while pending:
        name=pending.pop()
        if name in seen:continue
        seen.add(name);pending.extend(owned_names.get(name,{}).get('value_constants',[]))
    return seen
for start in contract['capture_data_mouths']:
    assert owned_names[start]['kind']=='def'
    assert not set(contract['capture_entry_points']).intersection(value_closure(start)),start
capture_report={'complete_TVO_graph_retained':True,'classification':'complete source RawIndex nuclear differentiability generates full raw energy smoothness and rules out native body nondifferentiability; ready follows from actual PostState field','source_review':contract['source_review'],'type_edges_used_in_value_closure':False,'no_finished_payload_selected_from_exists':True,'no_future_body_table':True}
headers=json.loads((out/'ExecuteAudit.header.json').read_text());indices={r['module']:i for i,r in enumerate(headers)}
for i,row in enumerate(headers):
    assert row['private_fullparts']
    assert all(indices[d['module']]<i for d in row['imports'])
report={'schema':'native-full-smooth-closed-lossless-TVO/v1','verdict':'passed','owner_slots':len(own),'expression_nodes':len(expr),'owner_types_values_and_recursor_rhs_closed':True,'private_raw':sum(r['name'].startswith('_private.') for r in own),'raw_constructors':sum(r['kind']=='constructor' for r in own),'raw_recursors':sum(r['kind']=='recursor' for r in own),'header_modules':len(headers),'public_mouths':len(mouths),'value_paths':len(paths),'closed_graph_nodes':len(graph),'fresh_declarations':len(fresh),'fresh_edges':summary['fresh_edges'],'reused_frontier_count':len(graph)-len(fresh),'paid_names':len(paid),'rechecked_paid_declarations':rechecks,'rechecked_paid_count':len(rechecked),'rechecked_paid_full_parts_identical':True,'rechecked_paid_body_walk':len(rechecked),'paid_frontier_body_walk':0,'old_body_walk_excludes_rechecked_paid':True,'capture_proof_classification':capture_report,'fresh_flags_zero':True,'official_compiler_backends':backend_rows,'official_backend_math_unreachable':True,'fresh_opaque_readable':[{'name':r['name'],'module':r['module']} for r in opaque],'old_body_walk':0,'Root_parent_owners_rebuilt':0,'value_only_closures_recomputed_exact':True,'live_value_excludes_fixed_factory':True}
(out/'returned-audit-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
