"""Exact dependency scopes and explicit qualification reuse; no network or mutation on import."""
from __future__ import annotations
import hashlib, json

def require(ok, message):
    if not ok: raise ValueError(message)
def digest(value):
    return hashlib.sha256((json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
def closure(graph, roots):
    seen=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n in seen:continue
        require(n in graph,'unresolved dependency '+n)
        seen.add(n);todo.extend(graph[n])
    return seen
def reverse_closure(graph, changed):
    rev={n:[] for n in graph}
    for n,ds in graph.items():
        for d in ds:require(d in rev,'unresolved dependency '+d);rev[d].append(n)
    return closure(rev,changed)
def topological(graph):
    states={};out=[]
    def visit(n):
        require(states.get(n)!=1,'dependency cycle '+n)
        if states.get(n)==2:return
        require(n in graph,'unresolved dependency '+n);states[n]=1
        for d in graph[n]:visit(d)
        states[n]=2;out.append(n)
    for n in sorted(graph):visit(n)
    return out
def flags(n):
    # Bounded process envelopes, not changes to Lean's logic or kernel checks.
    # R9 adds only CompactRepresentationRigidity; retained checkpoints keep their flags.
    memory='5120' if n in (
        'MathlibAnnex.Analysis.CStarAlgebra.DirectSum.DiscreteCCR',
        'MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactRepresentationRigidity',
    ) else '4096'
    f=['-j','1','-M',memory]
    if n.endswith(('.CompactOperatorDiagonal','.DirectSum.DiscreteCCR','.DirectSum.CompactlyRepresentedDecomposition','.Representation.ReducedAtomic','.Representation.DiscreteCCRCompact','.GeometricStructure.CompactTrichotomyTransport','.GeometricStructure.CompactRepresentationRigidity')):
        f+=['-DElab.async=false','-Dprofiler=true','-Dprofiler.threshold=1000','-DstderrAsMessages=false']
    return f
def module_keys(plan, compiler, platform, machine):
    """Candidate/workflow/doc identity is deliberately separate from mathematical reuse keys."""
    graph=plan['dependency_edges'];keys={}
    for n in topological(graph):
        keys[n]=digest(dict(module=n,source=plan['source_modules'][n],compiler=compiler,
            platform=platform,machine=machine,flags=flags(n),provider=plan['module_provider_identities'][n],
            imports={d:keys[d] for d in graph[n]},qualification_contract='module-origin-types-axioms-v1'))
    return keys
def classify(plan, keys, prior, approved_producers, present):
    """Only completed Linux qualification slices can be inherited; cache loss is not proof loss.

    The approved producer records must be retained outside the expiring artifact cache.
    This pure function never manufactures an approval, artifact, or successful Linux run.
    """
    result={}
    for n in topological(plan['dependency_edges']):
        r=prior.get(n)
        if not r:result[n]='FRESH';continue
        valid=(r.get('key')==keys[n] and r.get('platform')=='linux' and
               r.get('qualification')=='PASS' and r.get('producer') in approved_producers and
               r.get('type_axiom_census_sha256') and r.get('outputs') and
               all(result[d] not in ('FRESH','INVALIDATED') for d in plan['dependency_edges'][n]))
        result[n]='INVALIDATED' if not valid else ('INHERITED' if present(n,r['outputs']) else 'CACHE_MISS')
    require(set(result)==set(plan['source_modules']),'reuse accounting lost targets')
    return result
def validate_selected_outputs(expected, actual):
    require(set(expected)==set(actual),'missing or excess restored modules')
    for n,rows in expected.items():require(rows==actual[n],'restored output identity '+n)
def bundles(stages, graph):
    """Partition each producer by identical downstream consumers: no duplicate stored objects."""
    scopes={s['stage']:closure(graph,s['modules'])-set(s['modules']) for s in stages}
    out=[]
    for s in stages:
        grouped={}
        for n in s['modules']:
            users=tuple(k for k,ns in scopes.items() if n in ns)
            grouped.setdefault(users,[]).append(n)
        for i,(users,ns) in enumerate(sorted(grouped.items())):
            out.append(dict(id=s['stage']+'-b'+str(i).zfill(2),producer=s['stage'],consumers=list(users),modules=ns))
    require(len({n for b in out for n in b['modules']})==sum(len(s['modules']) for s in stages),'bundle partition')
    return out
