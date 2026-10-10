"""Small explicit module reuse layer. Empty approved registry means Linux bootstrap.

Registry/catalog evidence is retained in source control independently of 3-day cache objects.
No approximate keys, cache-hit qualification, Windows inheritance or auto-approval.
"""
from __future__ import annotations
import json, os, time
from pathlib import Path
import dependency_scope as scope
import hosted_resources as resources

def read(p):return json.loads(Path(p).read_text())
def prepare(root,evidence,plan,keys,capture):
    registry=read(root/plan['reuse_policy']['registry'])
    require=scope.require
    require(registry['schema']=='annex.accepted-linux-reuse.v1','reuse registry schema')
    approved=registry['approved_producers'];prior=registry['modules'];cache=Path(os.environ['RUNNER_TEMP'])/'gss-qualified-cache'
    def present(n,outputs):
        return all((cache/r['path']).is_file() and (cache/r['path']).stat().st_size==r['bytes'] and resources.sha(cache/r['path'])==r['sha256'] for r in outputs)
    decisions=scope.classify(plan,keys,prior,approved,present)
    selected=next(s for s in plan['stages'] if s['stage']==os.environ['STAGE_NAME'])
    eligible=[n for n in selected['modules'] if decisions[n] in ('INHERITED','CACHE_MISS')]
    # Approved records are explicit source-controlled evidence, not self-asserted cached receipts.
    for producer in sorted({prior[n]['producer'] for n in eligible}):
        p=approved[producer]
        require(p['acceptance']=='OWNER_ACCEPTED_LINUX_QUALIFICATION' and p['repository_id']==1367564442,'unaccepted producer')
        require(p['qualification']=='PASS' and p['platform']=='linux' and p['catalog_sha256'],'incomplete producer qualification')
        for field in ('catalog','qualification'):
            path=root/p[field+'_path']
            require(path.resolve().is_relative_to(root.resolve()) and not path.is_symlink(),'approved evidence path')
            require(resources.sha(path)==p[field+'_sha256'],'approved evidence hash')
        catalog=read(root/p['catalog_path']);qualification=read(root/p['qualification_path'])
        from segmented_qualification import CHECKS
        require(qualification['qualification']=='PASS' and set(qualification['checks'])==set(CHECKS) and set(qualification['checks'].values())=={'PASS'},'producer gates incomplete')
        require(catalog['identity']['commit']==qualification['identity']['commit']==p['commit'],'catalog/qualification producer binding')
        require(str(catalog['identity']['run_id'])==str(p['run_id']) and str(catalog['identity']['run_attempt'])==str(p['run_attempt']),'catalog run binding')
        for n in eligible:
            if prior[n]['producer']!=producer:continue
            source=catalog['modules'][n]
            require(all(prior[n].get(k)==v for k,v in source.items()),'accepted module differs from qualified catalog '+n)
        actual=json.loads(capture(['gh','api',f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{p['run_id']}"]))
        require(actual['head_sha']==p['commit'] and actual['status']=='completed' and actual['conclusion']=='success','producer run is not exact successful Linux qualification')
        require(str(actual['run_attempt'])==str(p['run_attempt']),'producer attempt changed')
    # Optional exact per-module artifact locators are attached when catalog is accepted.
    # A missing/expired cache causes only this required module to be compiled again.
    for n in eligible:
        if present(n,prior[n]['outputs']):continue
        locator=prior[n].get('cache_artifact')
        if not locator:continue
        producer=approved[prior[n]['producer']]
        try:a=json.loads(capture(['gh','api',f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/artifacts/{locator['id']}" ]))
        except ValueError as exc:
            resources.write(evidence/('cache-miss-'+scope.digest(n)+'.json'),dict(module=n,status='CACHE_MISS',reason=str(exc)))
            continue
        # Exact id lookup avoids an incomplete list or an approximate restore-key fallback.
        require(a['id']==locator['id'] and a['name']==locator['name'] and str(a['workflow_run']['id'])==str(producer['run_id']),'reuse artifact locator')
        from datetime import datetime
        if a['expired'] or datetime.fromisoformat(a['expires_at'].replace('Z','+00:00')).timestamp()-time.time()<plan['job_timeout_minutes']*60:continue
        require(a['workflow_run']['head_sha']==producer['commit'],'reuse artifact source')
        require(locator['module']==n and locator['outputs']==prior[n]['outputs'],'module locator scope')
        allowance=sum(r['bytes'] for r in prior[n]['outputs'])+65536
        resources.admission(root,evidence,'before_qualified_module_download',remaining_output_bytes=selected['limits']['own_output_bytes'],temporary_bytes=a['size_in_bytes']+allowance)
        dest=cache/'transport'/scope.digest(n);dest.mkdir(parents=True,exist_ok=True)
        capture(['gh','run','download',str(producer['run_id']),'--repo',os.environ['GITHUB_REPOSITORY'],'--name',a['name'],'--dir',str(dest)])
        files={p.relative_to(dest).as_posix() for p in dest.rglob('*') if p.is_file()}
        require(files=={r['path'] for r in prior[n]['outputs']},'reuse artifact missing/excess output')
        for r in prior[n]['outputs']:resources.move_exact(dest/r['path'],cache/r['path'],r,dest,cache)
    decisions=scope.classify(plan,keys,prior,approved,present)
    resources.write(evidence/'reuse-accounting.json',dict(mode='QUALIFIED_DELTA' if any(decisions[n]=='INHERITED' for n in selected['modules']) else 'BOOTSTRAP_OR_REQUIRED_CACHE_MISS',all_targets=decisions,selected_targets=selected['modules'],available_approved_producers=sorted(approved),cache_expiry_invalidates_proof=False))
    return decisions,prior,cache
def inherit(n,prior,cache,root,current_dependencies):
    rec=prior[n]
    scope.require(rec['local_dependencies']==current_dependencies,'inherited dependency output drift')
    for row in rec['outputs']:resources.move_exact(cache/row['path'],root/row['path'],row,cache,root/'.lake/build/lib/lean')
    main=next(r for r in rec['outputs'] if r['path'].endswith(n.replace('.','/')+'.olean'))
    return dict(execution='INHERITED',source_sha256=rec['source_sha256'],exit_code=0,output_sha256=main['sha256'],local_dependencies=current_dependencies,outputs=rec['outputs'],qualification_key=rec['key'],inherited_producer=rec['producer'],type_axiom_census_sha256=rec['type_axiom_census_sha256'])
