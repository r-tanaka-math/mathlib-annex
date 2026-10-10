"""Exact successful native outputs, independently of release qualification.

The source-bound registry is an explicit producer allowlist. A failed overall run
does not negate a completed module; it does not grant axiom/release qualification.
This layer uses dependency_scope.module_keys and never changes qualified_reuse.
"""
from __future__ import annotations
import hashlib, json, os, re, shutil, stat, subprocess, time, zipfile
from datetime import datetime
from pathlib import Path, PurePosixPath
import dependency_scope as scope
import hosted_resources as resources

require=scope.require
sha=resources.sha
FACETS=('.olean','.olean.private','.olean.server','.ilean','.ir')
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def atomic_write(p,value):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);temp=p.with_name(p.name+'.pending')
    with temp.open('w',encoding='utf-8') as f:
        json.dump(value,f,sort_keys=True,separators=(',',':'));f.write('\n');f.flush();os.fsync(f.fileno())
    os.replace(temp,p)
def safe_path(root,name):
    p=PurePosixPath(name)
    require(name and not p.is_absolute() and '\\' not in name and ':' not in name and all(x not in ('','.','..') and x==x.rstrip(' .') for x in name.split('/')),'unsafe checkpoint path')
    target=root.joinpath(*p.parts)
    require(target.resolve().is_relative_to(root.resolve()),'checkpoint path escape')
    for parent in [target,*target.parents]:
        require(not parent.is_symlink(),'checkpoint path link')
        if parent==root:break
    return target
def output_prefix(n):return '.lake/build/lib/lean/'+n.replace('.','/')
def source_arguments(root,relative):
    # Pinned Windows Lean rejects mixed POSIX relative paths under -R . .
    # Root relocation is not a mathematical compiler flag or a reuse identity.
    return (str(root),str(root/relative)) if os.name=='nt' else ('.',relative)
def validate_outputs(root,n,rows):
    prefix=output_prefix(n);names={r['path'] for r in rows}
    require(len(names)==len(rows) and prefix+'.olean' in names,'missing/duplicate main output '+n)
    require(names<={prefix+s for s in FACETS},'foreign output path '+n)
    for r in rows:
        p=safe_path(root,r['path'])
        require(p.is_file() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'missing/corrupt required facet '+r['path'])
    return next(r for r in rows if r['path']==prefix+'.olean')['sha256']
def record_success(root,n,plan,key,dependencies,command,command_path):
    require(command['exit_code']==0 and not command.get('stop_reason') and command.get('spawned') is True,'native terminal exit is not success')
    require(command['argv'][1:1+len(scope.flags(n))]==scope.flags(n),'native flags drift')
    require(command['argv'][-1]==source_arguments(root,plan['source_modules'][n]['path'])[1],'native source command')
    require(sha(root/plan['source_modules'][n]['path'])==plan['source_modules'][n]['sha256'],'native source drift')
    log=safe_path(command_path.parent,command['log']);require(sha(log)==command['log_sha256'],'native raw log drift')
    prefix=output_prefix(n)
    rows=[dict(path=prefix+s,bytes=p.stat().st_size,sha256=sha(p)) for s in FACETS if (p:=safe_path(root,prefix+s)).is_file()]
    main=validate_outputs(root,n,rows)
    return dict(execution='FRESH',qualification_key=key,source_sha256=plan['source_modules'][n]['sha256'],exit_code=0,output_sha256=main,local_dependencies=dependencies,outputs=rows,flags=scope.flags(n),command_receipt_sha256=sha(command_path),axioms='AXIOM_PENDING',checkpoint_state='BUILD_CHECKPOINT')
def eligible(plan,keys,record,n,producer,platform_name,machine,compiler):
    require(record['qualification_key']==keys[n] and record['source_sha256']==plan['source_modules'][n]['sha256'],'source/dependency key changed '+n)
    require(producer['platform']==platform_name and producer['machine']==machine and producer['compiler_sha256']==compiler,'compiler/platform mismatch')
    require(record['exit_code']==0 and record['flags']==scope.flags(n),'exit/flags mismatch')
    require(record.get('qualification')=='BUILD_CHECKPOINT' and record.get('axioms')=='AXIOM_PENDING','checkpoint must not claim qualification')
    require(set(record['local_dependencies'])==set(plan['dependency_edges'][n]),'dependency coverage')
def restore(root,cache,n,record,dependencies):
    require(record['local_dependencies']==dependencies,'checkpoint dependency output drift '+n)
    require(validate_outputs(cache,n,record['outputs'])==record['output_sha256'],'checkpoint main digest')
    # Validate every facet before moving the first; never import a partially checked module.
    for row in record['outputs']:
        resources.move_exact(cache/row['path'],root/row['path'],row,cache,root/'.lake/build/lib/lean')
    require(validate_outputs(root,n,record['outputs'])==record['output_sha256'],'restored output identity')
    return dict(record,execution='CHECKPOINT_RESTORED',checkpoint_state='CHECKPOINT_RESTORED',axioms='AXIOM_PENDING',qualification='BUILD_CHECKPOINT',local_dependencies=dependencies,checkpoint_producer=record['producer'])
def verify_producer(producer,repository,capture):
    require(producer['repository']==repository and producer['repository_id']==1367564442,'checkpoint repository')
    run=str(producer['run_id']);attempt=str(producer['attempt'])
    actual=json.loads(capture(['gh','api',f'repos/{repository}/actions/runs/{run}/attempts/{attempt}']))
    require(str(actual['id'])==run and str(actual['run_attempt'])==attempt and actual['head_sha']==producer['identity']['commit'] and actual['status']=='completed','exact producer run/attempt')
    job=json.loads(capture(['gh','api',f'repos/{repository}/actions/jobs/{producer["job_id"]}']))
    require(str(job['run_id'])==run and str(job['run_attempt'])==attempt and job['head_sha']==actual['head_sha'] and job['name']==producer['job_name'] and job['status']=='completed','exact producer job')
    require(job['conclusion']==producer['job_conclusion'] and producer['acceptance']=='BUILD_CHECKPOINT_ONLY_NOT_RELEASE_QUALIFICATION','producer evidence binding')
    # Deliberately no overall success requirement here. qualified_reuse retains it.
    return dict(run=actual,job=job,status='PRODUCER_VERIFIED_BUILD_CHECKPOINT_ONLY')
def fetch_artifact(root,evidence,repository,producer,locator,dest,expanded_cap,own_allowance,capture):
    a=json.loads(capture(['gh','api',f'repos/{repository}/actions/artifacts/{locator["id"]}']))
    require(all(a[k]==locator[k] for k in ['id','name','digest','size_in_bytes']),'artifact exact id/digest binding')
    require(str(a['workflow_run']['id'])==str(producer['run_id']) and a['workflow_run']['head_sha']==producer['identity']['commit'],'artifact producer source')
    require(a['name'].endswith('-'+str(producer['run_id'])+'-'+str(producer['attempt'])),'artifact attempt binding')
    require(not a['expired'] and datetime.fromisoformat(a['expires_at'].replace('Z','+00:00')).timestamp()>time.time(),'checkpoint artifact expired')
    require(a['size_in_bytes']<=expanded_cap+65536,'checkpoint compressed cap')
    resources.admission(root,evidence,'checkpoint_download_'+str(a['id']),remaining_output_bytes=own_allowance,temporary_bytes=a['size_in_bytes']+expanded_cap)
    archive=dest.parent/(dest.name+'.zip');dest.parent.mkdir(parents=True,exist_ok=True)
    require(not archive.exists() and not dest.exists(),'checkpoint transport must be fresh')
    with archive.open('xb') as out:
        cp=subprocess.run(['gh','api',f'repos/{repository}/actions/artifacts/{a["id"]}/zip'],stdout=out,stderr=subprocess.PIPE)
    require(cp.returncode==0,'checkpoint download failed '+cp.stderr.decode(errors='replace')[-1000:])
    require(archive.stat().st_size==a['size_in_bytes'] and 'sha256:'+sha(archive)==a['digest'],'checkpoint transport digest')
    with zipfile.ZipFile(archive) as z:
        infos=[i for i in z.infolist() if not i.is_dir()];names=[i.filename for i in infos]
        require(len({n.casefold() for n in names})==len(names),'checkpoint collision')
        require(sum(i.file_size for i in infos)<=expanded_cap,'checkpoint expansion cap')
        for i in infos:
            safe_path(dest,i.filename)
            require(not i.flag_bits&1 and stat.S_IFMT(i.external_attr>>16) in (0,stat.S_IFREG),'checkpoint special file')
            require(not any(p.as_posix() in names for p in PurePosixPath(i.filename).parents if p.as_posix()!='.'),'checkpoint file parent')
        require(z.testzip() is None,'checkpoint CRC')
        for i in infos:
            p=safe_path(dest,i.filename);p.parent.mkdir(parents=True,exist_ok=True)
            with z.open(i) as inp,p.open('xb') as out:shutil.copyfileobj(inp,out)
    atomic_write(evidence/('checkpoint-artifact-'+str(a['id'])+'.json'),dict(api=a,archive_sha256=sha(archive),files=len(infos),expanded_bytes=sum(i.file_size for i in infos),producer_attempt=producer['attempt']))
    # Verified archive is reproducible from the retained exact locator; release its
    # task-local compressed duplicate only after complete verified extraction.
    require(archive.resolve().is_relative_to(dest.parent.resolve()) and not archive.is_symlink(),'archive cleanup containment')
    archive.unlink()
    return a
def registry(root,plan):
    policy=plan.get('checkpoint_policy')
    if not policy:return dict(schema='annex.build-checkpoints.v1',producers={},modules={},prior_stage_locators={})
    p=safe_path(root,policy['registry']);require(sha(p)==policy['registry_sha256'],'checkpoint registry binding')
    value=read(p);require(value['schema']=='annex.build-checkpoints.v1','checkpoint schema');return value
def restore_expected(root,cache,n,record,dependencies,decision):
    """An eligible retained success must not silently become a new native build."""
    require(decision=='AVAILABLE_BUILD_CHECKPOINT','CHECKPOINT_RECOVERY_REQUIRED '+n+' '+decision)
    require(record['local_dependencies']==dependencies,'CHECKPOINT_DEPENDENCY_RECOVERY_REQUIRED '+n)
    return restore(root,cache,n,record,dependencies)

def prepare(root,evidence,plan,keys,compiler,platform_name,machine,selected,capture):
    reg=registry(root,plan);prior=reg['modules'];cache=Path(os.environ['RUNNER_TEMP'])/'gss-build-checkpoints'
    decisions={n:'NOT_AVAILABLE' for n in selected};accepted={};producers={};bundles={};repo=os.environ['GITHUB_REPOSITORY']
    for n in selected:
        if n not in prior:continue
        record=prior[n];p=reg['producers'][record['producer']]
        try:eligible(plan,keys,record,n,p,platform_name,machine,compiler)
        except ValueError as exc:decisions[n]='INVALIDATED';atomic_write(evidence/('checkpoint-invalid-'+scope.digest(n)+'.json'),dict(module=n,reason=str(exc)));continue
        accepted[n]=record;producers[record['producer']]=p;decisions[n]='CACHE_MISS'
        bundle=p['module_bundles'][n];bundles[(record['producer'],bundle)]=p['bundles'][bundle]
    verified=set()
    for token,p in producers.items():
        try:
            observation=verify_producer(p,repo,capture);atomic_write(evidence/('checkpoint-producer-'+scope.digest(token)+'.json'),observation);verified.add(token)
        except ValueError as exc:
            atomic_write(evidence/('checkpoint-unavailable-'+scope.digest(token)+'.json'),dict(reason=str(exc),status='PRODUCER_UNVERIFIED'))
    limits=next(s['limits'] for s in plan['stages'] if s['modules']==selected)
    for (token,bundle),locator in bundles.items():
        if token not in verified:continue
        p=producers[token];all_records={n:r for n,r in prior.items() if r['producer']==token and p['module_bundles'][n]==bundle}
        cap=sum(o['bytes'] for r in all_records.values() for o in r['outputs'])
        dest=cache/'transport'/str(locator['id'])
        try:
            fetch_artifact(root,evidence,repo,p,locator,dest,cap,limits['own_output_bytes'],capture)
            expected={o['path'] for r in all_records.values() for o in r['outputs']}
            require({x.relative_to(dest).as_posix() for x in dest.rglob('*') if x.is_file()}<=expected,'bundle excess facets')
            for n in selected:
                if n not in accepted or accepted[n]['producer']!=token or p['module_bundles'][n]!=bundle:continue
                try:validate_outputs(dest,n,accepted[n]['outputs'])
                except (ValueError,OSError) as exc:
                    atomic_write(evidence/('checkpoint-module-miss-'+scope.digest(n)+'.json'),dict(module=n,reason=str(exc),status='CACHE_MISS'));continue
                for row in accepted[n]['outputs']:resources.move_exact(dest/row['path'],cache/row['path'],row,dest,cache)
                decisions[n]='AVAILABLE_BUILD_CHECKPOINT'
        except (ValueError,OSError,zipfile.BadZipFile) as exc:
            atomic_write(evidence/('checkpoint-cache-miss-'+str(locator['id'])+'.json'),dict(reason=str(exc),modules=sorted(all_records),status='CACHE_MISS_NOT_QUALIFICATION_FAILURE'))
    atomic_write(evidence/'checkpoint-accounting.json',dict(selected=decisions,restored_is_qualified=False,axioms='AXIOM_PENDING',producer_locators={k:dict(run_id=p['run_id'],attempt=p['attempt'],job_id=p['job_id']) for k,p in producers.items()}))
    return decisions,accepted,cache

def validate_stage_record(record,receipt_record):
    # A re-saved bundle has a new transport producer; its original receipt keeps
    # the preceding producer. Every native/source/output field still matches.
    for key,value in receipt_record.items():
        expected=record.get('previous_checkpoint_producer',record['producer']) if key=='producer' else record[key]
        require(expected==value,'source-bound receipt mismatch '+key)

def prior_stage(root,evidence,plan,stage,ident,dest,capture):
    """Explicit old run/attempt fallback, never an approximate latest-artifact lookup."""
    reg=registry(root,plan);token=reg['prior_stage_locators'].get(stage)
    require(token in reg['producers'],'no explicit prior-attempt producer '+stage)
    p=reg['producers'][token];require(p['stage']==stage,'prior stage locator mismatch')
    observation=verify_producer(p,os.environ['GITHUB_REPOSITORY'],capture)
    atomic_write(evidence/('prior-stage-producer-'+stage+'.json'),observation)
    fetch_artifact(root,evidence,p['repository'],p,p['receipt'],dest,32*2**20,0,capture)
    original=dest/'stage.json';require(sha(original)==p['receipt_sha256'],'prior receipt bytes')
    r=read(original);require(r['identity']==p['identity'] and r['status']=='PASS','prior full stage incomplete')
    wanted=next(s['modules'] for s in plan['stages'] if s['stage']==stage)
    require(set(r['modules'])==set(wanted),'prior stage coverage')
    import platform
    keys=scope.module_keys(plan,p['compiler_sha256'],'linux',platform.machine())
    for n in wanted:
        record=reg['modules'][n];require(record['producer']==token,'prior module producer')
        eligible(plan,keys,record,n,p,'linux',platform.machine(),p['compiler_sha256'])
        validate_stage_record(record,r['modules'][n])
        r['modules'][n]=dict(record,execution='CHECKPOINT_RESTORED',checkpoint_producer=token,checkpoint_state='CHECKPOINT_RESTORED')
    atomic_write(evidence/('original-prior-stage-'+stage+'.json'),read(original))
    r['identity']=ident;r['checkpoint_original_identity']=p['identity'];atomic_write(original,r)
    budget=read(dest/'upload-budget.json');require(budget['identity']==p['identity'] and budget['status']=='PASS','prior budget provenance')
    atomic_write(evidence/('original-prior-budget-'+stage+'.json'),budget)
    budget['original_identity']=budget['identity'];budget['identity']=ident
    budget['allocation']='EXPLICIT_PRIOR_ATTEMPT_ARTIFACTS_CHARGED_TO_CURRENT_CUMULATIVE_BOUND'
    atomic_write(dest/'upload-budget.json',budget)
    return p
