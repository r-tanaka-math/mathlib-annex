"""Bounded transport for exact module scopes on the existing private Actions service."""
from __future__ import annotations
import hashlib, json, os, platform, shutil, subprocess, time
from pathlib import Path
import dependency_scope as scope
import hosted_resources as resources

def require(ok,msg):scope.require(ok,msg)
def sha(p):return resources.sha(p)
def write(p,x):resources.write(p,x)
def read(p):return json.loads(Path(p).read_text())
def selected(plan):return next(s for s in plan['stages'] if s['stage']==os.environ['STAGE_NAME'])
def reserve(plan):return resources.REPORT_CAP+len(plan['stages'])*131072
def paths(root,n,row):
    if row['owner'] in ('lean','lake'):
        tc=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())
        base=tc/'src/lean';base=base/'lake' if row['owner']=='lake' else base
    else:base=root/'.lake/packages'/row['owner']
    return base/row['path']
def validate_provider_sources(root,plan):
    graph=read(root/'docs/qualification/provider-graph.json');st=selected(plan)
    # Validate all selected source identities; import-time/meta/plugin edges are retained.
    roots={}
    prefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())
    for n in st['external_modules']:
        r=graph[n];owner=r['owner']
        base=prefix/'src/lean' if owner=='lean' else prefix/'src/lean/lake' if owner=='lake' else root/'.lake/packages'/owner
        p=base/r['path'];require(p.is_file() and not p.is_symlink(),'provider source missing '+n)
        require(hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()==r['sha256'],'provider source drift '+n)
        roots[n]=dict(owner=owner,source_sha256=r['sha256'])
    return roots
def verify_expansion(root,plan):
    graph=read(root/'docs/qualification/provider-graph.json');rows=[]
    for n in selected(plan)['cache_modules']:
        r=graph[n];base=root/'.lake/packages'/r['owner']/'.lake/build/lib/lean'/n.replace('.','/')
        main=Path(str(base)+'.olean');require(main.is_file(),'requested cache module missing '+n)
        # Every official sibling is kept; hashes prove the actual expanded objects retained.
        for p in sorted(base.parent.glob(base.name+'.*')):
            require(not p.is_symlink(),'provider artifact link')
            if p.is_file():rows.append(dict(path=p.relative_to(root).as_posix(),bytes=p.stat().st_size,sha256=sha(p)))
    return rows
def cache_get(root,evidence,ident,plan):
    resources.initialize_cache(root,evidence,ident)
    # Lake resolves the existing lock without lake update or a source build.
    subprocess.run(['lake','env','lean','--version'],cwd=root,check=True)
    for dep,rev in plan['locked_dependencies'].items():
        require(subprocess.check_output(['git','-C',str(root/'.lake/packages'/dep),'rev-parse','HEAD'],text=True).strip()==rev,'provider pin '+dep)
    write(evidence/'provider-source-check.json',validate_provider_sources(root,plan))
    st=selected(plan);limits=st['limits'];roots=st['cache_roots']
    require(roots==sorted(set(roots)) and 'Mathlib' not in roots,'explicit normalized selective roots required')
    records=[];cache=Path(os.environ['MATHLIB_CACHE_DIR'])
    for i in range(0,len(roots),12):
        resident=sum(resources.usage(p/'.lake/build')['logical_bytes'] for p in (root/'.lake/packages').iterdir() if p.is_dir())
        resources.admission(root,evidence,'before_cache_chunk_'+str(i//12),remaining_output_bytes=limits['own_output_bytes']+limits['incoming_output_bytes'],temporary_bytes=max(0,limits['dependency_expanded_bytes']-resident)+limits['compressed_cache_bytes'])
        args=['lake','exe','cache','get',*roots[i:i+12]]
        start=time.time();log=evidence/('cache-chunk-'+str(i//12)+'.log')
        with log.open('wb') as f:
            p=subprocess.Popen(args,cwd=root,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            stop=None
            while p.poll() is None:
                if shutil.disk_usage(root).free<resources.DISK_FLOOR+resources.EVIDENCE_MARGIN:stop='DISK_RESERVE'
                elif resources.usage(cache)['logical_bytes']>limits['compressed_cache_bytes']:stop='COMPRESSED_SCOPE_CAP'
                if stop:
                    import signal
                    os.killpg(p.pid,signal.SIGTERM)
                    try:p.wait(timeout=20)
                    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
                    break
                time.sleep(2)
        records.append(dict(argv=args,exit_code=p.returncode,stop_reason=stop,elapsed_seconds=time.time()-start,log_sha256=sha(log)))
        write(evidence/'cache-get.json',dict(identity=ident,exit_code=p.returncode,requested_roots=roots,chunks=records,expanded_verified=False))
        require(p.returncode==0 and stop is None,'scoped cache chunk failed')
        expanded_now=sum(resources.usage(p/'.lake/build')['logical_bytes'] for p in (root/'.lake/packages').iterdir() if p.is_dir())
        require(expanded_now<=limits['dependency_expanded_bytes'],'expanded provider scope exceeds admitted bound')
        resources.snapshot(root,evidence,'after_cache_chunk_'+str(i//12))
    outputs=verify_expansion(root,plan)
    write(evidence/'cache-expanded.json',outputs)
    write(evidence/'cache-get.json',dict(identity=ident,exit_code=0,requested_roots=roots,chunks=records,empty_roots_skipped=not roots,expanded_verified=True,expanded_inventory_sha256=sha(evidence/'cache-expanded.json')))
    # An actual native import of all external roots precedes every Annex compile in the same run.
    probe=evidence/'ScopedImport.lean';probe.write_text(''.join('import '+n+'\n' for n in roots),encoding='utf-8')
    resources.compilation_admission(root,evidence,'before_scoped_native_import')
    env=dict(os.environ);env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
    import segmented_qualification as native
    old=os.environ.get('LEAN_PATH');os.environ['LEAN_PATH']=env['LEAN_PATH']
    try:command=native.guarded(['lean','-j','1','-M','4096',str(probe)],root,evidence/'scope-native-import.log',time.monotonic()+300)
    finally:
        if old is None:os.environ.pop('LEAN_PATH',None)
        else:os.environ['LEAN_PATH']=old
    write(evidence/'scope-native-import.json',dict(command=command,source_sha256=sha(probe)))
    native.command_success(command,'scoped native provider import')
def download(root,evidence,ident,plan,capture):
    st=selected(plan);names=[s['stage'] for s in plan['stages']];prev=names[:names.index(st['stage'])]
    repo=os.environ['GITHUB_REPOSITORY'];run=os.environ['GITHUB_RUN_ID'];attempt=os.environ['GITHUB_RUN_ATTEMPT']
    artifacts=[];page=1
    while True:
        data=json.loads(capture(['gh','api',f'repos/{repo}/actions/runs/{run}/artifacts?per_page=100&page={page}']))
        artifacts+=data['artifacts']
        if len(artifacts)>=data['total_count']:break
        require(data['artifacts'],'incomplete pagination');page+=1
    from datetime import datetime,timezone
    observations=[]
    def fetch(name,dest,expanded_cap):
        expected=f'gss-{name}-{run}-{attempt}';matches=[a for a in artifacts if a['name']==expected]
        require(len(matches)==1,'missing/duplicate artifact '+expected);a=matches[0]
        expiry=datetime.fromisoformat(a['expires_at'].replace('Z','+00:00')).timestamp();remaining=expiry-time.time()
        require(not a['expired'] and remaining>plan['job_timeout_minutes']*60,'expired/insufficient lifetime '+expected)
        require(str(a['workflow_run']['id'])==run and a['workflow_run']['head_sha']==ident['commit'],'artifact producer identity')
        require(a['size_in_bytes']<=expanded_cap,'artifact compressed cap')
        resources.admission(root,evidence,'before_download_'+name,remaining_output_bytes=st['limits']['own_output_bytes'],temporary_bytes=a['size_in_bytes']+expanded_cap)
        dest.mkdir(parents=True,exist_ok=True)
        capture(['gh','run','download',run,'--repo',repo,'--name',expected,'--dir',str(dest)])
        require(resources.usage(dest)['logical_bytes']<=expanded_cap,'expanded artifact cap')
        observations.append({k:a[k] for k in ('id','name','size_in_bytes','expires_at','expired')})
        write(evidence/'download-artifact-expiry.json',dict(identity=ident,artifacts=observations,unlimited_queue_guarantee=False))
    incoming=Path(os.environ['INCOMING_DIR']);explicit={}
    import build_checkpoint as checkpoint
    for name in prev:
        expected=f'gss-{name}-receipt-{run}-{attempt}'
        if any(a['name']==expected for a in artifacts):fetch(name+'-receipt',incoming/name,32*2**20)
        else:explicit[name]=checkpoint.prior_stage(root,evidence,plan,name,ident,incoming/name,capture)
    for b in plan['artifact_bundles']:
        if st['stage'] not in b['consumers']:continue
        producer=read(incoming/b['producer']/'stage.json')
        expected={n:producer['modules'][n]['outputs'] for n in b['modules']}
        bound=sum(r['bytes'] for rows in expected.values() for r in rows)+65536
        dest=incoming/'bundles'/b['id']
        if b['producer'] in explicit:
            p=explicit[b['producer']]
            checkpoint.fetch_artifact(root,evidence,repo,p,p['bundles'][b['id']],dest,bound,st['limits']['own_output_bytes'],capture)
        else:fetch(b['id'],dest,bound)
        actual={p.relative_to(dest).as_posix() for p in dest.rglob('*') if p.is_file()}
        require(actual=={r['path'] for rows in expected.values() for r in rows},'missing/excess bundle files')
        for rows in expected.values():
            for r in rows:
                p=dest/r['path'];require(p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'bundle bytes')
        resources.snapshot(root,evidence,'after_artifact_download_'+b['id'])
    require(resources.usage(incoming/'bundles')['logical_bytes']<=st['limits']['incoming_output_bytes'],'scope restore cap')
def move_incoming(root,evidence,stage,ident,plan,seen):
    expected=set(selected(plan)['required_prior_modules']);actual=set()
    incoming=Path(os.environ['INCOMING_DIR'])
    for b in plan['artifact_bundles']:
        if stage not in b['consumers']:continue
        folder=incoming/'bundles'/b['id']
        for n in b['modules']:
            require(n not in actual,'duplicate restoration');actual.add(n)
            for r in seen[n]['outputs']:
                resources.move_exact(folder/r['path'],root/r['path'],r,folder,root/'.lake/build/lib/lean')
    require(actual==expected,'dependency scope missing/excess')
    write(evidence/'consumed-chain.json',dict(identity=ident,metadata_modules=len(seen),restored_modules=sorted(actual),restore_mode='EXACT_CONSUMER_PARTITION_MOVE'))
    resources.snapshot(root,evidence,'after_artifact_restore')
def collect_bundles(root,payload,plan):
    import build_checkpoint as checkpoint
    rec=read(payload/'stage.json');out=payload.parent/'gss-bundles';present=[];unavailable={}
    for b in plan['artifact_bundles']:
        if b['producer']!=rec['stage']:continue
        members=[n for n in b['modules'] if n in rec.get('modules',{})]
        moved=[]
        for n in members:
            record=rec['modules'][n]
            try:
                require(record['exit_code']==0,'failed module cannot be collected')
                checkpoint.validate_outputs(root,n,record['outputs'])
                for r in record['outputs']:
                    resources.move_exact(root/r['path'],out/b['id']/r['path'],r,root/'.lake/build/lib/lean',out/b['id'])
                moved.append(n)
            except (ValueError,OSError,KeyError) as exc:unavailable[n]=str(exc)
        if moved:present.append(dict(id=b['id'],modules=moved))
    if unavailable:
        rec['unavailable_modules']=unavailable;rec['status']='FAIL'
        for n in unavailable:rec['modules'].pop(n,None)
        checkpoint.atomic_write(payload/'stage.json',rec)
    checkpoint.atomic_write(payload/'collected-bundles.json',dict(bundles=present,empty_planned_bundles_omitted=True,unavailable=unavailable,qualification='NOT_GRANTED'))


def upload_budget(root,evidence,payload,ident,plan):
    names=[s['stage'] for s in plan['stages']];stage=os.environ['STAGE_NAME'];prev=names[:names.index(stage)]
    cap=plan['artifact_budget']['cumulative_upper_bound_bytes']-reserve(plan);prior=0
    for name in prev:
        r=read(Path(os.environ['INCOMING_DIR'])/name/'upload-budget.json')
        require(r['status']=='PASS' and r['identity']==ident and r['prior_cumulative_bytes']==prior and r['budget_bytes']==cap,'prior budget binding')
        prior+=r['reserved_bytes'];require(prior==r['cumulative_reserved_bytes'],'prior budget sum')
    collected=read(payload/'collected-bundles.json')
    folders=[payload,payload.parent/'gss-job-evidence',*[payload.parent/'gss-bundles'/b['id'] for b in collected['bundles']]]
    bounds=[]
    for folder in folders:
        rows=[dict(path=p.relative_to(folder).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(folder.rglob('*')) if p.is_file()]
        require(rows and all(not (folder/r['path']).is_symlink() for r in rows),'empty/linked payload')
        bounds.append(dict(folder=folder.name,actual_bytes=sum(r['bytes'] for r in rows),reserved_bytes=resources.zip_bound(rows),inventory_sha256=scope.digest(rows)))
    require(sum(x['actual_bytes'] for x in bounds if x['folder'] not in ('gss-payload','gss-job-evidence'))<=selected(plan)['limits']['own_output_bytes'],'own stage output cap')
    reserved=sum(x['reserved_bytes'] for x in bounds)+65536
    # Saving completed evidence must remain possible after the native disk floor stopped compilation.
    # Reserve measured packaging peak plus the existing evidence margin; never start a compiler here.
    needed=max(x['reserved_bytes'] for x in bounds)+resources.EVIDENCE_MARGIN
    require(shutil.disk_usage(root).free>=needed,'INSUFFICIENT_CHECKPOINT_PACKAGING_SPACE')
    rec=dict(stage=stage,status='PASS' if prior+reserved<=cap else 'FAIL',identity=ident,budget_bytes=cap,prior_cumulative_bytes=prior,reserved_bytes=reserved,cumulative_reserved_bytes=prior+reserved,artifacts=bounds,retention_days=3,future_linux_sizes='NOT_PREDICTED_ACTUAL_UPLOAD_BOUNDS')
    write(payload/'upload-budget.json',rec);write(evidence/'upload-budget.json',rec)
    require(rec['status']=='PASS','ARTIFACT_STORAGE_BUDGET_EXCEEDED')
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'],'a',encoding='utf-8') as f:
            f.write('bundles='+json.dumps([b['id'] for b in collected['bundles']],separators=(',',':'))+'\n')
    return rec
def diagnostic(evidence,dest):
    from diagnostic_capture import collect
    dest.mkdir(parents=True,exist_ok=True)
    if not any(evidence.glob('*.command.json')) and (evidence.parent/'gss-job-evidence').is_dir():evidence=evidence.parent/'gss-job-evidence'
    value=collect(evidence,Path(os.environ['PAYLOAD_DIR']))
    write(dest/'diagnostic.json',value)
    require(resources.zip_bound([dict(bytes=(dest/'diagnostic.json').stat().st_size)],metadata=4096)<=131072,'diagnostic budget')


def catalog(root,evidence,ident,plan,stages,census):
    compiler=stages[0]['compiler_sha256'];keys=scope.module_keys(plan,compiler,'linux',platform.machine())
    records={n:r for stage in stages for n,r in stage['modules'].items()}
    producer=ident['commit']+':'+ident['run_id']+':'+ident['run_attempt'];out={}
    for n,r in records.items():
        declarations={k:v for k,v in census['records'].items() if v['module']==n}
        out[n]=dict(key=keys[n],qualification='PASS',platform='linux',machine=platform.machine(),compiler_sha256=compiler,producer=producer,type_axiom_census_sha256=scope.digest(declarations),outputs=r['outputs'],source_sha256=r['source_sha256'],local_dependencies=r['local_dependencies'],execution=r.get('execution','FRESH'))
    require(set(out)==set(plan['source_modules']),'catalog target coverage')
    counts={s:sum(r['execution']==s for r in out.values()) for s in ('FRESH','INHERITED','CHECKPOINT_RESTORED')}
    write(Path(os.environ['PAYLOAD_DIR'])/'qualification-catalog.json',dict(schema='annex.qualified-module-catalog.v1',identity=ident,modules=out,counts=counts,qualification_mode='QUALIFIED_DELTA' if counts['INHERITED'] else 'BOOTSTRAP_SCOPED_LINUX',cache_retention_days=3,permanent_evidence='Archive this catalog and qualification receipt privately before cache expiry; approval remains separate',producer_accepted=False))
