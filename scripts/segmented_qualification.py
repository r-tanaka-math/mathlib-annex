"""Exact dependency-scoped Linux qualification with explicit accepted module reuse."""
from __future__ import annotations
import hashlib, json, os, re, shutil, signal, subprocess, sys, time, zipfile
from pathlib import Path
import hosted_resources as resources
import scoped_runtime as scoped
import dependency_scope as dependency
import platform
import native_process
import qualified_reuse
import build_checkpoint as checkpoint

ALLOW={'propext','Classical.choice','Quot.sound'}
BASE_CHECKS=('identity','build','downstream_import','project_entry_import','sphere_rigidity_entry_import','naimark_entry_import','pure_state_homogeneity_entry_import','rosenberg_entry_import','project_entry_parser','compiled_axiom_audit','cleanliness')
CHECKS=BASE_CHECKS+('gss_project_entry_import','gss_public_census','complete_source_coverage')
def require(x,message):
    if not x:raise ValueError(message)
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':'))+'\n'
def write(p,x):checkpoint.atomic_write(p,x)
def capture(args,cwd=None):
    cp=subprocess.run(args,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    require(cp.returncode==0,cp.stdout.decode(errors='replace')[-3000:]);return cp.stdout.decode().strip()
def identity(root,env):
    require(env.get('GITHUB_ACTIONS')=='true' and env.get('RUNNER_ENVIRONMENT')=='github-hosted' and sys.platform=='linux','fresh GitHub-hosted Linux runner required')
    require(env.get('GITHUB_EVENT_NAME')=='workflow_dispatch' and env.get('GITHUB_REPOSITORY_ID')=='1367564442','exact private manual repository required')
    require(env.get('REPOSITORY_PRIVATE')=='true','private repository required')
    require(env.get('LAKE_NO_CACHE')=='true' and env.get('LAKE_ARTIFACT_CACHE')=='false','implicit Annex cache forbidden')
    require(not env.get('LEAN_PATH') and not env.get('LEAN_GITHASH'),'no foreign Lean path or trace override')
    commit=capture(['git','rev-parse','HEAD']);tree=capture(['git','rev-parse','HEAD^{tree}'])
    require(commit==env['EXPECTED_COMMIT']==env['GITHUB_SHA']==env['WORKFLOW_SHA'] and re.fullmatch('[0-9a-f]{40}',commit),'exact source/workflow commit')
    require(tree==env['EXPECTED_TREE'] and re.fullmatch('[0-9a-f]{40}',tree),'exact tree')
    plan=json.loads((root/'docs/qualification/segmented-plan.json').read_text())
    require((root/'lean-toolchain').read_text().strip()==plan['lean_toolchain']==env['EXPECTED_TOOLCHAIN'],'toolchain pin')
    lock=json.loads((root/'lake-manifest.json').read_text());pins={p['name']:p['rev'] for p in lock['packages']}
    require(pins==plan['locked_dependencies'] and pins['mathlib']==env['EXPECTED_MATHLIB'],'all nine dependency pins')
    for row in plan['source_modules'].values():require(sha(root/row['path'])==row['sha256'] and (root/row['path']).stat().st_size==row['bytes'],'source inventory')
    return dict(commit=commit,tree=tree,workflow_sha256=sha(root/'.github/workflows/release-qualification.yml'),helper_sha256=sha(Path(__file__)),resource_helper_sha256=sha(root/'scripts/hosted_resources.py'),plan_sha256=sha(root/'docs/qualification/segmented-plan.json'),lock_sha256=sha(root/'lake-manifest.json'),toolchain=plan['lean_toolchain'],dependency_pins=pins,mode=('QUALIFIED_DELTA' if json.loads((root/plan['reuse_policy']['registry']).read_text())['modules'] else 'BOOTSTRAP_SCOPED_LINUX'),scope_helper_sha256=sha(root/'scripts/scoped_runtime.py'),dependency_helper_sha256=sha(root/'scripts/dependency_scope.py'),native_process_helper_sha256=sha(root/'scripts/native_process.py'),provider_graph_sha256=sha(root/'docs/qualification/provider-graph.json'),run_id=env['GITHUB_RUN_ID'],run_attempt=env['GITHUB_RUN_ATTEMPT'])
def check_chain(receipts,expected_stages,ident,plan):
    require([r['stage'] for r in receipts]==expected_stages,'missing, duplicate or out-of-order stages')
    seen={};compiler=None
    for r in receipts:
        require(r['status']=='PASS' and r['identity']==ident,'failed stage or wrong identity')
        require(r['platform']=='linux','foreign compiled artifacts')
        compiler=compiler or r['compiler_sha256'];require(r['compiler_sha256']==compiler,'different compiler binary')
        require(r['machine']==platform.machine(),'foreign machine architecture')
        keys=dependency.module_keys(plan,compiler,'linux',r['machine'])
        expected=next(s['modules'] for s in plan['stages'] if s['stage']==r['stage'])
        require(set(r['modules'])==set(expected),'stage module coverage')
        for n in expected:
            rec=r['modules'][n]
            require(rec['qualification_key']==keys[n] and rec['execution'] in ('FRESH','INHERITED','CHECKPOINT_RESTORED'),'module qualification key or execution mode')
            require(n not in seen and rec['exit_code']==0 and rec['source_sha256']==plan['source_modules'][n]['sha256'],'duplicate, failure or source drift')
            main=n.replace('.','/')+'.olean'
            require(any(x['path']=='.lake/build/lib/lean/'+main and x['sha256']==rec['output_sha256'] for x in rec['outputs']),'output digest not bound to artifact')
            for d in plan['dependency_edges'][n]:require(d in seen and rec['local_dependencies'].get(d)==seen[d]['output_sha256'],'dependency provenance')
            seen[n]=rec
    return seen
def load_incoming(root,evidence,stage,ident,plan,compiler):
    names=[s['stage'] for s in plan['stages']];prev=names[:names.index(stage)]
    receipts=[]
    for name in prev:
        incoming=Path(os.environ['INCOMING_DIR'])/name
        r=json.loads((incoming/'stage.json').read_text())
        require(r['compiler_sha256']==compiler,'incoming compiler binary differs from current compiler')
        receipts.append(r)
    seen=check_chain(receipts,prev,ident,plan)
    scoped.move_incoming(root,evidence,stage,ident,plan,seen)
    return seen
def guarded(args,root,log,deadline):
    start=time.monotonic();samples=[];stop=None
    log.parent.mkdir(parents=True,exist_ok=True)
    try:
        resources.compilation_admission(root,log.parent,'before_compiler_spawn')
        memory_gate=native_process.memory_admission(args)
        write(log.with_suffix('.memory-admission.json'),memory_gate)
        if memory_gate['status']=='BLOCKED':
            raise resources.ResourceBlocked(dict(status='ENVIRONMENT_RESOURCE_BLOCKED',reason=memory_gate['reason'],memory_gate=memory_gate))
        if time.monotonic()>deadline:raise resources.ResourceBlocked(dict(status='ENVIRONMENT_RESOURCE_BLOCKED',reason='SOFT_STAGE_TIMEOUT_BEFORE_SPAWN'))
    except resources.ResourceBlocked as exc:
        log.write_bytes(b'')
        return dict(argv=args,exit_code=None,elapsed_seconds=time.monotonic()-start,log=log.name,log_sha256=sha(log),resource_samples=[],stop_reason='ENVIRONMENT_RESOURCE_BLOCKED',spawned=False,resource_failure=exc.record)
    launch_args=native_process.launch_arguments(args,log.with_suffix('.child-policy.json'))
    with log.open('wb') as f:
        p=subprocess.Popen(launch_args,cwd=root,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            free=shutil.disk_usage(root).free;sample=dict(elapsed=time.monotonic()-start,pid=p.pid,free_bytes=free)
            stat=Path('/proc')/str(p.pid)/'status'
            if stat.exists():
                for line in stat.read_text().splitlines():
                    if line.split(':')[0] in ('VmRSS','VmHWM','VmSize','Threads'):sample[line.split(':')[0]]=line.split(':',1)[1].strip()
            members=[]
            for proc in (Path('/proc').iterdir() if Path('/proc').is_dir() else []):
                if not proc.name.isdecimal():continue
                try:
                    fields=(proc/'stat').read_text().rsplit(')',1)[1].split()
                    if int(fields[2])!=p.pid:continue
                    data=dict(pid=int(proc.name))
                    for line in (proc/'status').read_text().splitlines():
                        if line.split(':')[0] in ('VmRSS','Threads'):data[line.split(':')[0]]=line.split(':',1)[1].strip()
                    members.append(data)
                except (OSError,ValueError,IndexError):pass
            sample['owned_process_group']=members
            sample['group_rss_bytes']=sum(int(x.get('VmRSS','0 kB').split()[0])*1024 for x in members)
            sample['host_memory']=native_process.memory_snapshot()
            samples.append(sample)
            if time.monotonic()>deadline:stop='SOFT_STAGE_TIMEOUT'
            elif free<4*2**30:stop='DISK_RESERVE'
            elif sample['group_rss_bytes']>6*2**30:stop='RSS_RESERVE'
            elif sample['host_memory'].get('MemAvailable_bytes',2**63)<512*2**20:stop='HOST_MEMORY_RESERVE'
            if stop:
                p.terminate() if os.name=='nt' else os.killpg(p.pid,signal.SIGTERM)
                try:p.wait(timeout=20)
                except subprocess.TimeoutExpired:p.kill() if os.name=='nt' else os.killpg(p.pid,signal.SIGKILL);p.wait()
                break
            time.sleep(1)
    return dict(argv=args,exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,log=log.name,log_sha256=sha(log),resource_samples=samples,stop_reason=stop,spawned=True,launch_argv=launch_args,diagnosis=native_process.tail_diagnosis(log,p.returncode,stop))
def command_success(command,label):
    if command.get('diagnosis',{}).get('kind')=='LEAN_MEMORY_LIMIT_EXCEEDED':
        raise resources.ResourceBlocked(dict(status='ENVIRONMENT_RESOURCE_BLOCKED',reason='LEAN_MEMORY_LIMIT_EXCEEDED',target=label,monitor_stop_reason=command['stop_reason'],exit_code=command['exit_code'],log_sha256=command['log_sha256']))
    if command['stop_reason']:
        raise resources.ResourceBlocked(dict(status='ENVIRONMENT_RESOURCE_BLOCKED',reason=command['stop_reason'],target=label,command=command))
    require(command['exit_code']==0,'native compiler failure '+label)

def share_evidence(evidence,dest):
    dest.mkdir(parents=True,exist_ok=True)
    sources=[p for p in evidence.rglob('*') if p.is_file()]
    for source in sorted(sources):
        require(not source.is_symlink(),'evidence symlink')
        if not source.is_file():continue
        target=dest/source.relative_to(evidence)
        require(not target.exists(),'collect must run once; evidence already copied')
        resources.move_exact(source,target,dict(bytes=source.stat().st_size,sha256=sha(source)),evidence,dest)

def move_completed_outputs(root,payload):
    scoped.collect_bundles(root,payload,json.loads((root/'docs/qualification/segmented-plan.json').read_text()))

def compile_module(root,evidence,n,plan,key,dependencies,binary,deadline):
    out=root/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
    root_arg,source_arg=checkpoint.source_arguments(root,plan['source_modules'][n]['path'])
    args=[str(binary),*dependency.flags(n),'-R',root_arg, '-o',str(out),source_arg]
    command=guarded(args,root,evidence/(n+'.log'),deadline)
    receipt=evidence/(n+'.command.json');write(receipt,command)
    command_success(command,n)
    return checkpoint.record_success(root,n,plan,key,dependencies,command,receipt)

def stage(root,evidence,payload,name):
    env=os.environ;ident=identity(root,env);plan=json.loads((root/'docs/qualification/segmented-plan.json').read_text())
    require(not list((root/'.lake/build/lib/lean').rglob('*.olean')),'fresh checkout must have no Annex compiled outputs')
    evidence.mkdir(parents=True,exist_ok=True);payload.mkdir(parents=True,exist_ok=True)
    write(evidence/'identity.json',ident)
    resources.compilation_admission(root,evidence,'before_compiler_version')
    binary=Path(capture(['elan','which','lean']));compiler=sha(binary)
    version=capture([str(binary),'--version']);require('4.32.0-rc1' in version and 'b4812ae53eea93439ad5dce5a5c26591c31cb697' in version,'native compiler pin')
    for dep,rev in plan['locked_dependencies'].items():require(capture(['git','-C',str(root/'.lake/packages'/dep),'rev-parse','HEAD'])==rev,'dependency checkout '+dep)
    rec=dict(stage=name,status='FAIL',identity=ident,platform=sys.platform,machine=platform.machine(),compiler_sha256=compiler,compiler_version=version,modules={})
    keys=dependency.module_keys(plan,compiler,'linux',platform.machine())
    write(payload/'stage.json',rec)
    try:
        prior=load_incoming(root,evidence,name,ident,plan,compiler)
        decisions,accepted,reuse_cache=qualified_reuse.prepare(root,evidence,plan,keys,capture)
        os.environ['LEAN_PATH']=capture(['lake','env','printenv','LEAN_PATH'])
        begun=json.loads((evidence/'job-start.json').read_text())['time']
        deadline=time.monotonic()+max(0,plan['soft_timeout_seconds']-(time.time()-begun))
        selected=next(s['modules'] for s in plan['stages'] if s['stage']==name)
        checkpoint_decisions,checkpoint_records,checkpoint_cache=checkpoint.prepare(root,evidence,plan,keys,compiler,sys.platform,platform.machine(),selected,capture)
        for n in selected:
            row=plan['source_modules'][n];out=root/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
            require(all(d in prior for d in plan['dependency_edges'][n]),'missing compiler dependency '+n)
            dependencies={d:prior[d]['output_sha256'] for d in plan['dependency_edges'][n]}
            if decisions[n]=='INHERITED' and accepted[n]['local_dependencies']==dependencies:
                value=qualified_reuse.inherit(n,accepted,reuse_cache,root,dependencies)
                rec['modules'][n]=value;prior[n]=value;write(payload/'stage.json',rec)
                continue
            if n in checkpoint_records:
                value=checkpoint.restore_expected(root,checkpoint_cache,n,checkpoint_records[n],dependencies,checkpoint_decisions[n])
            else:
                value=compile_module(root,evidence,n,plan,keys[n],dependencies,binary,deadline)
                value['reuse_decision']=decisions[n]
                value['checkpoint_decision']=checkpoint_decisions[n] if checkpoint_decisions[n]!='AVAILABLE_BUILD_CHECKPOINT' else 'INVALIDATED_DEPENDENCY_OUTPUT'
            rec['modules'][n]=value;prior[n]=value;write(payload/'stage.json',rec)
        rec['status']='PASS'
    except Exception as exc:
        rec['failure']=str(exc)
        rec['failure_kind']='NATIVE_OR_OUTPUT_VALIDATION_FAILURE'
        if isinstance(exc,resources.ResourceBlocked):rec['resource_failure']=exc.record;rec['failure_kind']='ENVIRONMENT_RESOURCE_BLOCKED'
        raise
    finally:
        write(payload/'stage.json',rec)
def validate_census(log,plan):
    modules=[];rows={};summary=[];token=0
    for line in log.open(encoding='utf-8'):
        line=line.rstrip('\r\n')
        if line.startswith('MODULE\t'):modules.append(line.split('\t')[1])
        elif line.startswith('DECL\t'):
            p=line.split('\t',10);require(len(p)==11,'census format');_,n,m,kind,levels,inst,simp,axs,td,vd,typ=p
            require(n not in rows and kind!='axiom' and set(filter(None,axs.split(',')))<=ALLOW,'forbidden axiom or duplicate')
            require(json.loads(typ).strip(),'empty type');rows[n]=dict(module=m,kind=kind,type=json.loads(typ),universes=levels,axioms=axs,instance=inst,simp=simp,type_dependencies=td,value_dependencies=vd)
        elif line.startswith('SUMMARY\t'):summary.append(int(line.split('\t')[1]))
        elif line=='PASS_ANNEX_MODULE_ORIGIN_AXIOMS':token+=1
        elif 'error:' in line or 'sorryAx' in line:raise ValueError('census compiler error')
    wanted=Path('docs/qualification/all-library-modules.txt').read_text().splitlines()
    require(modules==wanted and summary==[len(rows)] and token==1 and rows,'census incomplete')
    expected=json.loads(Path('docs/qualification/gss-public-declarations.json').read_text())
    require(len(expected)==3252 and len({x['name'] for x in expected})==3252,'public scope')
    for e in expected:require(e['name'] in rows and rows[e['name']]['module']==e['module'],'missing/wrong-origin public declaration '+e['name'])
    return dict(status='PASS',modules=len(wanted),public_gss_names=3252,records=rows,log_sha256=sha(log))
def final_checks(root,evidence):
    import release_qualification as baseline
    results={k:'NOT_RUN' for k in CHECKS};ident=identity(root,os.environ);results['identity']='PASS'
    def checkpoint():write(evidence/'checks-progress.json',dict(checks=results,identity=ident))
    checkpoint()
    plan=json.loads((root/'docs/qualification/segmented-plan.json').read_text())
    names=[s['stage'] for s in plan['stages']]
    rs=[json.loads((Path(os.environ['INCOMING_DIR'])/n/'stage.json').read_text()) for n in names[:-1]]
    rs.append(json.loads((Path(os.environ['PAYLOAD_DIR'])/'stage.json').read_text()))
    seen=check_chain(rs,names,ident,plan);require(set(seen)==set(plan['source_modules']),'full source coverage')
    results['build']=results['complete_source_coverage']='PASS'
    checkpoint()
    os.environ['QUALIFICATION_DIR']=str(evidence)
    calls=[('import','downstream_import'),('project-import','project_entry_import'),('sphere-project-import','sphere_rigidity_entry_import'),('naimark-project-import','naimark_entry_import'),('pure-state-homogeneity-project-import','pure_state_homogeneity_entry_import'),('rosenberg-project-import','rosenberg_entry_import')]
    begun=json.loads((evidence/'job-start.json').read_text())['time']
    deadline=time.monotonic()+max(0,plan['soft_timeout_seconds']-(time.time()-begun))
    for command,check in calls:
        c=guarded([sys.executable,'-B','scripts/release_qualification.py',command],root,evidence/(check+'.driver.log'),deadline)
        write(evidence/(check+'.command.json'),c);command_success(c,check);results[check]='PASS';checkpoint()
    c=guarded(['lake','env','lean','-j','1','-M','4096','examples/ImportGeometricStructureSpaces.lean'],root,evidence/'gss-independent-import.log',deadline);write(evidence/'gss-independent-import.command.json',c);command_success(c,'GSS independent import');results['gss_project_entry_import']='PASS'
    checkpoint()
    paths=[plan['source_modules'][n]['path'] for n in plan['project_entries']]
    c=guarded(['lake','env','lean','-j','1','-M','4096','--run','scripts/ProjectEntryParser.lean',*paths],root,evidence/'project-entry-parser.log',deadline)
    write(evidence/'project-entry-parser.command.json',c);command_success(c,'Project entry parser');raw=(evidence/'project-entry-parser.log').read_text()
    parsed=json.loads(raw);require(len(parsed)==6,'six pinned parser results')
    manifests={j['entry_module']['path']:j for p in (root/'docs/projects').glob('*.json') if (j:=json.loads(p.read_text())).get('record_type')=='MATHLIBANNEX_PROJECT_SOURCE_MANIFEST'}
    for path,row in zip(paths,parsed):
        require(row['file']==path and row['header_only'] and row['imports_comments_only'] and row['finished'] and not row['diagnostics'],'Project facade syntax')
        m=manifests[path];require(row['imports']==m['direct_project_modules'] and sha(root/path)==m['entry_module']['sha256'],'Project manifest binding')
        for source in m['resolved_mathlibannex_import_closure']:require(sha(root/source['path'])==source['sha256'],'Project closure bytes')
    write(evidence/'project-entry-parser.json',dict(status='PASS',entries=parsed));results['project_entry_parser']='PASS'
    checkpoint()
    os.environ['CENSUS_OUTPUT']=str(evidence/'whole-root-census.rows.tsv')
    c=guarded(['lake','env','lean','-j','1','-M','4096','scripts/AnnexModuleCensus.lean'],root,evidence/'whole-root-census.log',deadline);write(evidence/'whole-root-census.command.json',c);command_success(c,'compiled census')
    census=validate_census(evidence/'whole-root-census.rows.tsv',plan);write(evidence/'whole-root-census.json',census);results['compiled_axiom_audit']=results['gss_public_census']='PASS'
    checkpoint()
    baseline.clean(root,evidence);results['cleanliness']='PASS'
    receipt=dict(schema='mathlibannex.github-release-qualification-receipt.v6-scoped',qualification='PASS' if all(v=='PASS' for v in results.values()) else 'FAIL',checks=results,identity=ident,stages=[dict(stage=r['stage'],status=r['status'],modules=len(r['modules'])) for r in rs],axiom_policy=dict(root='MathlibAnnex',allowlist=sorted(ALLOW)),public_deployment='NOT_PERFORMED',owner_acceptance=False,formal_public_admission=False,independent_clean_single_runner='NOT_RUN',source_exposition_review='NOT_RUN')
    receipt['module_execution_counts']={k:sum(v['execution']==k for stage in rs for v in stage['modules'].values()) for k in ('FRESH','INHERITED','CHECKPOINT_RESTORED')}
    receipt['execution_mode']='QUALIFIED_DELTA' if receipt['module_execution_counts']['INHERITED'] else ('CHECKPOINT_ASSISTED_BOOTSTRAP' if receipt['module_execution_counts']['CHECKPOINT_RESTORED'] else 'BOOTSTRAP_SCOPED_LINUX')
    write(evidence/'qualification.json',receipt)
    write(Path(os.environ['PAYLOAD_DIR'])/'qualification.json',receipt)
    scoped.catalog(root,evidence,ident,plan,rs,census)

def upload_budget(root,evidence,payload):
    return scoped.upload_budget(root,evidence,payload,identity(root,os.environ),json.loads((root/'docs/qualification/segmented-plan.json').read_text()))
def download_prior(root,evidence):
    return scoped.download(root,evidence,identity(root,os.environ),json.loads((root/'docs/qualification/segmented-plan.json').read_text()),capture)

def main():
    root=Path.cwd();evidence=Path(os.environ['QUALIFICATION_DIR']);payload=Path(os.environ['PAYLOAD_DIR'])
    action=sys.argv[1]
    if action=='identity':
        require(not (root/'.lake/build').exists(),'fresh initial checkout');write(evidence/'job-start.json',dict(time=time.time()));write(evidence/'identity-before-setup.json',identity(root,os.environ))
    elif action=='diagnostic':scoped.diagnostic(evidence,Path(os.environ['RUNNER_TEMP'])/'gss-diagnostic')
    elif action=='capacity':resources.snapshot(root,evidence,sys.argv[2])
    elif action=='setup-admission':resources.admission(root,evidence,'before_setup')
    elif action=='cache-get':scoped.cache_get(root,evidence,identity(root,os.environ),json.loads((root/'docs/qualification/segmented-plan.json').read_text()))
    elif action=='cleanup-compressed':resources.cleanup_archives(root,evidence,identity(root,os.environ))
    elif action=='native-admission':resources.compilation_admission(root,evidence,'after_cache_before_download_and_native')
    elif action=='failure-report':
        resources.failure_report(root,evidence,payload,identity(root,os.environ),json.loads(os.environ['NEEDS_JSON']),CHECKS)
    elif action=='upload-guard':upload_budget(root,evidence,payload)
    elif action=='download-prior':download_prior(root,evidence)
    elif action=='stage':stage(root,evidence,payload,sys.argv[2])
    elif action=='final':
        try:final_checks(root,evidence)
        except Exception as exc:
            progress=json.loads((evidence/'checks-progress.json').read_text()) if (evidence/'checks-progress.json').exists() else dict(checks={k:'NOT_RUN' for k in CHECKS})
            write(evidence/'qualification.json',dict(schema='mathlibannex.github-release-qualification-receipt.v6-scoped',qualification='FAIL',failure=str(exc),checks=progress['checks'],identity=progress.get('identity'),public_deployment='NOT_PERFORMED'));raise
    elif action=='collect':
        try:resources.snapshot(root,evidence,'before_collect')
        except Exception as exc:write(evidence/'capacity-observation-failure.json',dict(error=str(exc),success_evidence=False))
        payload.mkdir(parents=True,exist_ok=True)
        evidence.mkdir(parents=True,exist_ok=True)
        outcomes={k:os.environ.get(k,'') for k in ('IDENTITY_OUTCOME','SETUP_OUTCOME','CACHE_OUTCOME','RESOURCE_OUTCOME','DOWNLOAD_OUTCOME','COMPILE_OUTCOME','FINAL_CHECKS_OUTCOME')}
        write(evidence/'actual-step-outcomes.json',outcomes)
        if not (payload/'stage.json').exists():
            write(payload/'stage.json',dict(stage=os.environ['STAGE_NAME'],status='FAIL',identity=None,modules={},failure='Native stage did not produce a successful receipt',actual_step_outcomes=outcomes))
        if os.environ['STAGE_NAME']=='final' and not (evidence/'qualification.json').exists():
            progress=json.loads((evidence/'checks-progress.json').read_text()) if (evidence/'checks-progress.json').exists() else dict(checks={k:'NOT_RUN' for k in CHECKS})
            write(evidence/'qualification.json',dict(schema='mathlibannex.github-release-qualification-receipt.v6-scoped',qualification='FAIL',failure='Final check skipped, interrupted or not run',checks=progress['checks'],identity=progress.get('identity'),actual_step_outcomes=outcomes,public_deployment='NOT_PERFORMED'))
        move_completed_outputs(root,payload)
        if evidence.exists():
            dest=payload.parent/'gss-job-evidence'
            share_evidence(evidence,dest)
    elif action=='require':require(json.loads((payload/'qualification.json').read_text())['qualification']=='PASS' and os.environ.get('UPLOAD_OUTCOME')=='success','qualification or artifact delivery failed')
    elif action=='require-stage':require(json.loads((payload/'stage.json').read_text())['status']=='PASS' and os.environ.get('UPLOAD_OUTCOME')=='success','stage or artifact delivery failed')
    else:raise ValueError('unknown action')
if __name__=='__main__':main()
