"""Manual private release-qualification helper. Import is inert.

This SEP integration candidate is unbuilt until its new exact-tree receipts exist.
The owner alone dispatches the hosted workflow; source, LFH and website publication
remain separate acts. Prior receipts are not receipts for this candidate.
"""
import hashlib, json, os, re, subprocess, sys
from pathlib import Path

SCHEMA='mathlibannex.github-release-qualification-receipt.v4'
CHECKS=('identity','build','downstream_import','project_entry_import','sphere_rigidity_entry_import','naimark_entry_import','pure_state_homogeneity_entry_import','rosenberg_entry_import','project_entry_parser','compiled_axiom_audit','cleanliness')
ALLOW=['propext','Classical.choice','Quot.sound']
def digest(data):return hashlib.sha256(data).hexdigest()
def write(path,value):path.write_text(json.dumps(value,sort_keys=True,indent=2)+'\n',encoding='utf-8')
def run(args):return subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
def require(ok,message):
    if not ok:raise ValueError(message)
def outcome(value):return {'SUCCESS':'PASS','FAILURE':'FAIL','success':'PASS','failure':'FAIL','cancelled':'CANCELLED','skipped':'NOT_RUN','':'NOT_RUN'}.get(value,'NOT_RUN')
def make_receipt(identity,results,logs,run_identity):
    require(set(results)==set(CHECKS),'separate required checks')
    require(all(x in ('PASS','FAIL','NOT_RUN','CANCELLED') for x in results.values()),'typed check result')
    passed=all(x=='PASS' for x in results.values())
    if passed:
        require(identity and identity.get('execution_mode',{}).get('mode') in ('LOCAL_INCREMENTAL','HOSTED_CLEAN_ANNEX'),'PASS requires explicit cache-mode binding')
    require(not passed or (identity and identity.get('status')=='PASS'),'success requires exact identity')
    return {'schema':SCHEMA,'qualification':'PASS' if passed else 'FAIL','checks':results,'identity':identity,
        'axiom_policy':{'root':'MathlibAnnex','allowlist':ALLOW},'run':run_identity,'logs':logs,
        'public_deployment':'NOT PERFORMED','owner_acceptance':False,'formal_public_admission':False,
        'source_exposition_review':'NOT PERFORMED','license_grant':False,
        'independent_checkers':{'leanchecker':'DEFERRED_P2_LB03_RESOURCE_PROFILE','nanoda':'DEFERRED_P2_LB03_RESOURCE_PROFILE'}}
def summary(receipt):
    rows=['# MathlibAnnex release qualification','', '| Check | Result |','|---|---|']
    labels={'identity':'Exact commit / tree / workflow / toolchain / Mathlib','build':'MathlibAnnex build','downstream_import':'Downstream root import','project_entry_import':'Mankiewicz Project-entry import','sphere_rigidity_entry_import':'Sphere Rigidity Project-entry import','naimark_entry_import':'Naimark Project-entry import','pure_state_homogeneity_entry_import':'Pure State Homogeneity Project-entry import','rosenberg_entry_import':'Rosenberg Project-entry import','project_entry_parser':'Pinned Lean parser / listed source-content binding','compiled_axiom_audit':'Compiled-axiom audit','cleanliness':'Tracked / staged / porcelain cleanliness'}
    rows += ['| '+labels[k]+' | '+receipt['checks'][k]+' |' for k in CHECKS]
    rows += ['| Qualification | '+receipt['qualification']+' |','| Machine receipt | qualification.json in the run artifact |','| Public deployment | NOT PERFORMED |', '',
        'A PASS covers only the listed checks on the exact identities below. Owner acceptance, source-exposition review, license grant and publication remain separate.','',
        'A missing, skipped or cancelled required check is not a PASS. Download the artifact and the GitHub job logs when diagnosing a failure.','',
        '```json',json.dumps(receipt['identity'],sort_keys=True,indent=2),'```','']
    return '\n'.join(rows)
def execution_mode(root, evidence, env):
    """Bind cache semantics, without removing, rewriting or copying cache files."""
    mode=env.get('QUALIFICATION_MODE','')
    require(mode in ('LOCAL_INCREMENTAL','HOSTED_CLEAN_ANNEX'), 'explicit qualification mode required')
    fresh=not (root/'.lake/build').exists()
    if mode=='HOSTED_CLEAN_ANNEX':
        require(env.get('GITHUB_ACTIONS')=='true' and env.get('RUNNER_ENVIRONMENT')=='github-hosted', 'fresh GitHub-hosted runner required')
        require(env.get('GITHUB_EVENT_NAME')=='workflow_dispatch', 'manual event required')
        require(fresh, 'root .lake/build already exists before hosted build')
        require(env.get('LAKE_NO_CACHE')=='true' and env.get('LAKE_ARTIFACT_CACHE')=='false', 'no implicit Annex artifact download')
        require(not env.get('LEAN_PATH') and not env.get('LEAN_GITHASH'), 'no imported workspace/search-path or trace-identity override')
        wf=json.loads((root/'.github/workflows/release-qualification.yml').read_text(encoding='utf-8'))
        action=next(s for s in wf['jobs']['qualify']['steps'] if s.get('id')=='lean')
        require(action['with']['use-github-cache'] is False and action['with']['use-mathlib-cache'] is True, 'Annex cache off, pinned Mathlib cache on')
    value={'schema':'mathlibannex.qualification-execution-mode.v1','mode':mode,
        'project_build_directory_absent_before':fresh,
        'project_cached_artifacts_permitted':mode=='LOCAL_INCREMENTAL',
        'pinned_dependency_cache_permitted':True,'fresh_full_mathlib_build_claim':False,
        'all_required_checks_still_required':True}
    write(evidence/'execution-mode.json',value)
    return value

def identity(root,evidence,env):
    def git(*args):
        cp=run(['git','-C',str(root),*args]);require(cp.returncode==0,'git identity');return cp.stdout.decode().strip()
    commit=git('rev-parse','HEAD');tree=git('rev-parse','HEAD^{tree}')
    workflow=root/'.github/workflows/release-qualification.yml'
    toolchain=(root/'lean-toolchain').read_text(encoding='utf-8').strip()
    lock=json.loads((root/'lake-manifest.json').read_text(encoding='utf-8'));mathlibs=[p for p in lock['packages'] if p['name']=='mathlib']
    require(len(mathlibs)==1,'one pinned Mathlib');mathlib=mathlibs[0]['rev']
    require(re.fullmatch('[0-9a-f]{40}',env['EXPECTED_COMMIT']) and commit==env['EXPECTED_COMMIT']==env['GITHUB_SHA']==env['WORKFLOW_SHA'],'exact selected workflow and source commit')
    require(re.fullmatch('[0-9a-f]{40}',env['EXPECTED_TREE']) and tree==env['EXPECTED_TREE'],'exact expected tree')
    require(toolchain==env['EXPECTED_TOOLCHAIN'] and re.fullmatch(r'leanprover/lean4:v[0-9.]+(?:-rc[0-9]+)?',toolchain),'pinned release toolchain')
    require(re.fullmatch('[0-9a-f]{40}',mathlib) and mathlib==env['EXPECTED_MATHLIB'],'pinned Mathlib revision')
    value={'status':'PASS','commit':commit,'tree':tree,'workflow_sha256':digest(workflow.read_bytes()),'workflow_commit':env['WORKFLOW_SHA'],
        'helper_sha256':digest(Path(__file__).read_bytes()),'lean_toolchain':toolchain,'mathlib_revision':mathlib,
        'lock_sha256':digest((root/'lake-manifest.json').read_bytes()),'toolchain_sha256':digest((root/'lean-toolchain').read_bytes())}
    value['execution_mode']=execution_mode(root,evidence,env)
    write(evidence/'identity.json',value);print(json.dumps(value,sort_keys=True));return value
def clean(root,evidence):
    results={}
    for name,args in [('tracked',['diff','--exit-code']),('staged',['diff','--cached','--exit-code']),('porcelain',['status','--porcelain=v1','--untracked-files=all'])]:
        cp=run(['git','-C',str(root),*args]);(evidence/(name+'.log')).write_bytes(cp.stdout)
        results[name]={'exit_code':cp.returncode,'output_sha256':digest(cp.stdout),'empty':not cp.stdout.strip()}
    tracked=run(['git','-C',str(root),'ls-files','-z','*.lean']);require(tracked.returncode==0,'list governed Lean blobs')
    lf_rows=[]
    for raw_path in tracked.stdout.split(b'\0'):
        if not raw_path:continue
        path=raw_path.decode('utf-8')
        attrs=run(['git','-C',str(root),'check-attr','--cached','text','eol','--',path])
        require(attrs.returncode==0 and f'{path}: text: set'.encode() in attrs.stdout and f'{path}: eol: lf'.encode() in attrs.stdout,'LF attributes missing: '+path)
        blob=run(['git','-C',str(root),'show','HEAD:'+path]);require(blob.returncode==0 and b'\r\n' not in blob.stdout,'CRLF in LF-governed blob: '+path)
        lf_rows.append({'path':path,'bytes':len(blob.stdout),'sha256':digest(blob.stdout)})
    require(bool(lf_rows),'no governed Lean blobs')
    write(evidence/'blob-lf-policy.json',{'schema':'mathlibannex.blob-lf-policy.v1','status':'PASS','files':lf_rows})
    write(evidence/'cleanliness.json',results)
    require(all(r['exit_code']==0 and r['empty'] for r in results.values()),'tracked, index or porcelain dirty')
def finish(evidence,env):
    identity_value=json.loads((evidence/'identity.json').read_text(encoding='utf-8')) if (evidence/'identity.json').exists() else None
    results={'identity':outcome(env.get('IDENTITY_OUTCOME','')),'build':outcome(env.get('BUILD_STATUS','')),
        'downstream_import':outcome(env.get('IMPORT_OUTCOME','')),'project_entry_import':outcome(env.get('PROJECT_IMPORT_OUTCOME','')),'sphere_rigidity_entry_import':outcome(env.get('SPHERE_PROJECT_IMPORT_OUTCOME','')),'naimark_entry_import':outcome(env.get('NAIMARK_PROJECT_IMPORT_OUTCOME','')),'pure_state_homogeneity_entry_import':outcome(env.get('PURE_STATE_HOMOGENEITY_PROJECT_IMPORT_OUTCOME','')),'rosenberg_entry_import':outcome(env.get('ROSENBERG_PROJECT_IMPORT_OUTCOME','')),'project_entry_parser':outcome(env.get('PROJECT_ENTRY_PARSER_OUTCOME','')),'compiled_axiom_audit':outcome(env.get('AXIOM_STATUS','')),'cleanliness':outcome(env.get('CLEAN_OUTCOME',''))}
    logs=[{'path':p.name,'bytes':p.stat().st_size,'sha256':digest(p.read_bytes())} for p in sorted(evidence.glob('*')) if p.is_file() and p.name not in ('qualification.json','summary.md')]
    receipt=make_receipt(identity_value,results,logs,{'repository':env.get('GITHUB_REPOSITORY',''),'id':env.get('GITHUB_RUN_ID',''),'attempt':env.get('GITHUB_RUN_ATTEMPT','')})
    write(evidence/'qualification.json',receipt);text=summary(receipt);(evidence/'summary.md').write_text(text,encoding='utf-8')
    with open(env['GITHUB_STEP_SUMMARY'],'a',encoding='utf-8') as f:f.write(text)
    return receipt
def main():
    stage=sys.argv[1];root=Path.cwd();env=os.environ;evidence=Path(env['QUALIFICATION_DIR']);evidence.mkdir(parents=True,exist_ok=True)
    if stage=='identity':identity(root,evidence,env)
    elif stage=='import':
        cp=run(['lake','env','lean','examples/Import.lean']);(evidence/'downstream-import.log').write_bytes(cp.stdout);print(cp.stdout.decode(errors='replace'));return cp.returncode
    elif stage=='project-import':
        cp=run(['lake','env','lean','examples/ImportMankiewicz.lean']);(evidence/'project-entry-import.log').write_bytes(cp.stdout);print(cp.stdout.decode(errors='replace'));return cp.returncode
    elif stage=='sphere-project-import':
        cp=run(['lake','env','lean','examples/ImportSphereRigidity.lean']);(evidence/'sphere-rigidity-entry-import.log').write_bytes(cp.stdout);print(cp.stdout.decode(errors='replace'));return cp.returncode
    elif stage in ('naimark-project-import','pure-state-homogeneity-project-import','rosenberg-project-import'):
        filenames={'naimark-project-import':'ImportNaimark','pure-state-homogeneity-project-import':'ImportPureStateHomogeneity','rosenberg-project-import':'ImportRosenberg'}
        probes=['examples/'+filenames[stage]+'.lean']
        if stage=='naimark-project-import':
            probes+=['examples/SeparableFaithfulSmoke.lean','scripts/PrintSeparableFaithfulAxioms.lean']
        rows=[]
        for j,probe in enumerate(probes):
            cp=run(['lake','env','lean',probe])
            log=stage+('.log' if j==0 else '-'+Path(probe).stem+'.log')
            (evidence/log).write_bytes(cp.stdout);print(cp.stdout.decode(errors='replace'))
            rows.append({'source':probe,'source_sha256':digest((root/probe).read_bytes()),'exit_code':cp.returncode,'log':log,'log_sha256':digest(cp.stdout)})
            if cp.returncode:
                write(evidence/(stage+'-probes.json'),{'status':'FAIL','probes':rows})
                return cp.returncode
        write(evidence/(stage+'-probes.json'),{'status':'PASS','probes':rows})
        return 0
    elif stage=='entry-parser':
        names=['Mankiewicz','SphereRigidity','Naimark','PureStateHomogeneity','Rosenberg']
        paths=['MathlibAnnex/Projects/'+n+'.lean' for n in names]
        cp=run(['lake','env','lean','--run','scripts/ProjectEntryParser.lean',*paths]);(evidence/'project-entry-parser.log').write_bytes(cp.stdout)
        require(cp.returncode==0,'entry parser command failed')
        rows=json.loads(cp.stdout.decode());require(len(rows)==len(paths),'parser output cardinality')
        slugs=['mankiewicz','sphere-rigidity','naimark','pure-state-homogeneity','rosenberg']
        verified=[]
        for path,slug,row in zip(paths,slugs,rows):
            require(row['file']==path and row['header_only'] is True and row['imports_comments_only'] is True and row['finished'] is True and row['diagnostics']==[],'invalid Project facade '+path)
            manifest=json.loads((root/'docs/projects'/ (slug+'.json')).read_text(encoding='utf-8'))
            require(row['imports']==manifest['direct_project_modules'],'entry/manifest direct root mismatch '+slug)
            entry=manifest['entry_module'];require(entry['path']==path and entry['sha256']==digest((root/path).read_bytes()) and entry['bytes']==(root/path).stat().st_size,'entry bytes mismatch '+slug)
            for provider in manifest['resolved_mathlibannex_import_closure']:
                p=root/provider['path'];require(p.is_file() and digest(p.read_bytes())==provider['sha256'] and p.stat().st_size==provider['bytes'],'closure content mismatch '+provider['path'])
            # Full compiled/source closure and role accounting is a separate local admission gate.
            verified.append({'path':path,'manifest_sha256':digest((root/'docs/projects'/(slug+'.json')).read_bytes()),'parser':row})
        write(evidence/'project-entry-parser.json',{'status':'PASS','entries':verified,'parser_sha256':digest((root/'scripts/ProjectEntryParser.lean').read_bytes())})
    elif stage=='clean':clean(root,evidence)
    elif stage=='summary':finish(evidence,env)
    elif stage=='require':require(json.loads((evidence/'qualification.json').read_text(encoding='utf-8'))['qualification']=='PASS','one or more required checks failed or did not run')
    else:raise ValueError('unknown stage')
    return 0
if __name__=='__main__':raise SystemExit(main())
