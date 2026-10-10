"""Bounded resource accounting for disposable GitHub runners; no local cache cleanup."""
from __future__ import annotations
import hashlib, json, os, re, shutil, stat, sys, time
from pathlib import Path

DISK_FLOOR=4*2**30
REPORT_CAP=2**20
EVIDENCE_MARGIN=64*2**20

class ResourceBlocked(RuntimeError):
    def __init__(self, record):
        self.record=record
        super().__init__('ENVIRONMENT_RESOURCE_BLOCKED: '+json.dumps(record,sort_keys=True))

def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'))+'\n'
def write(path,value):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(canonical(value),encoding='utf-8')
def sha(path):
    with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def require(value,message):
    if not value:raise ValueError(message)
def policy(root):return json.loads((root/'docs/qualification/segmented-plan.json').read_text())
def append(evidence,filename,value):
    evidence.mkdir(parents=True,exist_ok=True)
    with (evidence/filename).open('a',encoding='utf-8') as f:f.write(canonical(value))
    print(canonical(value),flush=True)

def usage(path):
    """Stat only, do not traverse links. Logical and unique allocated sizes are distinct."""
    path=Path(path);seen=set();logical=allocated=files=links=0
    stack=[path]
    while stack:
        p=stack.pop()
        if not p.exists() and not p.is_symlink():continue
        s=p.lstat()
        if stat.S_ISLNK(s.st_mode):links+=1;continue
        if stat.S_ISDIR(s.st_mode):stack.extend(p.iterdir())
        elif stat.S_ISREG(s.st_mode):
            files+=1;logical+=s.st_size;key=(s.st_dev,s.st_ino)
            if key not in seen:allocated+=getattr(s,'st_blocks',(s.st_size+511)//512)*512;seen.add(key)
    return dict(logical_bytes=logical,unique_allocated_bytes=allocated,files=files,symlinks_not_followed=links)

def snapshot(root,evidence,phase):
    temp=Path(os.environ['RUNNER_TEMP'])
    elan=Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))
    groups=dict(toolchain=elan/'toolchains',toolchain_downloads=elan/'downloads',toolchain_temporary=elan/'tmp',
                compressed_mathlib=temp/'gss-mathlib-compressed',dependencies=root/'.lake/packages',
                annex_outputs=root/'.lake/build',incoming=Path(os.environ['INCOMING_DIR']),
                payload=Path(os.environ['PAYLOAD_DIR']),evidence=evidence,runner_temp=temp)
    value=dict(kind='CAPACITY_SNAPSHOT',phase=phase,time=time.time(),free_bytes=shutil.disk_usage(root).free,
               groups={k:usage(p) for k,p in groups.items()},groups_overlap_do_not_sum=True,
               setup_outcome=os.environ.get('SETUP_OUTCOME'),cache_outcome=os.environ.get('CACHE_OUTCOME'))
    packages=root/'.lake/packages'
    value['dependency_expanded_builds']={p.name:usage(p/'.lake/build') for p in sorted(packages.iterdir()) if p.is_dir() and not p.is_symlink()} if packages.exists() else {}
    append(evidence,'capacity.jsonl',value);return value

def admission(root,evidence,phase,remaining_output_bytes=0,temporary_bytes=0,free_bytes=None):
    """Reserve the unchanged 4 GiB floor PLUS bounded future allocations."""
    require(remaining_output_bytes>=0 and temporary_bytes>=0,'negative capacity request')
    free=shutil.disk_usage(root).free if free_bytes is None else free_bytes
    required=DISK_FLOOR+remaining_output_bytes+temporary_bytes+EVIDENCE_MARGIN
    rec=dict(kind='RESOURCE_ADMISSION',phase=phase,time=time.time(),free_bytes=free,
             minimum_free_floor_bytes=DISK_FLOOR,remaining_output_allowance_bytes=remaining_output_bytes,
             temporary_peak_allowance_bytes=temporary_bytes,evidence_margin_bytes=EVIDENCE_MARGIN,
             required_free_bytes=required,shortfall_bytes=max(0,required-free),
             status='PASS' if free>=required else 'ENVIRONMENT_RESOURCE_BLOCKED',
             future_linux_sizes='NOT_MEASURED_POLICY_BOUNDS_NOT_PREDICTIONS')
    append(evidence,'resource-admissions.jsonl',rec)
    if free<required:write(evidence/'resource-blocked.json',rec);raise ResourceBlocked(rec)
    return rec

def compilation_admission(root,evidence,phase):
    from scoped_runtime import selected
    limits=selected(policy(root))['limits']
    own=limits['own_output_bytes'];incoming=limits['incoming_output_bytes']
    resident=usage(root/'.lake/build/lib/lean')['logical_bytes']+usage(Path(os.environ['PAYLOAD_DIR']).parent/'gss-bundles')['logical_bytes']
    require(resident<=own+incoming,'resident scoped outputs exceed bounded allowance')
    evidence_resident=usage(evidence)['logical_bytes']
    evidence_remaining=max(0,limits.get('evidence_output_bytes',0)-evidence_resident)
    return admission(root,evidence,phase,remaining_output_bytes=max(0,own+incoming-resident)+evidence_remaining)

def hosted_owned_cache(root,evidence):
    require(sys.platform=='linux' and os.environ.get('GITHUB_ACTIONS')=='true' and
            os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted','cleanup only on disposable GitHub Linux runner')
    temp=Path(os.environ['RUNNER_TEMP']);cache=Path(os.environ['MATHLIB_CACHE_DIR'])
    require(temp.is_absolute() and cache==temp/'gss-mathlib-compressed','exact dedicated compressed cache path')
    require(cache.resolve().parent==temp.resolve() and not cache.is_symlink(),'cache path containment')
    for parent in [temp,cache]:require(not parent.is_symlink(),'linked cleanup root forbidden')
    return cache

def initialize_cache(root,evidence,ident):
    cache=hosted_owned_cache(root,evidence)
    require(not cache.exists(),'fresh task-owned compressed cache required')
    cache.mkdir()
    write(evidence/'compressed-cache-owner.json',dict(path=str(cache.resolve()),identity=ident,created_empty=True))

def cleanup_archives(root,evidence,ident):
    cache=hosted_owned_cache(root,evidence)
    owner=json.loads((evidence/'compressed-cache-owner.json').read_text())
    result=json.loads((evidence/'cache-get.json').read_text())
    require(owner==dict(path=str(cache.resolve()),identity=ident,created_empty=True),'cache ownership identity')
    require(result['exit_code']==0 and result['identity']==ident,'successful exact cache expansion required')
    require(result.get('expanded_verified') is True,'requested closure has not been verified')
    inventory=json.loads((evidence/'cache-expanded.json').read_text())
    require(sha(evidence/'cache-expanded.json')==result['expanded_inventory_sha256'],'expanded inventory binding')
    for row in inventory:
        p=root/row['path'];require(p.is_file() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'requested expanded bytes changed')
    snapshot(root,evidence,'before_compressed_archive_cleanup')
    selected=[]
    for p in sorted(cache.iterdir()):
        if not re.fullmatch(r'[0-9a-f]{16}\.ltar',p.name):continue
        s=p.lstat();require(stat.S_ISREG(s.st_mode) and s.st_nlink==1 and p.resolve().parent==cache.resolve(),'non-owned archive or link')
        selected.append((p,s,sha(p)))
    for p,s,digest in selected:
        current=p.lstat();require((current.st_dev,current.st_ino,current.st_size,current.st_mtime_ns)==(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns),'archive changed')
        row=dict(path=str(p),bytes=s.st_size,sha256=digest,reason='Exact selective cache get exit0; requested closure bytes verified; run-owned compressed copy only')
        append(evidence,'cleanup-authorizations.jsonl',row)
        p.unlink()
        append(evidence,'cleanup-completed.jsonl',row)
    after=snapshot(root,evidence,'after_compressed_archive_cleanup')
    write(evidence/'cleanup-summary.json',dict(removed_files=len(selected),logical_bytes=sum(s.st_size for _,s,_ in selected),free_bytes_after=after['free_bytes'],expanded_dependencies_deleted=False,toolchain_deleted=False,scope=str(cache)))
    return len(selected)

def move_exact(source,dest,expected,source_root,dest_root):
    """Consume an exact owned artifact by same-filesystem rename, never copy fallback."""
    source=Path(source);dest=Path(dest)
    require(source.resolve().is_relative_to(source_root.resolve()) and dest.resolve().is_relative_to(dest_root.resolve()),'link containment')
    require(not source.is_symlink() and stat.S_ISREG(source.lstat().st_mode),'regular link source required')
    require(source.stat().st_size==expected['bytes'] and sha(source)==expected['sha256'],'link source bytes')
    require(not dest.exists() and not dest.is_symlink(),'preexisting destination')
    dest.parent.mkdir(parents=True,exist_ok=True)
    require(source.stat().st_dev==dest.parent.stat().st_dev,'different filesystems: copy peak not admitted')
    source.rename(dest)
    require(not source.exists() and dest.stat().st_size==expected['bytes'] and sha(dest)==expected['sha256'],'move readback')

def zip_bound(rows,metadata=65536):
    return sum(r['bytes']+(r['bytes']>>12)+(r['bytes']>>14)+(r['bytes']>>25)+13+1024 for r in rows)+metadata

def failure_report(root,evidence,payload,ident,needs,checks):
    """A reserved <=1 MiB report independent of all compiler/dependency/artifact paths."""
    require(set(needs)=={s['stage'] for s in policy(root)['stages']},'incomplete job map')
    states={k:v.get('result','unknown') for k,v in needs.items()}
    require(not all(v=='success' for v in states.values()),'all-success does not enter failure reporter')
    require(not payload.exists() or not list(payload.iterdir()),'fresh report payload required')
    payload.mkdir(parents=True,exist_ok=True)
    value=dict(schema='mathlibannex.resource-failure-report.v1',qualification='FAIL',identity=ident,
               reason='Required predecessor failed, was skipped or cancelled; consult original job logs',
               jobs=states,checks={k:'NOT_RUN' for k in checks},checks_note='This lightweight reporter executes no qualification checks; job results above are separate observations.',
               native_setup='NOT_RUN',prior_artifacts_required=False,report_budget_bytes=REPORT_CAP,
               public_deployment='NOT_PERFORMED',owner_acceptance=False)
    write(payload/'failure.json',value)
    summary='# GSS hosted qualification: FAIL\n\n'+''.join('- '+k+': '+v+'\n' for k,v in sorted(states.items()))
    summary+='\nLight report: no Lean/Mathlib setup and no prior artifact download. Full qualification is not PASS.\n'
    (payload/'summary.md').write_text(summary,encoding='utf-8')
    rows=[dict(bytes=p.stat().st_size) for p in payload.iterdir()]
    bound=zip_bound(rows)
    require(bound<=REPORT_CAP,'FAILURE_REPORT_BUDGET_EXCEEDED')
    write(payload/'upload-budget.json',dict(status='PASS',qualification='FAIL',budget_bytes=REPORT_CAP,reserved_bytes=bound,measurement='ACTUAL_PAYLOAD_PLUS_ZIP_BOUND',reservation='DISJOINT_FIXED_RESERVE_DEDUCTED_FROM_NORMAL_CUMULATIVE_CAP',prior_artifacts_required=False))
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with Path(os.environ['GITHUB_STEP_SUMMARY']).open('a',encoding='utf-8') as f:f.write(summary)
    print(canonical(value),flush=True)
    return value
