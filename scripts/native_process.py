"""Process-local resource containment. No global runner/security changes; no Lean bypass.

The compiler and logical arguments are unchanged by the launcher.  Only the child
process's ability to create a core dump is restricted.  The parent remains unchanged.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import sys

MiB = 1024 ** 2
GiB = 1024 ** 3


def memory_snapshot() -> dict:
    result = {}
    try:
        for line in Path('/proc/meminfo').read_text().splitlines():
            key, value = line.split(':', 1)
            if key in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree'):
                result[key + '_bytes'] = int(value.split()[0]) * 1024
    except (OSError, ValueError):
        pass
    # Observe the current cgroup-v2 node, not a guessed global limit.
    try:
        entries = Path('/proc/self/cgroup').read_text().splitlines()
        for entry in entries:
            if entry.startswith('0::'):
                rel = entry[3:].lstrip('/')
                if '..' in Path(rel).parts:
                    break
                folder = Path('/sys/fs/cgroup') / rel
                lim = (folder / 'memory.max').read_text().strip()
                cur = int((folder / 'memory.current').read_text().strip())
                result['cgroup_current_bytes'] = cur
                if lim != 'max':
                    result['cgroup_max_bytes'] = int(lim)
                    result['cgroup_headroom_bytes'] = max(0, int(lim) - cur)
                break
    except (OSError, ValueError):
        pass
    return result


def memory_admission(args: list[str], observed: dict | None = None) -> dict:
    """Only bounded Lean -M commands above the old 4096 MiB limit get a new gate."""
    value = None
    for i, arg in enumerate(args):
        if arg == '-M' and i + 1 < len(args):
            value = int(args[i + 1])
    obs = memory_snapshot() if observed is None else observed
    result = {'lean_limit_mib': value, 'observed': obs,
              'hard_group_rss_limit_bytes': 6 * GiB,
              'host_min_available_bytes_during_run': 512 * MiB}
    if value is None or 0 < value <= 4096:
        return dict(result, status='UNCHANGED_MEMORY_POLICY')
    if value != 5120:
        return dict(result, status='BLOCKED', reason='UNAPPROVED_MEMORY_LIMIT')
    # 5 GiB soft compiler limit, 6 GiB group stop, >=1 GiB of physical host reserve.
    headrooms = [obs[k] for k in ('MemAvailable_bytes', 'cgroup_headroom_bytes') if k in obs]
    valid = (obs.get('MemTotal_bytes', 0) >= 7 * GiB and
             headrooms and min(headrooms) >= 6 * GiB)
    return dict(result, status='PASS' if valid else 'BLOCKED',
                reason=None if valid else 'INSUFFICIENT_OBSERVED_MEMORY_HEADROOM')


def tail_diagnosis(log: Path, exit_code: int | None, monitor_reason: str | None) -> dict:
    try:
        with log.open('rb') as f:
            f.seek(0, 2)
            length = f.tell()
            f.seek(max(0, length - 32768))
            tail = f.read()
    except OSError:
        return {'kind': 'LOG_UNAVAILABLE', 'monitor_stop_reason': monitor_reason}
    memory = b'lean::memory_exception' in tail or b'excessive memory consumption detected' in tail
    return {'kind': ('LEAN_MEMORY_LIMIT_EXCEEDED' if memory and (exit_code != 0 or monitor_reason)
                     else 'SUCCESS' if exit_code == 0 and not monitor_reason else 'OTHER_FAILURE'),
            'memory_exception_observed': memory, 'monitor_stop_reason': monitor_reason,
            'exit_code': exit_code, 'tail_sha256': hashlib.sha256(tail).hexdigest(),
            'core_dump_cause': 'NOT_ESTABLISHED_BY_THIS_LOG'}


def launch_arguments(args: list[str], receipt: Path) -> list[str]:
    return [sys.executable, '-B', str(Path(__file__).resolve()), '--receipt', str(receipt), '--', *args]


def child_policy() -> dict:
    if sys.platform != 'linux':
        raise RuntimeError('This child containment launcher is for Linux qualification only')
    import resource
    before = resource.getrlimit(resource.RLIMIT_CORE)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    # coredump_filter survives exec; on kernels exposing it, omit process
    # mappings even if a pipe collector ignores RLIMIT_CORE. Small ELF/vDSO
    # metadata may remain. A full GitHub runner must expose enough information.
    filt = Path('/proc/self/coredump_filter')
    before_filter = None
    after_filter = None
    if filt.exists():
        before_filter = filt.read_text().strip()
        filt.write_text('0x0\n')
        after_filter = int(filt.read_text().strip(), 16)
        if after_filter != 0:
            raise RuntimeError('Child memory-dump filter was not applied')
    try:
        pattern = Path('/proc/sys/kernel/core_pattern').read_text().strip()
    except FileNotFoundError:
        pattern = None
    if pattern and pattern.startswith('|') and after_filter != 0:
        raise RuntimeError('Pipe core collector without an effective child dump filter')
    if os.environ.get('GITHUB_ACTIONS') == 'true' and pattern is None and after_filter is None:
        raise RuntimeError('GitHub runner core policy cannot be established before compiler start')
    if resource.getrlimit(resource.RLIMIT_CORE) != (0, 0):
        raise RuntimeError('Child RLIMIT_CORE was not applied')
    return {'schema': 'annex.native-child-containment.v1', 'pid': os.getpid(),
            'core_limit_before': list(before), 'core_limit_after': [0, 0],
            'coredump_filter_before': before_filter, 'coredump_filter_after': after_filter,
            'core_pattern_observed': pattern,
            'filter_status': 'APPLIED' if after_filter == 0 else 'NOT_EXPOSED_BY_TEST_KERNEL',
            'pipe_metadata_core_not_claimed_impossible': True,
            'global_settings_changed': False, 'compiler_trust_modified': False}


def main() -> int:
    argv = sys.argv[1:]
    if len(argv) < 4 or argv[0] != '--receipt' or argv[2] != '--':
        raise ValueError('Expected --receipt PATH -- COMMAND [ARG ...]')
    receipt = Path(argv[1]); args = argv[3:]
    if receipt.is_symlink() or receipt.exists():
        raise ValueError('A fresh child policy receipt is required')
    record = child_policy()
    record['logical_argv'] = args
    receipt.parent.mkdir(parents=True, exist_ok=True)
    with receipt.open('x', encoding='utf-8') as out:
        out.write(json.dumps(record, sort_keys=True) + '\n')
        out.flush()
        os.fsync(out.fileno())
    os.execvpe(args[0], args, os.environ)
    return 127


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError) as exc:
        print('NATIVE_CHILD_POLICY_FAILURE: ' + str(exc), file=sys.stderr)
        raise SystemExit(125)
