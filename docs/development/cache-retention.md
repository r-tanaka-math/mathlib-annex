# Persistent local Annex workspace and cache

The unpacked canonical development workspace, `.lake/build`, `.lake/packages`,
and the pinned toolchain / Mathlib caches are retained across successful tasks,
acceptance and source-version updates. Do not clean or garbage-collect these
artifacts as ordinary packaging or task-closure housekeeping.

Local verification uses normal Lake incremental dependency checks on the same
workspace. Only an identified invalid or corrupt artifact may be quarantined,
with consumer identity, reason and repair evidence. Do not rename old-name
`.olean` files, falsify traces/timestamps, pass `--old`, or bypass dependency checks.

The final hosted check starts with no Annex build output and does not restore a
GitHub project cache. It may obtain the pinned Mathlib cache. This is a fresh
Annex build, not a fresh source compilation of all Mathlib dependencies.

Receipts remain tied to exact source/toolchain/lock/compiled artifacts. Reusing
valid artifacts does not reuse a successful result for changed source blindly.
No build caches are copied into public release archives or Return ZIPs.
