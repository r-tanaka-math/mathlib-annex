# Contributing and reporting corrections

Report corrections through the repository issue tracker. Proposed source changes can be submitted as pull requests for maintainer review.

For a mathematical or formalization correction, identify:

1. the fully qualified Lean declaration name;
2. the exact repository revision;
3. the claimed mismatch or failure;
4. a minimal reproducer or proposed source change when available.

For documentation or build corrections, identify the exact file and pinned Lean/Mathlib environment. Keep toolchain and dependency-lock changes separate from incidental repairs and explain why any such change is needed.

Keep reusable declarations in mathematically organized modules. Project entry points are comments/imports-only navigation facades. Update the relevant source-content manifest when changing an entry or its resolved closure, and provide exact qualification evidence under the contract in [Verification](VERIFICATION.md).

Identify source origins, applicable licenses and modifications in every proposed contribution. See [third-party notices](THIRD_PARTY_NOTICES.md).
