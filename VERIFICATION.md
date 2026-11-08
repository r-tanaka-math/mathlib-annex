# Source qualification

Owner-final run 42447808184, attempt 1, job 128630358596, passed all 18 checks on Linux for commit `ef2cc76a246881b64cba030870944cad3172817d`, tree `85e94ffe211808309453bbfbb4ce035be68fe130`. The run restored all 958 targets from verified native checkpoints. The checks included the root, independent imports and consumers for the seven Projects, the entry parser, compiled axioms, collection, required uploads and the final seal.

The census covered 948 modules and 18,752 declarations. All dependencies on axioms were within `propext`, `Classical.choice` and `Quot.sound`. The 304 compiled declarations in the new Naimark modules and consumers matched their accepted kernel type, universes, providers and axioms. Controller Lean execution was recorded as `NOT_RUN`.

This source distribution carries the exact qualified Lean modules, examples, package settings, toolchain and dependency lock. See the [qualification summary](docs/qualification/owner-final.json) for the original receipt and seal digests, and the [Project manifests](docs/projects/MATHLIBANNEX_PROJECT_SOURCE_MANIFESTS.json) for the source closures.

For a local build, run `lake exe cache get` and `lake build` at the package root. To use the Naimark results, import `MathlibAnnex.Projects.Naimark`.
