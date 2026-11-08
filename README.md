# MathlibAnnex v0.6.1

MathlibAnnex collects reusable Lean declarations in functional analysis and operator algebras. This version extends the Naimark Project with von Neumann algebra foundations and the trace representation of the CAR algebra.

```lean
import MathlibAnnex.Projects.Naimark
```

The Naimark entry includes the trace representation’s finite factor, its infinite dimensionality, its finite matrix stages, and Hilbert basis cardinality results. Here the type II₁ predicate describes a nonzero infinite-dimensional factor with finite unit. The entry and its imports cover 356 modules.

The [seven Project manifests](docs/projects/MATHLIBANNEX_PROJECT_SOURCE_MANIFESTS.json) list the entry points and transitive source dependencies. The library also contains 48 production modules outside all seven entries. See [build and verification](VERIFICATION.md), [changes](CHANGELOG.md) and [source notices](THIRD_PARTY_NOTICES.md).
