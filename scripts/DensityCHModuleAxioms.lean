import MathlibAnnex.Projects.Naimark
import Lean.Util.CollectAxioms
open Lean
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`MathlibAnnex.Analysis.CStarAlgebra.CAR.Cardinality,
    `MathlibAnnex.Analysis.CStarAlgebra.CAR.ContinuumHypothesis,
    `MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CharacterCardinality,
    `MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactImageOfRankOne,
    `MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactModelDensity,
    `MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CyclicDensity,
    `MathlibAnnex.Analysis.CStarAlgebra.NonUnital.DensityLowerBound,
    `MathlibAnnex.Analysis.CStarAlgebra.NonUnital.MinimalProjectionDensity,
    `MathlibAnnex.Analysis.CStarAlgebra.Representation.CharacterCardinality,
    `MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactModelDensity,
    `MathlibAnnex.Analysis.CStarAlgebra.Representation.DensityCharacter,
    `MathlibAnnex.Analysis.CStarAlgebra.Representation.DensityLowerBound,
    `MathlibAnnex.Analysis.CStarAlgebra.Representation.MinimalProjectionDensity,
    `MathlibAnnex.Analysis.CStarAlgebra.Representation.SeparableCardinality,
    `MathlibAnnex.Analysis.Normed.Operator.Cardinality,
    `MathlibAnnex.Topology.CompactCardinality,
    `MathlibAnnex.Topology.DensityCharacter,
    `MathlibAnnex.Topology.MetricSpace.DenseCardinality,
    `MathlibAnnex.Topology.MetricSpace.SeparableCardinality]
  let mut seenModules : NameSet := {}
  let mut count := 0
  let mut sawCantor := false
  for (declName, _) in env.constants.toList.toArray.qsort (fun a b => Name.quickLt a.1 b.1) do
    if let some moduleIdx := env.getModuleIdxFor? declName then
      let moduleName := env.header.moduleNames[moduleIdx]!
      if wanted.contains moduleName then
        seenModules := seenModules.insert moduleName
        let axioms := (← Lean.collectAxioms declName).qsort Name.quickLt
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} for {declName} from {moduleName}"
        if declName == `CantorScheme.nonempty_iInter_of_isCompact then
          sawCantor := true
        IO.println s!"DECL\t{declName}\t{moduleName}\t{String.intercalate "," (axioms.toList.map Name.toString)}"
        count := count + 1
  for moduleName in wanted do
    unless seenModules.contains moduleName do
      throwError "no compiled declarations from {moduleName}"
  unless sawCantor do
    throwError "root CantorScheme declaration omitted from module-origin audit"
  IO.println s!"SUMMARY\t{count}"
