import MathlibAnnex.Projects.Naimark
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Meta.Tactic.Simp.Main

open Lean

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

private def sortedNames (names : Array Name) : Array Name :=
  names.qsort Name.quickLt

run_cmd do
  let env ← getEnv
  let source ← IO.FS.readFile "scripts/PrintDensityCHAxioms.lean"
  let marker := "#print axioms "
  let names := source.splitOn "\n" |>.filterMap fun line ↦
    let line := line.trim
    if line.startsWith marker then
      some ((line.drop marker.length).trim.toName)
    else
      none
  let mut seen : NameSet := {}
  let mut count := 0
  for declName in names do
    if seen.contains declName then
      throwError "duplicate inventory declaration: {declName}"
    seen := seen.insert declName
    let some info := env.find? declName | throwError "missing compiled declaration: {declName}"
    let some moduleIdx := env.getModuleIdxFor? declName |
      throwError "missing module provenance: {declName}"
    let moduleName := env.header.moduleNames[moduleIdx]!
    let axioms := sortedNames (← Lean.collectAxioms declName)
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unexpected axiom {ax} for {declName}"
    let typeDeps := sortedNames info.type.getUsedConstants
    let valueDeps := sortedNames <| match info.value? (allowOpaque := true) with
      | some value => value.getUsedConstants
      | none => #[]
    let isInstance := Lean.Meta.isInstanceCore env declName
    let isSimp := (Lean.Meta.simpExtension.getState env).lemmaNames.contains (.decl declName)
    let typeFmt ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr info.type
    let typeJson := Json.compress (toJson (typeFmt.pretty 1000000))
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    IO.println s!"DECL\t{declName}\t{moduleName}\t{kind}\t{String.intercalate "," (info.levelParams.map Name.toString)}\t{isInstance}\t{isSimp}\t{String.intercalate "," (axioms.toList.map Name.toString)}\t{String.intercalate "," (typeDeps.toList.map Name.toString)}\t{String.intercalate "," (valueDeps.toList.map Name.toString)}\t{typeJson}"
    count := count + 1
  IO.println s!"SUMMARY\t{count}"
