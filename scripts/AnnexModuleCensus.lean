/- Whole-library module-origin inspection. No mathematical declarations are added.
All fields and the three-axiom allowlist are retained; output is streamed to
the explicitly supplied CENSUS_OUTPUT file to avoid command-message retention. -/
import MathlibAnnex
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Meta.Tactic.Simp.Main

open Lean
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

run_cmd do
  let env ← getEnv
  let some outputPath ← IO.getEnv "CENSUS_OUTPUT"
    | throwError "CENSUS_OUTPUT is required"
  let stream ← IO.FS.Handle.mk outputPath .write
  let text ← IO.FS.readFile "docs/qualification/all-library-modules.txt"
  let wanted := (text.splitOn "\n").filterMap fun s =>
    let s := s.trimAscii.toString
    if s.isEmpty then none else some s.toName
  unless wanted.length == 732 do
    throwError "Expected 732 source modules, got {wanted.length}"
  let mut moduleSet : NameSet := {}
  for m in wanted do
    if moduleSet.contains m then
      throwError "Duplicate wanted module: {m}"
    moduleSet := moduleSet.insert m
    unless env.header.moduleNames.contains m do
      throwError "Missing imported source module: {m}"
    stream.putStrLn s!"MODULE\t{m}"
  let selected := env.constants.fold (init := #[]) fun selected name info =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if moduleSet.contains env.header.moduleNames[idx]! then selected.push (name, info)
      else selected
    | none => selected
  stream.flush
  let mut count := 0
  for (declName, info) in selected.qsort (fun a b => Name.quickLt a.1 b.1) do
    if let some idx := env.getModuleIdxFor? declName then
      let moduleName := env.header.moduleNames[idx]!
      if moduleSet.contains moduleName then
        let axioms := (← Lean.collectAxioms declName).qsort Name.quickLt
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Unexpected axiom {ax} in {declName} from {moduleName}"
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "def"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let typeDeps := info.type.getUsedConstants.qsort Name.quickLt
        let valueDeps := (match info.value? (allowOpaque := true) with
          | some v => v.getUsedConstants
          | none => #[]).qsort Name.quickLt
        let typeFmt ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr info.type
        let typeJson := Json.compress (toJson (typeFmt.pretty 1000000))
        let isInstance := Lean.Meta.isInstanceCore env declName
        let isSimp := (Lean.Meta.simpExtension.getState env).lemmaNames.contains (.decl declName)
        stream.putStrLn s!"DECL\t{declName}\t{moduleName}\t{kind}\t{String.intercalate "," (info.levelParams.map Name.toString)}\t{isInstance}\t{isSimp}\t{String.intercalate "," (axioms.toList.map Name.toString)}\t{String.intercalate "," (typeDeps.toList.map Name.toString)}\t{String.intercalate "," (valueDeps.toList.map Name.toString)}\t{typeJson}"
        count := count + 1
        if count % 100 == 0 then stream.flush
  stream.putStrLn s!"SUMMARY\t{count}"
  stream.putStrLn "PASS_ANNEX_MODULE_ORIGIN_AXIOMS"
  stream.flush
  IO.println s!"CENSUS_ROWS_WRITTEN\t{count}"
  IO.println "PASS_ANNEX_MODULE_ORIGIN_AXIOMS"
