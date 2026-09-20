import Lean

open Lean Parser

def parseOne (env : Environment) (file : String) (headerOnly : Bool := false) : IO Json := do
  let contents ← IO.FS.readFile file
  let ctx := mkInputContext contents file
  let (header, start, errors) ← parseHeader ctx
  let h := header.raw
  let imports := h[2].getArgs.map fun stx => stx[4].getId.toString
  let mut state := start
  let mut messages := errors
  let mut kinds : Array String := #[]
  let mut onlyComments := true
  let mut finished := headerOnly
  for _ in [:(if headerOnly then 0 else 10000)] do
    let (stx, next, msgs) := parseCommand ctx { env := env, options := {} } state messages
    state := next
    messages := msgs
    if stx.isOfKind ``Lean.Parser.Command.eoi then
      finished := true
      break
    kinds := kinds.push stx.getKind.toString
    if !stx.isOfKind ``Lean.Parser.Command.moduleDoc then
      onlyComments := false
    if isTerminalCommand stx then
      break
  let diagnostics ← messages.toList.toArray.mapM fun msg => msg.toString
  let ordinaryImports := h[2].getArgs.all fun stx =>
    stx[0].getArgs.isEmpty && stx[1].getArgs.isEmpty && stx[3].getArgs.isEmpty
  -- Mathematical source may use `module` and `public import`. Project entries
  -- must still contain only ordinary imports and module documentation.
  let headerOk := h[1].getArgs.isEmpty
  let entryHeaderOk := h[0].getArgs.isEmpty && headerOk && ordinaryImports
  return Json.mkObj [
    ("file", toJson file), ("imports", toJson imports),
    ("header_only", toJson (headerOk && !errors.hasErrors)),
    ("imports_comments_only", toJson (!headerOnly && entryHeaderOk && onlyComments && finished && !messages.hasErrors)),
    ("finished", toJson finished), ("command_kinds", toJson kinds),
    ("diagnostics", toJson diagnostics)]

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Lean }] {} 0
  let mut rows : Array Json := #[]
  for file in args do
    if file.startsWith "header:" then
      rows := rows.push (← parseOne env (file.drop 7).toString true)
    else
      rows := rows.push (← parseOne env file)
  IO.println (Json.arr rows).compress
  return 0
