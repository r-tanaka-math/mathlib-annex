import Lean

open Lean Parser

/-- Parse dependency headers with the pinned compiler, including implicit Init. -/
def main (args : List String) : IO UInt32 := do
  let [listFile] := args | throw <| IO.userError "expected one path-list file"
  for file in (← IO.FS.readFile listFile).splitOn "\n" do
    let file := file.trimAscii.toString
    if file.isEmpty then continue
    let contents ← IO.FS.readFile file
    let (header, _, messages) ← parseHeader (mkInputContext contents file)
    if messages.hasErrors then throw <| IO.userError s!"invalid header: {file}"
    let h := header.raw
    let imports := h[2].getArgs.map fun stx => stx[4].getId.toString
    let imports := if h[1].getArgs.isEmpty then #["Init"] ++ imports else imports
    IO.println (Json.mkObj [("file", toJson file), ("imports", toJson imports)]).compress
  return 0
