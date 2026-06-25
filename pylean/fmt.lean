-- Formatter for py2many-generated Lean sources.
--
-- Parses a single .lean file into a module syntax tree and re-emits it through
-- Lean's own pretty printer (`Lean.PrettyPrinter.ppModule`), rewriting the file
-- in place. There is no standalone Lean source formatter yet, so this drives the
-- compiler's built-in pretty printer instead.
--
-- The pretty printer leaves trailing whitespace and surrounds the output with
-- blank lines, so we post-process: strip trailing whitespace per line, drop
-- leading/trailing blank lines, and restore the space the pretty printer drops
-- between a closing paren and the `do` of a `for x in (e) do` loop.
--
-- Invoked by py2many as: lean --run pylean/fmt.lean <file.lean>
import Lean
open Lean Lean.Parser Lean.PrettyPrinter

/-- Drop trailing spaces and tabs from a single line. -/
private def rstrip (line : String) : String :=
  String.ofList (line.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse

/-- Strip trailing whitespace per line and surrounding blank lines. -/
private def tidy (s : String) : String :=
  let lines := (s.splitOn "\n").map (fun l => (rstrip l).replace ")do" ") do")
  let lines := lines.dropWhile (· == "")
  let lines := (lines.reverse.dropWhile (· == "")).reverse
  String.intercalate "\n" lines ++ "\n"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let contents ← IO.FS.readFile path
    Lean.enableInitializersExecution
    let env ← importModules #[{ module := `Init }] {} (loadExts := true)
    let stx ← testParseModule env path contents
    let coreCtx : Core.Context := { fileName := path, fileMap := FileMap.ofString contents }
    match ← ((ppModule ⟨stx⟩).toIO coreCtx { env }).toBaseIO with
    | .ok (fmt, _) => IO.FS.writeFile path (tidy (toString fmt)); pure 0
    | .error e => IO.eprintln s!"lean fmt error: {toString e}"; pure 1
  | _ => IO.eprintln "usage: fmt <file.lean>"; pure 2
