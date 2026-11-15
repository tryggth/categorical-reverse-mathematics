/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James F. Walters
-/
import Lean
import HomotopyCRM

open Lean

/-- Verify every Lean declaration listed in `blueprint/lean_decls` exists in the
    compiled `HomotopyCRM` kernel environment and contains zero `sorry` axioms. -/
unsafe def main (args : List String) : IO UInt32 := do
  let declPath : System.FilePath := match args with
    | [p] => p
    | []  => "blueprint/lean_decls"
    | _   => ""
  if declPath == "" then
    IO.eprintln "Usage: lake exe checkdecls [path/to/lean_decls]"
    return 1
  unless ← declPath.pathExists do
    IO.eprintln s!"Declaration list not found: {declPath}"
    return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `HomotopyCRM }] {}
  let rawLines ← IO.FS.lines declPath
  let mut checked : Nat := 0
  let mut ok : Bool := true
  for raw in rawLines do
    let s := raw.trimAscii.toString
    if s.isEmpty || s.startsWith "#" then
      continue
    let name := s.toName
    match env.find? name with
    | none =>
      IO.eprintln s!"MISSING Lean declaration cited in book: {s}"
      ok := false
    | some ci =>
      let hasSorry := ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false
      if hasSorry then
        IO.eprintln s!"SORRY found in Lean declaration cited in book: {s}"
        ok := false
      checked := checked + 1
  if ok then
    IO.println s!"checkdecls PASSED: verified {checked} Lean declarations in HomotopyCRM."
    return 0
  else
    return 1
