import Lean

open Lean Parser

def main (args : List String) : IO Unit := do
  let root :: mod :: _ := args | throw (.userError "usage: deps <ROOT> <MODULE>")
  let mut out : Array String := #[]
  let mut visited : NameSet := {}
  let mut toVisit : Array Name := #[mod.toName]
  while !toVisit.isEmpty do
    let mut nextToVisit : Array Name := #[]
    for p in toVisit do
      if !visited.contains p then
        let path := modToFilePath root p "olean"
        let (mod, _) ← readModuleData path
        nextToVisit := mod.imports.foldr (init := nextToVisit) fun i nextToVisit =>
          let c := i.module
          if c.getRoot == `Mathlib then nextToVisit.push c
          else nextToVisit
        visited := visited.insert p
        out := out.push s!"{p}"
    toVisit := nextToVisit
  out.forRevM IO.println
