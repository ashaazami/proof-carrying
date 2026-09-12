import Programs.ListMax.ListMax

/-- A command-line front end for `listMax`.

The maximum it prints is backed by `listMax_is_max`: the result is proved
to dominate every element of the input. -/
def main (args : List String) : IO Unit := do
  match args.filterMap (·.toNat?) with
  | [] =>
    IO.println "usage: listmax N [N ...]"
  | x :: xs =>
    IO.println s!"max = {listMax x xs}"

/-! ## Running this from the editor

`#eval` runs code right here -- put your cursor on a line below and the
result appears in the InfoView. No terminal, no build.

From a terminal instead: `lake exe listmax 3 1 7 2 9 4`
-/

/-! ## Running in VS Code -/

#eval listMax 3 [1, 7, 2, 9, 4]
#eval listMax 42 []
#eval main ["3", "1", "7", "2", "9", "4"]
