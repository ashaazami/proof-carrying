# Running the code

The example is `listMax`, from `Programs/ListMax/` — it finds the maximum of a
non-empty list, and `listMax_is_max` proves the result dominates every element.

## In the editor

Open `Programs/ListMax/Main.lean` and put your cursor on an `#eval` line. The answer
appears in the InfoView, with no build and no terminal.

```lean
#eval listMax 3 [1, 7, 2, 9, 4]              -- 9
#eval main ["3", "1", "7", "2", "9", "4"]    -- max = 9
```

`#eval` runs computable values only. It refuses a proof — proofs have nothing to run.

## From a terminal

```sh
lake exe listmax 3 1 7 2 9 4      # rebuilds if stale, then runs
./.lake/build/bin/listmax 5 100 3 # straight to the binary
```

The binary is statically linked and depends on nothing but two system libraries, so it
runs on a machine with no Lean installed. It is large (~130 MB) because Lean's runtime
and everything Mathlib pulled in are baked in.

Linking an executable also takes the build from ~8,700 jobs to ~17,000: a library build
only loads Mathlib's proofs, while linking compiles its generated C.

## What is actually in the binary

Not the proofs. `listMax_is_max` appears nowhere in the compiled output — proofs are
erased at compile time. See for yourself:

```sh
scripts/show-c.sh Programs.ListMax.ListMax   # formatted C, to stdout
scripts/build.sh                             # build, then mirror Programs/ C into build/
```

`ListMax.c` is ~138 lines, all of it the algorithm. `build/` mirrors only `Programs/`,
because theorem-only modules compile to ~42 lines of module header and nothing else —
there is nothing to read. Add a theorem to `ListMax.lean` and rerun: the C is unchanged.

Your tail-recursive `listMax` also compiles to a `goto` loop rather than a recursive
call, so it runs in constant stack whatever the list length.
