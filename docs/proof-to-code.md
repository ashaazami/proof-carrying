# From proof to C

![Theorem statement to LLM to Lean kernel to compiled C, with a rejection loop from the
kernel back to the model.](pipeline.svg)

What the compiler does with a verified program, end to end. Every listing here is taken
verbatim from the repository or from `build/`.

## The source

`Programs/ListMax/ListMax.lean` — one definition and three theorems about it.

```lean
def listMax (x : ℕ) (xs : List ℕ) : ℕ :=
  match xs with
  | [] => x
  | y :: ys => listMax (if x ≥ y then x else y) ys
```

```lean
theorem le_listMax     (x : ℕ) (xs : List ℕ) : listMax x xs ≥ x
theorem listMax_is_max (x : ℕ) (xs : List ℕ) (a : ℕ) : a ∈ x :: xs → listMax x xs ≥ a
theorem listMax_mem    (x : ℕ) (xs : List ℕ) : listMax x xs ∈ x :: xs
```

Together the last two characterise the maximum: an upper bound that is also a member of
the list, which nothing but the maximum can be.

## The generated C

`build/Programs/ListMax/ListMax.c`, the core function:

```c
LEAN_EXPORT lean_object *lp_ProofCarrying_listMax(lean_object *v_x_1_,
                                                  lean_object *v_xs_2_) {
_start: {
  if (lean_obj_tag(v_xs_2_) == 0) {         // list is empty
    lean_inc(v_x_1_);
    return v_x_1_;                          //   return the accumulator
  } else {
    v_head_3_ = lean_ctor_get(v_xs_2_, 0);  // head
    v_tail_4_ = lean_ctor_get(v_xs_2_, 1);  // tail
    v___x_5_ = lean_nat_dec_le(v_head_3_, v_x_1_);
    if (v___x_5_ == 0) {                    // head > accumulator
      v_x_1_ = v_head_3_;                   //   take it
      v_xs_2_ = v_tail_4_;
      goto _start;
    } else {
      v_xs_2_ = v_tail_4_;
      goto _start;
    }
  }
}
}
```

Reading it needs only a few conventions: `lean_object *` because Lean boxes every value
uniformly; `lean_obj_tag` asks which constructor a value was built with (`nil` is 0,
`cons` is 1); `lean_ctor_get(xs, 0)` and `(xs, 1)` are the head and tail; `lean_inc` is
reference counting.

## Two things to notice

**The theorems are not there.** Not as a runtime check, not as an assertion, not as a
comment:

| | appearances in the C |
|---|---|
| `listMax` | 9 |
| `le_listMax` | 0 |
| `listMax_is_max` | 0 |
| `listMax_mem` | 0 |

Proofs are erased at compile time. `listMax_mem` was added after the C above was first
generated, and the file stayed at exactly 138 lines — adding a theorem changed nothing.

The same measured on a file that is *only* theorems: `MathTheorems/Sqrt2Irrational.lean`
holds four of them, and its compiled output is 42 lines of module header with no
executable code at all. That is why `build/` mirrors only `Programs/` — there is nothing
to read on the other side.

**The recursion became a loop.** No recursive call appears; both branches end in
`goto _start` with the parameters overwritten. `listMax` is tail-recursive, so it runs in
constant stack whatever the list length. You write it recursively because that is the
form induction reasons about, and it runs as iteration.

## Regenerate it

```sh
scripts/build.sh                             # mirror Programs/ C into build/
scripts/show-c.sh Programs.ListMax.ListMax   # or straight to stdout
```

`build/` is gitignored — it is derived, and goes stale the moment a `.lean` file changes.

## Why this matters

The cost of a proof is paid entirely at build time. What ships is an ordinary
tail-recursive loop, indistinguishable from what you would have written by hand — except
that a machine has checked it returns the maximum of every list it is ever given.
