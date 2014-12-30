A small, incomplete, and **inconsistent** formalization of homotopy type theory in Idris. This demonstrates that any attempt to formalize HoTT in Idris will be unsound under Idris's current handling of equality.

The issue is that Idris has heterogeneous equality, and heterogeneous equality rewriting, which allows us to prove that `True = False`. In HoTT, it is reasonable for `True = False` to be inhabited if `=` is heterogeneous. So the real issue is that the built-in `replace` function (and the `rewrite` tactic) handles heterogeneous paths as if they were homogeneous paths.

`hott.idr` is the main file. It contains the definition of paths, fibers, equivalence, and univalence. `bad.idr` contains the contradiction.


