/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Pulled-back cohomology classes and connecting homomorphisms

For a morphism of schemes `g : X ⟶ Y` the comparison map
`AlgebraicGeometry.Etale.cohomologyMap g F n : Hⁿ(Y_ét, F) ⟶ Hⁿ(X_ét, g^* F)` commutes with the
connecting homomorphisms of a short exact sequence `S` of abelian sheaves on `Y` and of its
pullback `g^* S`, which is short exact since `g^*` is exact.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_δSucc`: the compatibility with connecting
  homomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **Pulling back commutes with connecting homomorphisms.** For a short exact sequence `S` of
abelian sheaves on `Y_ét` and `g : X ⟶ Y`, the square

```
  Hⁿ(Y, S.X₃) ──δ──▶ Hⁿ⁺¹(Y, S.X₁)
      │                    │
  cohomologyMap g     cohomologyMap g
      ▼                    ▼
  Hⁿ(X, g^* S.X₃) ─δ─▶ Hⁿ⁺¹(X, g^* S.X₁)
```

commutes, the bottom map being the connecting homomorphism of the short exact sequence `g^* S`.
-/
lemma cohomologyMap_δSucc {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H S.X₃ n) :
    cohomologyMap g S.X₁ (n + 1) (Sheaf.H.δSucc hS n x) =
      Sheaf.H.δSucc (hS.map_of_exact (g)^*[AddCommGrpCat.{u + 1}]) n
        (cohomologyMap g S.X₃ n x) := by
  simp only [cohomologyMap_apply, Sheaf.H.δSucc_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

end AlgebraicGeometry.Etale
