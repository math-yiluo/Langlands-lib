/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex

/-!
# Koszul-regular and H₁-regular sequences

Source: Stacks Project, More on Algebra, Definition 15.31.1, Tag 062E
(blueprint: def-weil-pbc-koszul-regular-sequence).

The Koszul complex is indexed by `ℕ`, with negative degrees zero by the extension
convention of def-weil-pbc-module-chain-complex-homology. Vanishing in all nonzero
integer degrees therefore means vanishing in all nonzero natural degrees.
The module-valued homology is Mathlib's kernel-modulo-image homology; `IsZero`
expresses that this module is zero, without requiring a chosen equality to a zero object.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingTheory.Sequence

/-- `M`-Koszul-regularity: all nonzero homology of `K_•(f) ⊗[R] M` vanishes.
The tensor complex is the existing degreewise tensor construction, with differentials
`d ⊗ id_M`. Source: Stacks, Tag 062E, clause (1)
(blueprint: def-weil-pbc-koszul-regular-sequence). -/
def IsKoszulRegularOn {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplexTensor R r f M).homology i)

/-- `M`-H₁-regularity: the first homology of `K_•(f) ⊗[R] M` vanishes.
Source: Stacks, Tag 062E, clause (2)
(blueprint: def-weil-pbc-koszul-regular-sequence). -/
def IsH1RegularOn {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) : Prop :=
  IsZero ((ExteriorAlgebra.koszulComplexTensor R r f M).homology 1)

/-- Koszul-regularity: all nonzero homology of `K_•(f)` vanishes.
Source: Stacks, Tag 062E, clause (3)
(blueprint: def-weil-pbc-koszul-regular-sequence). -/
def IsKoszulRegular {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplex R r f).homology i)

/-- H₁-regularity: the first homology of `K_•(f)` vanishes.
Source: Stacks, Tag 062E, clause (4)
(blueprint: def-weil-pbc-koszul-regular-sequence). -/
def IsH1Regular {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) : Prop :=
  IsZero ((ExteriorAlgebra.koszulComplex R r f).homology 1)

end RingTheory.Sequence
