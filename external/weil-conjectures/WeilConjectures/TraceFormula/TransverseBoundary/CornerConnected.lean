/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationDomain
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerStrictLocalization

/-!
# Connectedness of the complement of the divisors in the strict localization

The strict localization `S` of the regular surface `Z` at a geometric point is irreducible
(`AlgebraicGeometry.Scheme.irreducibleSpace_strictLocalization_of_isRegular`), so its open
subscheme `S - (X_S ∪ Y_S)` is preconnected (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, dévissage on a connected scheme).

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.preconnectedSpace_strictLocalizationComplement`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

/-- `S - (X_S ∪ Y_S)` is preconnected, being open in the irreducible strict localization `S`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem preconnectedSpace_strictLocalizationComplement :
    PreconnectedSpace (C.strictLocalizationComplement zbar) := by
  have := irreducibleSpace_strictLocalization_of_isRegular zbar
  let f := C.strictLocalizationComplementι zbar ≫ pullback.snd C.j (strictLocalizationToBase zbar)
  have hf := f.isOpenEmbedding
  refine ⟨?_⟩
  rw [← hf.isInducing.isPreconnected_image, Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset hf.isOpen_range
    (Set.subset_univ _)).isPreconnected

end AlgebraicGeometry.Scheme.TransverseCorner
