/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import WeilConjectures.CategoryTheory.Idempotents.TStructure
public import WeilConjectures.CategoryTheory.StageSystem.IdempotentComplete
public import WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit

/-!
# Idempotent completeness of the `E`-stages and of their `2`-colimit

The standard t-structure of the derived category of pro-étale `E`-Weil sheaves induces a bounded
t-structure on `D^b_{c,W}(X, E)` (`AlgebraicGeometry.FieldWeilComplex.tStructure`), so that
`D^b_{c,W}(X, E)` is idempotent complete and its canonical functor into its Karoubi envelope is
an exact equivalence, by the Karoubian bounded-t theorem.

The common-stage category `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` of blueprint
`definition-weil-structure` (`AlgebraicGeometry.WeilComplexTwoColimit`) is then idempotent
complete as well, a filtered `2`-colimit of idempotent complete categories being idempotent
complete (`CategoryTheory.StageSystem.PairCategory.isIdempotentComplete`); hence its canonical
functor into its Karoubi envelope is an equivalence.

This file also records the forgetful functor `For` and the derived Frobenius isomorphism `θ` of
the `2`-colimit model, through its comparison functor to the direct `ℚ̄_ℓ`-stage
`AlgebraicGeometry.WeilComplex`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Triangulated

namespace AlgebraicGeometry

namespace FieldWeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (Λ : Type) [NormedField Λ] [IsUltrametricDist Λ]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- `D^b_{c,W}(X, Λ)` is stable under the truncations of the canonical t-structure of the derived
category of pro-étale `Λ`-Weil sheaves. -/
instance : (objectProperty k₀ Λ X).HasInducedTStructure _root_.DerivedCategory.TStructure.t :=
  .mk' fun K hK n ↦ by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncLE hc n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncGE hc n⟩⟩

/-- The canonical t-structure on `D^b_{c,W}(X, Λ)`, induced by the canonical t-structure of the
derived category of pro-étale `Λ`-Weil sheaves. -/
noncomputable def tStructure : TStructure (FieldWeilComplex k₀ Λ X) :=
  (objectProperty k₀ Λ X).tStructure _root_.DerivedCategory.TStructure.t

/-- The canonical t-structure on `D^b_{c,W}(X, Λ)` is bounded. -/
lemma tStructure_bounded (K : FieldWeilComplex k₀ Λ X) : (tStructure k₀ Λ X).bounded K := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  exact ⟨⟨a, (ObjectProperty.tStructure_isGE_iff _ _ K a).2 ha⟩,
    ⟨b, (ObjectProperty.tStructure_isLE_iff _ _ K b).2 hb⟩⟩

/-- `D^b_{c,W}(X, Λ)` is idempotent complete. -/
instance isIdempotentComplete : IsIdempotentComplete (FieldWeilComplex k₀ Λ X) :=
  (tStructure k₀ Λ X).isIdempotentComplete_of_bounded (tStructure_bounded k₀ Λ X)

/-- The canonical functor from `D^b_{c,W}(X, Λ)` into its Karoubi envelope is an exact
equivalence. -/
theorem isEquivalence_toKaroubi_and_isTriangulated :
    (Idempotents.toKaroubi (FieldWeilComplex k₀ Λ X)).IsEquivalence ∧
      (Idempotents.toKaroubi (FieldWeilComplex k₀ Λ X)).IsTriangulated :=
  (tStructure k₀ Λ X).isEquivalence_toKaroubi_and_isTriangulated_of_bounded
    (tStructure_bounded k₀ Λ X)

end FieldWeilComplex

namespace WeilComplexTwoColimit

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))]

/-- Idempotent completeness of the Weil category, for the `2`-colimit model.

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` (`AlgebraicGeometry.WeilComplexTwoColimit`) is
idempotent complete, and the canonical functor into its Karoubi envelope is an equivalence: every
stage `D^b_{c,W}(X, E)` is idempotent complete
(`AlgebraicGeometry.FieldWeilComplex.isIdempotentComplete`), and an idempotent of the
`2`-colimit is represented, and splits, at a finite stage
(`CategoryTheory.StageSystem.PairCategory.isIdempotentComplete`). The exactness of this
equivalence, for the triangulated structure of the `2`-colimit, is
`WeilComplexTwoColimit.isIdempotentComplete_and_isEquivalence_toKaroubi_and_isTriangulated`
(in `WeilConjectures.WeilSheaf.FieldCoefficientTriangulated`). -/
theorem isIdempotentComplete_and_isEquivalence_toKaroubi
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    IsIdempotentComplete (WeilComplexTwoColimit k₀ l X) ∧
      (Idempotents.toKaroubi (WeilComplexTwoColimit k₀ l X)).IsEquivalence :=
  StageSystem.PairCategory.isIdempotentComplete_and_isEquivalence_toKaroubi
    (S := FieldWeilComplex.stageSystem (l := l) k₀ X)

variable {k₀ l X}

/-- Blueprint `definition-weil-structure`: the forgetful functor
`For : D^b_{c,W}(X, ℚ̄_ℓ) ⥤ D(X̄_proét, ℚ̄_ℓ)` of the `2`-colimit model, `(E, K) ↦ For(ℚ̄_ℓ ⊗_E K)`:
the comparison functor to the direct `ℚ̄_ℓ`-stage
(`AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex`) followed by its forgetful functor
(`AlgebraicGeometry.WeilComplex.forget`), whose values lie in `D^b_c(X̄, ℚ̄_ℓ)`. -/
noncomputable def forget :=
  toWeilComplex (l := l) k₀ X ⋙ WeilComplex.forget (X := X)

variable (X) in
/-- Blueprint `definition-weil-structure`: the derived Frobenius isomorphism
`θ_K : Fr_X^* For(K) ≅ For(K)` of an object `K` of the `2`-colimit model, natural in `K`: that of
its image `ℚ̄_ℓ ⊗_E K` in the direct `ℚ̄_ℓ`-stage (`AlgebraicGeometry.WeilComplex.frobeniusIso`). -/
noncomputable def frobeniusIso :
    WeilComplexTwoColimit.forget (k₀ := k₀) (l := l) (X := X) ⋙
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory ≅ WeilComplexTwoColimit.forget :=
  Functor.isoWhiskerLeft (toWeilComplex (l := l) k₀ X) (WeilComplex.frobeniusIso X)

end WeilComplexTwoColimit

end AlgebraicGeometry
