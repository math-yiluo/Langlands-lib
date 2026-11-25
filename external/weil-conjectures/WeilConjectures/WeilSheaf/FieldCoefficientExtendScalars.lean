/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible
public import WeilConjectures.WeilSheaf.FieldCoefficient

/-!
# From `E`-Weil complexes to `ℚ̄_ℓ`-Weil complexes

Following blueprint `definition-weil-structure`, the `ℚ̄_ℓ`-stage `D^b_{c,W}(X, ℚ̄_ℓ)` is the
`2`-colimit of the stages `D^b_{c,W}(X, E)` over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the
transition functors being the extensions of scalars.
In this repository the `ℚ̄_ℓ`-stage is realised directly, as `AlgebraicGeometry.WeilComplex`
(Weil complexes of modules over the constant sheaf `ℚ̄_ℓ,X̄` of locally finite functions), and the
`E`-stage as `AlgebraicGeometry.FieldWeilComplex` (modules over `E_X̄ : U ↦ C(U, E)`). This file
constructs the functors from the `E`-stages to the `ℚ̄_ℓ`-stage: the extension of scalars
`ℚ̄_ℓ ⊗_E -` of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdic`) is exact, commutes with the Frobenius
pullbacks (`AlgebraicGeometry.fieldExtendScalarsToAdicFrobeniusIso`) and preserves
constructibility, hence induces an exact functor on pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsToAdic`) and a functor
`D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` (`AlgebraicGeometry.FieldWeilComplex.extendScalarsToAdic`,
and `AlgebraicGeometry.FieldWeilComplex.toWeilComplex` for a subfield `E ⊆ ℚ̄_ℓ`).

The transition functors between two finite stages `E ⊆ E'`, the cocone of these functors
(`AlgebraicGeometry.FieldWeilComplex.cocone`) and the `2`-colimit
`AlgebraicGeometry.WeilComplexTwoColimit`, with its comparison functor to
`AlgebraicGeometry.WeilComplex`, are in `WeilConjectures.WeilSheaf.FieldCoefficientTransition`
and `WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ -` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*`. -/
noncomputable def fieldExtendScalarsToAdicFrobeniusIso :
    fieldExtendScalarsToAdic he hc (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⋙
        WeilSheaf.frobeniusPullback k₀ l X ≅
      FieldWeilSheaf.frobeniusPullback k₀ Λ X ⋙
        fieldExtendScalarsToAdic he hc (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm ≪≫
    (fieldUpperStarCompExtendScalarsToAdicIso he hc
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).symm ≪≫
    Functor.isoWhiskerRight
      (fieldUpperStarIsoLowerStarInv Λ
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso) _

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ -` of pro-étale Weil sheaves. -/
noncomputable def ProEtaleFieldWeilSheaf.extendScalarsToAdic :
    ProEtaleFieldWeilSheaf k₀ Λ X ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mapOfNatIso (fieldExtendScalarsToAdicFrobeniusIso he hc k₀ X)

instance : (ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

instance : PreservesFiniteLimits (ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance : PreservesFiniteColimits (ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X) :=
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

variable [Fact (ringChar k₀ ≠ l)]

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex, the functor from the
stage `Λ = E` to the stage `ℚ̄_ℓ`.

The functor `D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` towards the `2`-colimit, induced on derived
categories by the exact extension of scalars `ℚ̄_ℓ ⊗_E -` of pro-étale Weil sheaves, which
preserves constructibility. -/
noncomputable def FieldWeilComplex.extendScalarsToAdic :
    FieldWeilComplex k₀ Λ X ⥤ WeilComplex k₀ l X :=
  (FieldWeilComplex.objectProperty k₀ Λ X).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X).mapDerivedCategory
    fun K hK ↦ ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
      (WeilSheaf.objectProperty k₀ l X).prop_of_iso
        (((ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X
          ).mapDerivedCategoryHomologyFunctorIso n).app K) ((hK.2 n).extendScalarsToAdic he hc)⟩


section Subfield

variable (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E]

/-- Blueprint `definition-weil-structure`: the functor `D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)`
for a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the extension of scalars along the inclusion
`E → ℚ̄_ℓ` (`AlgebraicGeometry.FieldWeilComplex.extendScalarsToAdic`). -/
noncomputable def FieldWeilComplex.toWeilComplex : FieldWeilComplex k₀ E X ⥤ WeilComplex k₀ l X :=
  FieldWeilComplex.extendScalarsToAdic (e := E.val) continuous_subtype_val
    ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).subtype_mk _) k₀ X

end Subfield

end AlgebraicGeometry
