/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible
public import WeilConjectures.TateTwist.IntegralLocallyFree

/-!
# Extension of scalars of the integral Tate twists

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` and `T = - ⊗ᴸ_{𝒪_E} ℚ̄_ℓ` the extension of scalars on
bounded constructible complexes, the composite of `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`. For a separated
`k`-scheme of finite type `X`, `d ∈ ℕ` and `n ∈ ℤ`,
`T(𝒪_{E,X}(d)[n]) ≅ ℚ̄_ℓ,X(d)[n]`
(`ProEtale.CondensedRing.extendScalarsIntegralTateTwistBoundedConstructibleIso`): the two derived
extensions of scalars compose to the one along `𝒪_E ⟶ ℚ̄_ℓ`, which commutes with the shifts and is
computed on the flat module object `𝒪_{E,X}(d)` by the underived extension of scalars, and
`ℚ̄_ℓ ⊗_{𝒪_E} 𝒪_E(d) ≅ ℚ̄_ℓ(d)` (`ProEtale.extendScalarsIntegralTateTwistNatIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The inclusions `𝒪̲_E ⟶ E̲ ⟶ ℚ̲̄_ℓ` compose to the inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ`. -/
lemma padicIntegersRingObjToContinuousMapRingObj_comp_padicSubfieldRingObjToPadicAlgCl :
    AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E ≫
        padicSubfieldRingObjToPadicAlgCl ℓ E =
      padicIntegersRingObjToPadicAlgCl ℓ E.1 := by
  rw [AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj,
    padicSubfieldRingObjToPadicAlgCl, padicIntegersRingObjToPadicAlgCl, ← Functor.map_comp]
  rfl

end Profinite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The extension of scalars of the shifted integral Tate twist is the shifted Tate twist**:
`T(𝒪_{E,X}(d)[n]) ≅ ℚ̄_ℓ,X(d)[n]` in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, for `T` the extension of scalars along
`𝒪_E ⟶ E ⟶ ℚ̄_ℓ`. -/
noncomputable def extendScalarsIntegralTateTwistBoundedConstructibleIso (d : ℕ) (n : ℤ) :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleToPadicAlgCl X.left ℓ E).obj
        ((shiftFunctor _ n).obj (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)) ≅
      boundedConstructibleTateTwist ℓ X d n :=
  let φ := padicIntegersToPadicSubfield X.left ℓ E
  let ψ := padicSubfieldRingObjToPadicAlgCl X.left ℓ E
  let χ := coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E.1) X.left
  have h : φ ≫ ψ = χ := by
    rw [← coefficientMap_comp,
      Profinite.padicIntegersRingObjToContinuousMapRingObj_comp_padicSubfieldRingObjToPadicAlgCl]
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)).ι
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((boundedConstructibleToPadicAlgClCompatibility X.left ℓ E).app _ ≪≫
      (derivedExtendScalarsToPadicAlgCl X.left ℓ E).mapIso
        ((boundedConstructibleExtendScalarsCompatibility X.left ℓ E).app _) ≪≫
      ((Mod.derivedExtendScalarsCompIso φ ψ χ h).app _).symm ≪≫
      ((Mod.extendScalars χ).leftDerivedFunctor).mapIso ((ι.commShiftIso n).app _) ≪≫
      (((Mod.extendScalars χ).leftDerivedFunctor).commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso (Functor.leftDerivedFunctorSingleFunctorIsoOfFlat _
          (isLocallyFree_integralTateTwistNat ℓ E.1 X.hom d).flat ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (extendScalarsIntegralTateTwistNatIso X.left ℓ E.1 d)))

end AlgebraicGeometry.ProEtale.CondensedRing
