/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.Tactic.ExactModProofs

/-!
# The base-change morphism and the coefficient change `E ⟶ ℚ̄_ℓ`

For a commutative square of schemes separated and of finite type over `k` and a bounded
constructible `E`-complex `M`, the extension of scalars `ℚ̄_ℓ ⊗ᴸ_E BC_sq(M)` and the base-change
morphism of `Dᵇc(-)⟦ℚ̄_ℓ⟧` at `ℚ̄_ℓ ⊗ᴸ_E M` are isomorphic arrows
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_rationalToPadicAlgCl`),
given that (Push) for `E ⟶ ℚ̄_ℓ` is invertible on bounded below complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The rational stage of blueprint `lemma-naturality-pasting-comparison`, for the inclusion
`E ⟶ ℚ̄_ℓ`: given that (Push) for `E ⟶ ℚ̄_ℓ` is invertible on bounded below complexes along
quasi-compact quasi-separated morphisms, the extension of scalars `ℚ̄_ℓ ⊗ᴸ_E BC_sq(M)` and the
base-change morphism of `Dᵇc(-)⟦ℚ̄_ℓ⟧` at `ℚ̄_ℓ ⊗ᴸ_E M` are isomorphic arrows. -/
theorem nonempty_arrowIso_boundedConstructibleBaseChange_rationalToPadicAlgCl
    (hP : ∀ {A B : Scheme.{u}} (p : A ⟶ B) [QuasiCompact p] [QuasiSeparated p]
      (K : DerivedCategory (Mod (Sheaf (ProEt.topology A) Ab.{u + 1})
        (padicSubfieldRingObj A ℓ E))) (n : ℤ) [K.IsGE n],
      IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app K))
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible X.left ℓ E) :
    Nonempty (Arrow.mk ((constructibleToPadicAlgCl Y'.left ℓ E).map
        ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq).app M)) ≅
      Arrow.mk ((boundedConstructibleBaseChange ℓ sq).app
        ((constructibleToPadicAlgCl X.left ℓ E).obj M))) := by
  have : QuasiCompact f.left := by
    have : QuasiCompact (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact QuasiCompact.of_comp f.left Y.hom
  have : QuasiCompact f'.left := by
    have : QuasiCompact (f'.left ≫ Y'.hom) := by rw [Over.w f']; infer_instance
    exact QuasiCompact.of_comp f'.left Y'.hom
  have : QuasiSeparated f.left := by
    have : QuasiSeparated (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact QuasiSeparated.of_comp f.left Y.hom
  have : QuasiSeparated f'.left := by
    have : QuasiSeparated (f'.left ≫ Y'.hom) := by rw [Over.w f']; infer_instance
    exact QuasiSeparated.of_comp f'.left Y'.hom
  have hM := M.property.1.1
  obtain ⟨a, ha⟩ := hM
  have : M.obj.IsGE a := ha
  have : ((g'.left)^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj
      M.obj).IsGE a := isGE_leftDerivedUpperStar_obj _ g'.left M.obj a
  have H : DerivedPullIsoCompCoherence (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) :=
    derivedPullIsoCompCoherence _
  have key := nonempty_arrowIso_boundedConstructibleBaseChange_extendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ℓ H sq
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K)
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f' K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X.left ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj Y'.left ℓ E K)
    (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq)
    (ContinuousMapRingObj.boundedConstructibleBaseChange_eq_exchangeRight ℓ E sq)
    (boundedConstructibleBaseChange ℓ sq) (boundedConstructibleBaseChange_eq_exchangeRight ℓ sq)
    M ?h₁ ?h₂
  -- the instances of the transfer theorem differ from those on the concrete coefficient rings by
  -- proofs of `Precoherent Profinite`: compare the comparisons up to proofs, not by unification
  case h₁ => exact_mod_proofs hP f.left M.obj a
  case h₂ =>
    exact_mod_proofs (hP f'.left
      ((g'.left)^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj M.obj) a)
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing
