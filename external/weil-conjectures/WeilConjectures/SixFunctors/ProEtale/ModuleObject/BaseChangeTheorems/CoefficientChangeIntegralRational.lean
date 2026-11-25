/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeCubeBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceProof
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.Tactic.ExactModProofs

/-!
# The base-change morphism and the coefficient change `𝒪_E ⟶ E`

For a commutative square of schemes separated and of finite type over `k` and a bounded
constructible `𝒪_E`-complex `K₀`, the extension of scalars `E ⊗ᴸ_{𝒪_E} BC_sq(K₀)` of the integral
base-change morphism and the base-change morphism of `Dᵇc(-)⟦E⟧` at `E ⊗ᴸ_{𝒪_E} K₀` are isomorphic
arrows
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational`).
This combines the transfer of base-change morphisms along a flat coefficient change
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_extendScalars`), the
coherence of (Pull) with composition (`ProEtale.CondensedRing.derivedPullIso_hom_app_comp`) and the
invertibility of (Push) on bounded below complexes
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- The coherence `DerivedPullIsoCompCoherence a` of (Pull) with composition holds for every flat
coefficient change (`derivedPullIso_hom_app_comp`). -/
theorem derivedPullIsoCompCoherence {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] :
    DerivedPullIsoCompCoherence a :=
  fun _ _ _ p q M ↦ derivedPullIso_hom_app_comp Λ p q a M

/-- The derived pullback of module objects, being exact, preserves bounded below complexes. -/
lemma isGE_leftDerivedUpperStar_obj (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (n : ℤ) [K.IsGE n] : ((g)^*⟦Λ⟧.leftDerivedFunctor.obj K).IsGE n := by
  have := ((g)^*⟦Λ⟧).isGE_mapDerivedCategory_obj K n
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app K).symm n

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Blueprint `lemma-naturality-pasting-comparison`, its last assertion for the localization
`𝒪_E ⟶ E` of `proposition-six-operations-change-coefficients`: the extension of scalars
`E ⊗ᴸ_{𝒪_E} BC_sq(K₀)` of the integral base-change morphism and the base-change morphism of
`Dᵇc(-)⟦E⟧` at `E ⊗ᴸ_{𝒪_E} K₀` are isomorphic arrows. -/
theorem nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational
    (sq : CommSq g' f' f g) (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    Nonempty (Arrow.mk ((boundedConstructibleExtendScalars Y'.left ℓ E).map
        ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E.1 sq).app K₀)) ≅
      Arrow.mk ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq).app
        ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀))) := by
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
  have ha := K₀.property.1.1.choose_spec
  let a := K₀.property.1.1.choose
  have : K₀.obj.IsGE a := ha
  have : ((g'.left)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj
      K₀.obj).IsGE a := isGE_leftDerivedUpperStar_obj _ g'.left K₀.obj a
  have H : DerivedPullIsoCompCoherence (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) :=
    derivedPullIsoCompCoherence _
  have key := nonempty_arrowIso_boundedConstructibleBaseChange_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) ℓ H sq
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E.1 f K)
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E.1 f' K)
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K)
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f' K)
    (fun K ↦ boundedConstructible_derivedExtendScalars_obj X.left ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalars_obj Y'.left ℓ E K)
    (PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E.1 sq)
    (PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight ℓ E.1 sq)
    (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq)
    (ContinuousMapRingObj.boundedConstructibleBaseChange_eq_exchangeRight ℓ E sq) K₀ ?h₁ ?h₂
  -- Compare the concrete and generic coefficient instances by proof irrelevance without
  -- unfolding the surrounding derived functors during unification.
  case h₁ => exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f.left K₀.obj a
  case h₂ =>
    exact_mod_proofs isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E f'.left
      ((g'.left)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀.obj) a
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing
