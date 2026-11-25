/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgClOfSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicSubfield
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgClOfSubfieldAux
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicSubfieldAux

/-!
# The `ℚ̄_ℓ` projection formula from the integral one

Let `p : X ⟶ Y` be a morphism of separated `k`-schemes of finite type, `ℓ ≠ char k`. If the
projection map `Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism for bounded constructible
`𝒪_E`-complexes, for every finite subextension `E ⊆ ℚ̄_ℓ`, then it is an isomorphism for bounded
constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.isIso_projectionMap_padicAlgClRingObj_of_integral`, blueprint
`proposition-proper-direct-image-constructible-complexes` (3)).

Bounded constructible `ℚ̄_ℓ`-complexes `K` and `M` have integral models `K₀`, `M₀` over a common
`𝒪_E` (`ProEtale.exists_padicAlgCl_iso_integralModel_pair`): `K ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)`.
The extensions of scalars `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ` are flat, and the (Push) comparisons
`T Rp_* ⟶ Rp_* T` are isomorphisms on bounded below objects
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicSubfield_of_padicIntegers`,
`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield`), so the
projection formula is transported along both of them
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_extendScalars`).

The concrete coefficient rings carry instance arguments elaborated in different contexts, which
differ by proofs only; comparing them with the unifier times out, and the tactic
`exact_mod_proofs` bridges them.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- the concrete coefficient rings are unfolded when comparing elaborations from different files
/-- **The `ℚ̄_ℓ` projection formula from the integral one**: if the projection map
`Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism on bounded constructible `𝒪_E`-complexes for
every finite subextension `E ⊆ ℚ̄_ℓ`, it is an isomorphism on bounded constructible
`ℚ̄_ℓ`-complexes. -/
theorem isIso_projectionMap_padicAlgClRingObj_of_integral (p : X ⟶ Y)
    (h : ∀ (E : FiniteIntermediateField ℓ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)))
      (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y.left))),
      boundedConstructible _ K → boundedConstructible _ M →
        IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E.1) p.left).app K).app M))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hK : boundedConstructible _ K) (hM : boundedConstructible _ M) :
    IsIso (((projectionMap (Profinite.padicAlgClRingObj ℓ) p.left).app K).app M) := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have : QuasiCompact p.left :=
    have : QuasiCompact (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
    QuasiCompact.of_comp p.left Y.hom
  have : QuasiSeparated p.left :=
    have : QuasiSeparated (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
    QuasiSeparated.of_comp p.left Y.hom
  obtain ⟨E, K₀, M₀, eK, eM⟩ :=
    exists_derivedExtendScalars_iso_integralModel_pair X.left Y.left ℓ ⟨K, hK⟩ ⟨M, hM⟩
  -- bounded below complexes
  have hKM₀ := (PadicIntegersRingObj.isMonoidal_boundedConstructible ℓ E.1 X).toTensorLE.prop_tensor
    _ _ K₀.property (boundedConstructible_leftDerivedUpperStar_obj _ ℓ p M₀)
  have hK₁ := boundedConstructible_derivedExtendScalars_obj X.left ℓ E K₀
  have hM₁ := boundedConstructible_derivedExtendScalars_obj Y.left ℓ E M₀
  have hKM₁ := (ContinuousMapRingObj.isMonoidal_boundedConstructible ℓ E X).toTensorLE.prop_tensor
    _ _ hK₁ (boundedConstructible_leftDerivedUpperStar_obj _ ℓ p ⟨_, hM₁⟩)
  -- the changes of coefficients `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`
  have e₁ := isIso_projectionMap_app_app_padicSubfield_of_padicIntegers_aux ℓ E p.left K₀.obj
    M₀.obj _ _ (exists_isGE_of_boundedConstructible K₀.property).choose_spec
    (by exact_mod_proofs (exists_isGE_of_boundedConstructible hKM₀).choose_spec)
    (by exact_mod_proofs h E K₀.obj M₀.obj K₀.property M₀.property)
  have e₂ := isIso_projectionMap_app_app_padicAlgCl_of_padicSubfield_aux ℓ E p.left
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      X.left)).leftDerivedFunctor.obj K₀.obj)
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      Y.left)).leftDerivedFunctor.obj M₀.obj)
    (exists_isGE_of_boundedConstructible hK₁).choose
    (exists_isGE_of_boundedConstructible hKM₁).choose
    (by exact_mod_proofs (exists_isGE_of_boundedConstructible hK₁).choose_spec)
    (by exact_mod_proofs (exists_isGE_of_boundedConstructible hKM₁).choose_spec)
    (by exact_mod_proofs e₁)
  have e₃ := @NatTrans.isIso_app_app_of_iso _ _ _ _ _ _ _ _
    (projectionMap (Profinite.padicAlgClRingObj ℓ) p.left) _ _ _ _ eK.some eM.some
    (by exact_mod_proofs e₂)
  exact_mod_proofs e₃

end AlgebraicGeometry.ProEtale.CondensedRing
