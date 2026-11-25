/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessPadicIntegers

/-!

# Deligne's finiteness theorem for nearby cycles with `ℚ̄_ℓ`-coefficients

Over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the
geometric nearby cycles of the standard model of `𝔸ⁿ_S` carry bounded constructible
`ℚ̄_ℓ`-complexes to bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`; SGA 4½,
[Th. finitude], Thm. 3.2, for `ℚ̄_ℓ`-coefficients as in Bhatt–Scholze §6.8). It is deduced from the
case of the finite coefficients `𝔽_E = 𝒪_E/ϖ`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`):

* a bounded constructible `ℚ̄_ℓ`-complex `B` has an integral model: `B ≅ ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} K₀`
  for a derived complete bounded constructible `𝒪_E`-complex `K₀`
  (`ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`);
* the nearby cycles commute with these extensions of scalars on bounded below complexes
  (`NearbyCyclesModel.nonempty_extendScalars_nearbyCycles_iso`, from the pullbacks and from
  `Rj_*`), so `Ψ B ≅ ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Ψ K₀` and `𝔽_E ⊗ᴸ Ψ K₀ ≅ Ψ (𝔽_E ⊗ᴸ K₀)`;
* `Ψ K₀` is derived complete (pullbacks and pushforwards preserve derived completeness) and its
  reduction `Ψ (𝔽_E ⊗ᴸ K₀)` is bounded constructible by the finite-coefficient theorem, so `Ψ K₀`
  is bounded constructible by the integral criterion
  (`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`), and so is `Ψ B`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

-- the extension of scalars and the pushforward comparison at concrete models
/-- **From `𝒪_E` to `E`**: the nearby cycles of `E ⊗ᴸ_{𝒪_E} K₀`, for a bounded constructible
`𝒪_E`-complex `K₀` on `𝔸ⁿ_S`, are bounded constructible: they are `E ⊗ᴸ_{𝒪_E} Ψ K₀`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj_padicSubfield (n : ℕ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
        (affineSpaceModel k' n).total))}
    (hK₀ : boundedConstructible _ K₀) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.continuousMapRingObj E.1)).obj
        ((L(Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          (affineSpaceModel k' n).total))).obj K₀)) := by
  let M := (affineSpaceModel k' n).geometric
  have : QuasiCompact M.j := inferInstanceAs
    (QuasiCompact (pullback.fst (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') (traitGenericPoint k')))
  have : QuasiSeparated M.j := inferInstanceAs
    (QuasiSeparated (pullback.fst (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')
      (traitGenericPoint k')))
  obtain ⟨m, hm⟩ := hK₀.1.1
  have : K₀.IsGE m := hm
  have h𝒪 := boundedConstructible_nearbyCycles_affineSpace_obj_padicIntegers n E hK₀
  have hGE₁ := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) M.ε K₀ m
  have hpush₁ := isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E M.j
    ((L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀) m
  obtain ⟨e₁⟩ := nonempty_extendScalars_nearbyCycles_iso
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) M K₀
    (asIso ((derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) M.j).app _))
  have hE := boundedConstructible_derivedExtendScalars_obj _ ℓ E ⟨_, h𝒪⟩
  exact (boundedConstructible _).prop_of_iso e₁ (by exact_mod_proofs hE)

-- the extension of scalars and the pushforward comparison at concrete models
omit [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)] in
/-- **From `E` to `ℚ̄_ℓ`**: if the nearby cycles of a bounded below `E`-complex `K₁` on `𝔸ⁿ_S` are
bounded constructible, so are those of `ℚ̄_ℓ ⊗ᴸ_E K₁`: they are `ℚ̄_ℓ ⊗ᴸ_E Ψ K₁`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj_padicAlgCl_of_padicSubfield (n : ℕ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₁ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj E.1)
        (affineSpaceModel k' n).total))} (m : ℤ) [K₁.IsGE m]
    (hK₁ : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.continuousMapRingObj E.1)).obj
        K₁)) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((L(Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          (affineSpaceModel k' n).total))).obj K₁)) := by
  let M := (affineSpaceModel k' n).geometric
  have : QuasiCompact M.j := inferInstanceAs
    (QuasiCompact (pullback.fst (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') (traitGenericPoint k')))
  have : QuasiSeparated M.j := inferInstanceAs
    (QuasiSeparated (pullback.fst (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')
      (traitGenericPoint k')))
  have hGE₂ := isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj E.1) M.ε K₁ m
  have hpush₂ := isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E M.j
    ((L((M.ε)^*⟦Profinite.continuousMapRingObj E.1⟧)).obj K₁) m
  obtain ⟨e₂⟩ := nonempty_extendScalars_nearbyCycles_iso
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) M K₁
    (asIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) M.j).app _))
  have hℚ := boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj _ ℓ E ⟨_, hK₁⟩
  exact (boundedConstructible _).prop_of_iso e₂ (by exact_mod_proofs hℚ)

/-- **Deligne's finiteness theorem on `𝔸ⁿ_S` with `ℚ̄_ℓ`-coefficients, from integral models**
(SGA 4½, [Th. finitude], Thm. 3.2; Bhatt–Scholze §6.8): over the strictly henselian trait
`S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the geometric nearby cycles of the
standard model of `𝔸ⁿ_S` carry bounded constructible `ℚ̄_ℓ`-complexes to bounded constructible
complexes. A bounded constructible `B` is `ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} K₀` for a bounded constructible
`𝒪_E`-complex `K₀`
(`ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`), and the nearby cycles
commute with the two extensions of scalars
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_padicSubfield`,
`boundedConstructible_nearbyCycles_affineSpace_obj_padicAlgCl_of_padicSubfield`). -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj_of_integral (n : ℕ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (affineSpaceModel k' n).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  obtain ⟨E, K₀, m, -, hm, hK₀, ⟨e⟩⟩ := exists_derivedCompleteIntegers_iso_integralModel ℓ hB
  have : K₀.IsGE m := hm
  have : ((L(Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      (affineSpaceModel k' n).total))).obj K₀).IsGE m :=
    isGE_leftDerivedFunctor_extendScalars_obj _ K₀ m
  have h := boundedConstructible_nearbyCycles_affineSpace_obj_padicAlgCl_of_padicSubfield n E m
    (boundedConstructible_nearbyCycles_affineSpace_obj_padicSubfield n E hK₀)
  exact (boundedConstructible _).prop_of_iso
    (((affineSpaceModel k' n).geometric.nearbyCycles _).mapIso e) h

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
