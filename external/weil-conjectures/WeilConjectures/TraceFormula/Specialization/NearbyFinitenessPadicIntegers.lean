/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.IntegralModelAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterionResidue

/-!

# Deligne's finiteness theorem for nearby cycles with `𝒪_E`-coefficients

The nearby cycles commute with extension of scalars along a coefficient change `Λ ⟶ Λ'` at
complexes where `Rj_*` does (`NearbyCyclesModel.nonempty_extendScalars_nearbyCycles_iso`). Over the
strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the nearby cycles
of the standard model of `𝔸ⁿ_S` carry bounded constructible `𝒪_E`-complexes `K₀` to bounded
constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_padicIntegers`): `Ψ K₀` is
derived complete, and its reduction `𝔽_E ⊗ᴸ Ψ K₀ ≅ Ψ (𝔽_E ⊗ᴸ K₀)` is bounded constructible by the
finite-coefficient theorem
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`), so the integral
criterion applies (`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`).
SGA 4½, [Th. finitude], Thm. 3.2; Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- **Nearby cycles commute with extension of scalars** along a coefficient change `a : Λ ⟶ Λ'`,
at a complex `K` at which `Rj_*` commutes with the extension of scalars: then
`Λ' ⊗ᴸ Ψ_M K ≅ Ψ_M (Λ' ⊗ᴸ K)`, the pullbacks commuting with extension of scalars
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`). -/
lemma nonempty_extendScalars_nearbyCycles_iso {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (e : (L(Mod.extendScalars (coefficientMap a M.total))).obj
        ((R((M.j)_*⟦Λ⟧)).obj ((L((M.ε)^*⟦Λ⟧)).obj K)) ≅
      (R((M.j)_*⟦Λ'⟧)).obj ((L(Mod.extendScalars (coefficientMap a M.generic))).obj
        ((L((M.ε)^*⟦Λ⟧)).obj K))) :
    Nonempty ((L(Mod.extendScalars (coefficientMap a X'))).obj ((M.nearbyCycles Λ).obj K) ≅
      (M.nearbyCycles Λ').obj ((L(Mod.extendScalars (coefficientMap a X))).obj K)) := by
  exact ⟨(derivedUpperStarExtendScalarsIso a M.i).app _ ≪≫
    (L((M.i)^*⟦Λ'⟧)).mapIso
      (e ≪≫ (R((M.j)_*⟦Λ'⟧)).mapIso ((derivedUpperStarExtendScalarsIso a M.ε).app K))⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

omit [IsSepClosed k'] in
/-- The exponent `ℓ` of the residue field `𝔽_E` is invertible in a field `k'` of characteristic
different from `ℓ`. -/
lemma hasInvertibleExponent_integersResidueField (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    HasInvertibleExponent (ULift.{u + 1} (integersResidueField ℓ E.1)) (Spec (.of k')) := by
  have hk : (ℓ : k') ≠ 0 := by
    intro h
    rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k' ℓ).1 h) with h₁ | h₁
    · exact CharP.ringChar_ne_one h₁
    · exact (Fact.out : ringChar k' ≠ ℓ) h₁
  exact ⟨ℓ, (Fact.out : ℓ.Prime).pos,
    ULift.ext (by simpa using natCast_eq_zero_integersResidueField ℓ E.1),
    by simpa using (Ne.isUnit hk).map (Scheme.ΓSpecIso (.of k')).inv.hom⟩

/-- **Deligne's finiteness theorem on `𝔸ⁿ_S` with `𝔽_E`-coefficients, for reductions**: the
nearby cycles of the reduction `𝔽_E ⊗ᴸ K₀` of a bounded constructible `𝒪_E`-complex `K₀` on
`𝔸ⁿ_S` are bounded constructible, by the finite-coefficient theorem
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`). -/
theorem boundedConstructible_nearbyCycles_affineSpace_extendScalars_residueField (n : ℕ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
        (affineSpaceModel k' n).total))}
    (hK₀ : boundedConstructible _ K₀) :
    boundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles
        (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))).obj
        ((L(Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
          (affineSpaceModel k' n).total))).obj K₀)) := by
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have := hasInvertibleExponent_integersResidueField (k' := k') E
  obtain ⟨p, hp, hpℓ, hpk⟩ := exists_prime_ne_dvd_of_natCast_eq_zero k'
    (Fact.out : ringChar k' ≠ ℓ)
  have : Fact p.Prime := ⟨hp⟩
  have h := boundedConstructible_derivedExtendScalars_residueField _ ℓ E K₀ hK₀
  exact boundedConstructible_nearbyCycles_affineSpace_obj_of_finite (integersResidueField ℓ E.1)
    n hpk (isUnit_natCast_integersResidueField E.1 hp hpℓ) (by exact_mod_proofs h)

-- the three extensions of scalars and the pushforward comparison at concrete models
/-- **Deligne's finiteness theorem on `𝔸ⁿ_S` with `𝒪_E`-coefficients**: the nearby cycles of a
bounded constructible `𝒪_E`-complex `K₀` on `𝔸ⁿ_S` are bounded constructible. They are derived
complete, and their reduction `𝔽_E ⊗ᴸ Ψ K₀ ≅ Ψ (𝔽_E ⊗ᴸ K₀)` is bounded constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_extendScalars_residueField`), so
the integral criterion applies
(`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`). -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj_padicIntegers (n : ℕ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
        (affineSpaceModel k' n).total))}
    (hK₀ : boundedConstructible _ K₀) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles
        (Profinite.padicIntegersRingObj ℓ E.1)).obj K₀) := by
  let M := (affineSpaceModel k' n).geometric
  have : IsNoetherian (affineSpaceModel k' n).total :=
    (isTraitModel_affineSpaceModel (k' := k') n).isNoetherian_total
  have : IsNoetherian M.total := ‹IsNoetherian (affineSpaceModel k' n).total›
  have : IsNoetherian (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left :=
    isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel n)
  have : LocallyOfFiniteType (pullback.snd (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')
      (traitGenericPoint k')) := inferInstance
  have : IsNoetherian M.generic := isNoetherian_of_locallyOfFiniteType
    (pullback.snd (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') (traitGenericPoint k'))
  obtain ⟨m, hm⟩ := hK₀.1.1
  have : K₀.IsGE m := hm
  have hGE := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) M.ε K₀ m
  have hc := derivedCompleteIntegers_of_boundedConstructible hK₀
  have hcΨ := derivedCompleteIntegers_leftDerivedUpperStar_obj M.i
    (derivedCompleteIntegers_rightDerivedLowerStar_obj M.j
      (derivedCompleteIntegers_leftDerivedUpperStar_obj M.ε hc))
  have hpush := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E.1 M.j
    ((L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀) m
  obtain ⟨e⟩ := nonempty_extendScalars_nearbyCycles_iso
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1) M K₀
    (asIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) M.j).app _))
  have hred := boundedConstructible_nearbyCycles_affineSpace_extendScalars_residueField n E hK₀
  have h₁ := (boundedConstructible _).prop_of_iso e.symm hred
  exact boundedConstructible_of_derivedCompleteIntegers_of_residueField hcΨ (by exact_mod_proofs h₁)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
