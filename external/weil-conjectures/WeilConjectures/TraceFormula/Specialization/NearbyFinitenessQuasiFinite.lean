/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessFinite

/-!

# Nearby cycles of complexes supported on a closed subscheme quasi-finite over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait (`k'` separably closed, `ℓ ≠ char k'`) and
`c : D ⟶ 𝔸ⁿ_S` a closed immersion such that `p = c ≫ q : D ⟶ S` is locally quasi-finite, `q` being
the structure map of `𝔸ⁿ_S`. For every bounded constructible `ℚ̄_ℓ`-complex `K` on `D`, the
geometric nearby cycles of `Rc_* K` are bounded constructible on the special fibre `𝔸ⁿ_s`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_locallyQuasiFinite_comp`).
This generalizes the finite case
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isFinite_comp`.

The proof:
* for a scheme `p̄ : T ⟶ S` finite over the trait, the geometric nearby cycles of its standard
  model preserve bounded constructible complexes
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_traitStdModel_of_isFinite`): by
  the proper exchange along `p̄`, `Rp̄_{s*} Ψ_T B ≅ Ψ_S (Rp̄_* B)`, and `T_s` is finite over the
  separably closed point `Spec k'`;
* by Zariski's main theorem
  (`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`), `p`
  factors as an open immersion `j : D ⟶ T` followed by a finite `p̄ : T ⟶ S`. Nearby cycles
  commute with the open immersion `j`
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`), so
  `Ψ_D K ≅ Ψ_D (Lj^* j_! K) ≅ Lj_s^* Ψ_T (j_! K)` is bounded constructible
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_traitStdModel_of_isOpenImmersion`);
* by the proper exchange along `c`, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`.

The proper exchange is `sorry`ed upstream
(`WeilConjectures.TraceFormula.Specialization.NearbyProperExchange`), as is the finiteness of
proper direct images.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k').Prime] in
/-- **Nearby cycles of a scheme finite over the trait**: for a finite morphism `p : T ⟶ S` to the
trait, the geometric nearby cycles of the standard model of `T` preserve bounded constructible
complexes. By the proper exchange along `p`, `Rp_{s*} Ψ_T B ≅ Ψ_S (Rp_* B)` is bounded
constructible, hence so is `Ψ_T B`, the special fibre `T_s` being finite over the separably closed
point `Spec k'`. -/
theorem boundedConstructible_geometricNearbyCycles_traitStdModel_of_isFinite {T : Scheme.{u}}
    (p : T ⟶ trait k') [IsFinite p]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre p).left)
      (((traitStdModel p).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  let M := traitStdModel p
  have hj : IsPullback M.j (pullback.snd p (traitGenericPoint k')) p (traitGenericPoint k') :=
    IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre p).hom p (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let ψ : M.geometric.Hom (traitSelfModel k').geometric p
      (pullback.snd p (traitClosedPoint k')) :=
    { total := p
      generic := pullback.snd p (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  have hiso :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric (X' := traitStdSpecialFibre p)
      (Y' := Over.mk (𝟙 (Spec (.of k')))) (M := M) (N := traitSelfModel k') ψ
      (isTraitModel_traitStdModel _) (isTraitModel_traitSelfModel k') rfl hj.flip hi B hB
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have h₁ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of k')))
      (((traitSelfModel k').geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B)) :=
    preservesBoundedConstructible_traitSelfModel k' _
      (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj ℓ
        (traitToBase k' k') p B hB)
  have h₂ := (boundedConstructible _).prop_of_iso (@asIso _ _ _ _ _ hiso) h₁
  exact boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite _
    (pullback.snd p (traitClosedPoint k')) _ h₂

omit [Fact (ringChar k').Prime] in
/-- **Nearby cycles of a scheme open in a scheme finite over the trait**: if `p : D ⟶ S` factors
as an open immersion `j : D ⟶ T` followed by a finite morphism `p̄ : T ⟶ S`, the geometric nearby
cycles of the standard model of `D` preserve bounded constructible complexes. Nearby cycles commute
with the open immersion `j`, so `Ψ_D K ≅ Ψ_D (Lj^* j_! K) ≅ Lj_s^* Ψ_T (j_! K)`, and `j_! K` is
bounded constructible. -/
theorem boundedConstructible_geometricNearbyCycles_traitStdModel_of_isOpenImmersion
    {D T : Scheme.{u}} (p : D ⟶ trait k') (j : D ⟶ T) [IsOpenImmersion j] (p' : T ⟶ trait k')
    [IsFinite p'] (hjp : j ≫ p' = p)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre p).left)
      (((traitStdModel p).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj K) := by
  let M := traitStdModel p
  have hj : IsPullback M.j (pullback.snd p (traitGenericPoint k')) p (traitGenericPoint k') :=
    IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre p).hom p (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  let φ := traitStdHom p' hj hi j hjp
  have : IsOpenImmersion φ.total := ‹IsOpenImmersion j›
  have := φ.isIso_pullbackExchange_of_isOpenImmersion (Profinite.padicAlgClRingObj ℓ)
    (isPullback_traitStdHom_generic p' hj hi j hjp)
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian p'
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p'
  have : IsNoetherian T := ⟨⟩
  have h₁ := boundedConstructible_geometricNearbyCycles_traitStdModel_of_isFinite p'
    (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj _ j K hK)
  have h₂ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
    (traitStdSpecialHom p' hi j hjp) _ h₁
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  refine (boundedConstructible _).prop_of_iso (asIso ((φ.pullbackExchange
    (Profinite.padicAlgClRingObj ℓ)).app _) ≪≫
      (M.geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _ j).app _ ≪≫
          (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) j).unit.app K)).symm)) h₂

omit [Fact (ringChar k').Prime] in
/-- **Nearby cycles of a complex supported on a closed subscheme quasi-finite over the trait**:
if the closed subscheme `c : D ⟶ 𝔸ⁿ_S` is locally quasi-finite over the trait `S`, then
`Ψ (Rc_* K)` is bounded constructible for every bounded constructible `K` on `D`. By Zariski's
main theorem, `D ⟶ S` factors as an open immersion followed by a finite morphism, so `Ψ_D K` is
bounded constructible
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_traitStdModel_of_isOpenImmersion`);
and by the proper exchange along `c`, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_locallyQuasiFinite_comp (n : ℕ)
    {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hcq : LocallyQuasiFinite (c ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D))}
    (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  let q := 𝔸(ULift.{u} (Fin n); trait k') ↘ trait k'
  let M := traitStdModel (c ≫ q)
  have hj : IsPullback M.j (pullback.snd (c ≫ q) (traitGenericPoint k')) (c ≫ q)
      (traitGenericPoint k') := IsPullback.of_hasPullback _ _
  have hi : IsPullback M.i (traitStdSpecialFibre (c ≫ q)).hom (c ≫ q) (traitClosedPoint k') :=
    IsPullback.of_hasPullback _ _
  have : LocallyQuasiFinite (c ≫ q) := hcq
  obtain ⟨T, j, p', _, -, _, hjp⟩ := (c ≫ q).exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have hΨ := boundedConstructible_geometricNearbyCycles_traitStdModel_of_isOpenImmersion
    (c ≫ q) j p' hjp hK
  let φ := traitStdHom q hj hi c rfl
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ (isTraitModel_traitStdModel _)
      (isTraitModel_affineSpaceModel n) rfl (isPullback_traitStdHom_generic q hj hi c rfl)
      (isPullback_traitStdHom_special q hi c rfl) K hK
  have := isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel (k' := k') n)
  have := isClosedImmersion_traitStdSpecialHom q hi c rfl
  exact (boundedConstructible _).prop_of_iso
    (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K)).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ _ hΨ)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
