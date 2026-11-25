/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.TraceFormula.Specialization.FinitePointReflection
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases

/-!

# Nearby cycles of complexes supported on a closed subscheme finite over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait (`k'` separably closed, `ℓ ≠ char k'`) and
`c : D ⟶ 𝔸ⁿ_S` a closed immersion such that `p = c ≫ q : D ⟶ S` is finite, `q : 𝔸ⁿ_S ⟶ S` being
the structure map. For every bounded constructible `ℚ̄_ℓ`-complex `K` on `D`, the geometric
nearby cycles of `Rc_* K` are bounded constructible on the special fibre `𝔸ⁿ_s`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isFinite_comp`). This is the
case "`D` finite over the trait" of Deligne's finiteness theorem for nearby cycles (SGA 4½,
[Th. finitude], Thm. 3.2), generalizing
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp`.

The proof:
* by the proper exchange along `p`
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`),
  `Ψ_S (Rp_* K) ≅ Rp_{s*} Ψ_D K`, where `Rp_* K` is bounded constructible
  (`boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`)
  and the nearby cycles of the trait preserve bounded constructible complexes
  (`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`);
* the special fibre `p_s : D_s ⟶ Spec k'` is finite over the separably closed point `Spec k'`, so
  `Ψ_D K` is bounded constructible as soon as `Rp_{s*} Ψ_D K` is
  (`boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite`);
* by the proper exchange along `c`, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`, and `Rc_{s*}` preserves
  bounded constructible complexes.

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

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k').Prime] in
/-- **Nearby cycles of a complex supported on a closed subscheme finite over the trait**: if the
closed subscheme `c : D ⟶ 𝔸ⁿ_S` is finite over the trait `S`, then `Ψ (Rc_* K)` is bounded
constructible for every bounded constructible `K` on `D`. By the proper exchange along the finite
`p : D ⟶ S`, `Rp_{s*} Ψ_D K ≅ Ψ_S (Rp_* K)` is bounded constructible, hence so is `Ψ_D K`, the
special fibre `D_s` being finite over the separably closed point `Spec k'`; and by the proper
exchange along `c`, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_isFinite_comp (n : ℕ)
    {D : Scheme.{u}} (c : D ⟶ (affineSpaceModel k' n).total) [IsClosedImmersion c]
    (hcq : IsFinite (c ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')))
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
  let ψ : M.geometric.Hom (traitSelfModel k').geometric (c ≫ q)
      (pullback.snd (c ≫ q) (traitClosedPoint k')) :=
    { total := c ≫ q
      generic := pullback.snd (c ≫ q) (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  have : IsFinite (c ≫ q) := hcq
  have hiso :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric (X' := traitStdSpecialFibre (c ≫ q))
      (Y' := Over.mk (𝟙 (Spec (.of k')))) (M := M) (N := traitSelfModel k') ψ
      (isTraitModel_traitStdModel _) (isTraitModel_traitSelfModel k') rfl hj.flip hi K hK
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have h₁ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of k')))
      (((traitSelfModel k').geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c ≫ q)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) :=
    preservesBoundedConstructible_traitSelfModel k' _
      (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj ℓ
        (traitToBase k' k') (c ≫ q) K hK)
  have h₂ := (boundedConstructible _).prop_of_iso (@asIso _ _ _ _ _ hiso) h₁
  have hΨ := boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite _
    (pullback.snd (c ≫ q) (traitClosedPoint k')) _ h₂
  let φ := traitStdHom q hj hi c rfl
  have : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_geometric φ (isTraitModel_traitStdModel _)
      (isTraitModel_affineSpaceModel n) rfl
      (isPullback_traitStdHom_generic q hj hi c rfl) (isPullback_traitStdHom_special q hi c rfl)
      K hK
  have := isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel (k' := k') n)
  have := isClosedImmersion_traitStdSpecialHom q hi c rfl
  exact (boundedConstructible _).prop_of_iso
    (asIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K)).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ _ hΨ)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
