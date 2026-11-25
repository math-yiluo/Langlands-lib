/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.BoundedConstructibleFinite
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

/-!

# Deligne's finiteness theorem for the nearby cycles of the trait, finite coefficients

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait, with
geometric generic point `j : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`, and let `T` be a
finite discrete ring. The geometric nearby cycles `Li^* Rj_* Lj^*` of `S` carry bounded
constructible complexes of `T̲`-modules on `S` to bounded constructible complexes on `Spec k'`
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj_of_finite`). This is the
case `𝔸⁰_S = S` of Deligne's finiteness theorem for nearby cycles (SGA 4½, [Th. finitude],
Thm. 3.2), for finite coefficients.

The proof is that of the `ℚ̄_ℓ` case
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj`), whose ingredients are
stated for an arbitrary coefficient ring; the dévissage uses that bounded constructible complexes
of `T̲`-modules form a triangulated subcategory
(`ProEtale.CondensedRing.isTriangulated_boundedConstructible_of_finite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k' : Type u) [Field k'] [IsSepClosed k']
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [DiscreteTopology T] [Finite T] in
/-- For a constructible sheaf `M` of `T̲`-modules on the geometric generic point
`Spec Ω` of the trait, `Li^* Rj_* (M[0]) = (i^* j_* M)[0]` is bounded constructible on the closed
point: `M` is finitely presented, `i^*` kills `Rⁿ j_* M` for `n > 0`, and `i^* j_*` preserves
finitely presented modules. -/
theorem boundedConstructible_traitNearby_singleFunctor_obj_of_finite
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) (Spec (.of (traitGenericField k'))))}
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj T) (Spec (.of (traitGenericField k')))) M) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) (Spec (.of k')))
      ((L((traitClosedPoint k')^*⟦Profinite.continuousMapRingObj T⟧)).obj
        ((R((traitGenericPoint k')_*⟦Profinite.continuousMapRingObj T⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  set Λ := Profinite.continuousMapRingObj T
  have hfp : Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of (traitGenericField k')))) M :=
    (isFinitelyPresented_upperStar_of_isConstructibleModuleObject Λ (Field.toIsField _)
      IsField.isSepClosed_toField hM
      (𝟙 _)).of_iso ((upperStarId Λ _).app M)
  have hGE : ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsGE 0 :=
    (traitGenericPoint k')_*⟦Λ⟧.isGE_rightDerivedFunctor_obj_singleFunctor M
  have hpos : ∀ n : ℤ, 0 < n → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((L((traitClosedPoint k')^*⟦Λ⟧)).obj ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    exact (isZero_upperStar_traitClosedPoint_obj_rightDerived_of_pos Λ k' m (by omega) M).of_iso
      (homologyTraitNearbyObjSingleIso Λ k' m M)
  have hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((L((traitClosedPoint k')^*⟦Λ⟧)).obj ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
    intro n hn
    refine ((traitClosedPoint k')^*⟦Λ⟧.map_isZero
      (DerivedCategory.isZero_of_isGE ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) 0 n hn)).of_iso ?_
    exact (DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ (traitClosedPoint k')).app _) ≪≫
      ((traitClosedPoint k')^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm.app _
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨0, 0, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · rcases hi with hi | hi
    · exact hneg i hi
    · exact hpos i hi
  · rcases lt_trichotomy n 0 with hn | rfl | hn
    · exact isConstructibleModuleObject_of_isZero _ (hneg n hn)
    · refine IsConstructibleModuleObject.of_iso ?_
        (isConstructibleModuleObject_of_isFinitelyPresented Λ
          (isFinitelyPresented_traitNearbyFunctor_obj Λ k' hfp))
      exact ((traitClosedPoint k')^*⟦Λ⟧.mapIso
          ((traitGenericPoint k')_*⟦Λ⟧.rightDerivedZeroIsoSelf.app M).symm) ≪≫
        (homologyTraitNearbyObjSingleIso Λ k' 0 M).symm
    · exact isConstructibleModuleObject_of_isZero _ (hpos n hn)

/-- **Deligne's finiteness theorem for the nearby cycles of the trait, finite coefficients** (the
case `𝔸⁰_S = S` of SGA 4½, [Th. finitude], Thm. 3.2): for a finite discrete ring `T`, the
geometric nearby cycles `Li^* Rj_* Lj^*` of the strictly henselian trait `S = Spec k'⟦t⟧` carry
bounded constructible complexes of `T̲`-modules on `S` to bounded constructible complexes on its
closed point. `Lj^* B` is bounded constructible on `Spec Ω`, and by dévissage it suffices to treat
a constructible sheaf on `Spec Ω` placed in degree `0`
(`ProEtale.CondensedRing.boundedConstructible_traitNearby_singleFunctor_obj_of_finite`). -/
theorem boundedConstructible_traitNearbyCycles_obj_of_finite
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (trait k')) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) (trait k')))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) (Spec (.of k')))
      ((L((traitClosedPoint k')^*⟦Profinite.continuousMapRingObj T⟧)).obj
        ((R((traitGenericPoint k')_*⟦Profinite.continuousMapRingObj T⟧)).obj
          ((L((traitGenericPoint k')^*⟦Profinite.continuousMapRingObj T⟧)).obj B))) :=
  boundedConstructible_obj_of_forall_singleFunctor
    (Φ := R((traitGenericPoint k')_*⟦Profinite.continuousMapRingObj T⟧) ⋙
      L((traitClosedPoint k')^*⟦Profinite.continuousMapRingObj T⟧))
    (fun _ hF ↦ boundedConstructible_traitNearby_singleFunctor_obj_of_finite k' T hF)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (traitGenericPoint k') B hB)

namespace NearbyCyclesModel

/-- **Deligne's finiteness theorem for the trait itself, finite coefficients**: the nearby cycles
of the trait, as a model of itself, preserve bounded constructible complexes of `T̲`-modules
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj_of_finite`). -/
theorem preservesBoundedConstructible_traitSelfModel_of_finite :
    (traitSelfModel k').PreservesBoundedConstructible (Profinite.continuousMapRingObj T) :=
  fun _ hB ↦ boundedConstructible_traitNearbyCycles_obj_of_finite k' T hB

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
