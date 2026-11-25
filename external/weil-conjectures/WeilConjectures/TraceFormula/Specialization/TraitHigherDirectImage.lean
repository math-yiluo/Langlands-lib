/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.WeaklyContractibleSections
public import WeilConjectures.TraceFormula.Specialization.TraitClosedLift
public import WeilConjectures.TraceFormula.Specialization.TraitGenericFibre

/-!

# Higher direct images from the geometric generic point of the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait,
`i : Spec k' ⟶ S` its closed point and `j : Spec Ω ⟶ S` its geometric generic point. For a
commutative condensed ring `Λ`, the higher direct images `Rⁿ j_* (j^* Λ_S)`, `n > 0`, vanish
after `i^*` (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_rightDerived`).

It suffices to check this on sections over the henselian lifts `W = Spec H_{k'⟦t⟧}(C̄)` of the
w-contractible ind-étale `k'`-algebras `C̄`, which compute the sections of `i^*`
(`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_of_forall`). Such a `W` is weakly
contractible, and so is its geometric generic fibre `W ×_S Spec Ω`
(`ProEtale.isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec`). Sections over a
weakly contractible object are exact, so the sections of `Rⁿ j_* N` over `W` are the cohomology
of the sections over `W ×_S Spec Ω` of an injective resolution of `N`, which vanishes in
positive degrees.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

/-- After restriction to the closed point of the trait, the higher direct images
`Rⁿ j_* (j^* Λ_S)`, `n > 0`, along the geometric generic point `j : Spec Ω ⟶ S` vanish. -/
theorem isZero_upperStar_traitClosedPoint_obj_rightDerived (n : ℕ) (hn : 0 < n) :
    IsZero ((traitClosedPoint k')^*⟦Λ⟧.obj
      (((traitGenericPoint k')_*⟦Λ⟧.rightDerived n).obj
        ((traitGenericPoint k')^*⟦Λ⟧.obj (𝟙_ _)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine isZero_upperStar_traitClosedPoint_obj_of_forall Λ _ fun C _ _ _ _ _ hC ↦ ?_
  have hW : (ProEt.topology (trait k')).IsWeaklyContractible.{u + 1} (traitClosedLift C) :=
    Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction
      (R := CommRingCat.of (Algebra.ClosedLift (PowerSeries k') C))
      (Algebra.ClosedLift.exists_retraction (A := PowerSeries k') (C := C)
        (Ideal.span {(PowerSeries.X : PowerSeries k')})
        (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction C T)) (Iso.refl _)
  have := preservesHomology_sectionsFunctor Λ hW
  have := preservesHomology_sectionsFunctor Λ
    (isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec (k' := k') C hC)
  let I := injectiveResolution ((traitGenericPoint k')^*⟦Λ⟧.obj (𝟙_ _))
  let K := ((traitGenericPoint k')_*⟦Λ⟧.mapHomologicalComplex _).obj I.cocomplex
  have hK : ((K.sc' m (m + 1) (m + 2)).map (sectionsFunctor Λ (traitClosedLift C))).Exact :=
    (I.exact_succ m).map (sectionsFunctor Λ _)
  refine AddCommGrpCat.subsingleton_of_isZero
    (((ShortComplex.exact_iff_isZero_homology _).1 hK).of_iso ?_)
  exact (sectionsFunctor Λ (traitClosedLift C)).mapIso (I.isoRightDerivedObj _ (m + 1) ≪≫
      K.homologyIsoSc' m (m + 1) (m + 2) (by simp) (by simp)) ≪≫
    ((K.sc' m (m + 1) (m + 2)).mapHomologyIso _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
