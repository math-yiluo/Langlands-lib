/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.TateTwist.IntegralLocallyFree
public import WeilConjectures.TraceFormula.PointDualizable

/-!
# Dualizable bounded constructible `𝒪_E`-complexes

The integral analogues of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeDualizable`
and `WeilConjectures.TraceFormula.DualizableShift`: in `Dᵇc(X)⟦𝒪_E⟧`, a locally free module object
placed in degree `0` is dualizable
(`ProEtale.CondensedRing.isDualizable_singleFunctor_of_isLocallyFree_padicIntegers`), and so are
the shifts of a dualizable object (`ProEtale.CondensedRing.IsDualizable.shift_padicIntegers`). In
particular the shifted integral Tate twists `𝒪_{E,X}(d)[n]` are dualizable
(`ProEtale.CondensedRing.isDualizable_shift_integralTateTwistBoundedConstructible`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- A locally free module object over `𝒪_{E,X}`, placed in degree `0`, is dualizable in
`Dᵇc(X)⟦𝒪_E⟧`. -/
theorem isDualizable_singleFunctor_of_isLocallyFree_padicIntegers
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hM : IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) M) :
    IsDualizable (C := Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
      ⟨(DerivedCategory.singleFunctor _ 0).obj M,
        boundedConstructible_singleFunctor_obj _ X.left 0 M hM.isConstructibleModuleObject⟩ := by
  let := DerivedCategory.braidedCategory'
    (C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
  refine ObjectProperty.isDualizable_of_isDualizable_obj _ _ ?_
  refine DerivedCategory.isDualizable_Q_obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) 0 0 fun n ↦ ?_
  by_cases hn : n = 0
  · subst hn
    exact IsDualizable.of_iso (HomologicalComplex.singleObjXSelf _ _ M).symm hM.isDualizable
  · exact IsZero.isDualizable (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- The tensor product of shifts in `Dᵇc(X)⟦𝒪_E⟧`, `A⟦a⟧ ⊗ B⟦b⟧ ≅ (A ⊗ B)⟦a + b⟧`. -/
noncomputable def boundedConstructibleShiftTensorShiftIso_padicIntegers
    (A B : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) (a b : ℤ) :
    (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) a).obj A ⊗
        (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) b).obj B ≅
      (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) (a + b)).obj (A ⊗ B) :=
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).ι
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((((ι.commShiftIso a).app A) ⊗ᵢ ((ι.commShiftIso b).app B)) ≪≫
      DerivedCategory.shiftTensorShiftIso _ (ι.obj A) (ι.obj B) a b ≪≫
      ((ι.commShiftIso (a + b)).app (A ⊗ B)).symm)

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- The shifts `𝟙⟦n⟧` of the unit of `Dᵇc(X)⟦𝒪_E⟧` are dualizable. -/
theorem isDualizable_shift_unit_padicIntegers (n : ℤ) :
    IsDualizable ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) n).obj
      (𝟙_ _)) := by
  have e : ∀ a b : ℤ, a + b = 0 →
      ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) a).obj (𝟙_ _) ⊗
        (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) b).obj (𝟙_ _) ≅
          𝟙_ _) :=
    fun a b h ↦ boundedConstructibleShiftTensorShiftIso_padicIntegers ℓ E X _ _ a b ≪≫
      (shiftFunctor _ (a + b)).mapIso (λ_ _) ≪≫ eqToIso (by rw [h]) ≪≫
      (shiftFunctorZero _ ℤ).app _
  exact isDualizable_of_tensorIso (e n (-n) (add_neg_cancel n)) (e (-n) n (neg_add_cancel n))

variable {ℓ E X} in
omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- The shifts of a dualizable object of `Dᵇc(X)⟦𝒪_E⟧` are dualizable. -/
theorem IsDualizable.shift_padicIntegers {L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (hL : IsDualizable L) (n : ℤ) :
    IsDualizable ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) n).obj L) := by
  have e := boundedConstructibleShiftTensorShiftIso_padicIntegers ℓ E X L (𝟙_ _) 0 n
  refine IsDualizable.of_iso (e ≪≫ (shiftFunctor _ (0 + n)).mapIso (ρ_ L) ≪≫
    eqToIso (by rw [zero_add])) ?_
  exact IsDualizable.tensorObj (IsDualizable.of_iso ((shiftFunctorZero _ ℤ).app L).symm hL)
    (isDualizable_shift_unit_padicIntegers ℓ E X n)

/-- The shifted integral Tate twists `𝒪_{E,X}(d)[n]` are dualizable in `Dᵇc(X)⟦𝒪_E⟧`. -/
theorem isDualizable_shift_integralTateTwistBoundedConstructible [NeZero (ℓ : k)] (d : ℕ)
    (n : ℤ) :
    IsDualizable ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) n).obj
      (integralTateTwistBoundedConstructible ℓ E X.hom d)) :=
  IsDualizable.shift_padicIntegers (isDualizable_singleFunctor_of_isLocallyFree_padicIntegers ℓ E X
    _ (isLocallyFree_integralTateTwistNat ℓ E X.hom d)) n

end AlgebraicGeometry.ProEtale.CondensedRing
