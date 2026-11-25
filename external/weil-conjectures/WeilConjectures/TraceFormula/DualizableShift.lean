/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PointDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-!
# Shifts of dualizable bounded constructible complexes

Let `X` be a separated `k`-scheme of finite type. The shifts `𝟙⟦n⟧` of the unit of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` are invertible, with inverse `𝟙⟦-n⟧`
(`ProEtale.CondensedRing.isDualizable_shift_unit`), so the shifts of a dualizable object are
dualizable (`ProEtale.CondensedRing.IsDualizable.shift`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- The tensor product of shifts in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, `A⟦a⟧ ⊗ B⟦b⟧ ≅ (A ⊗ B)⟦a + b⟧`: the
isomorphism `DerivedCategory.shiftTensorShiftIso` of the ambient derived category, restricted to
the full subcategory. -/
noncomputable def boundedConstructibleShiftTensorShiftIso
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (a b : ℤ) :
    (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).obj A ⊗
        (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) b).obj B ≅
      (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (a + b)).obj (A ⊗ B) :=
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((((ι.commShiftIso a).app A) ⊗ᵢ ((ι.commShiftIso b).app B)) ≪≫
      DerivedCategory.shiftTensorShiftIso _ (ι.obj A) (ι.obj B) a b ≪≫
      ((ι.commShiftIso (a + b)).app (A ⊗ B)).symm)

/-- The shifts `𝟙⟦n⟧` of the unit of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` are dualizable: they are invertible, with
inverse `𝟙⟦-n⟧`. -/
theorem isDualizable_shift_unit (n : ℤ) :
    IsDualizable ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).obj (𝟙_ _)) := by
  have e : ∀ a b : ℤ, a + b = 0 →
      ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).obj (𝟙_ _) ⊗
        (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) b).obj (𝟙_ _) ≅ 𝟙_ _) :=
    fun a b h ↦ boundedConstructibleShiftTensorShiftIso ℓ X _ _ a b ≪≫
      (shiftFunctor _ (a + b)).mapIso (λ_ _) ≪≫ eqToIso (by rw [h]) ≪≫
      (shiftFunctorZero _ ℤ).app _
  exact isDualizable_of_tensorIso (e n (-n) (add_neg_cancel n)) (e (-n) n (neg_add_cancel n))

variable {X} in
/-- The shifts of a dualizable object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` are dualizable:
`L⟦n⟧ ≅ L ⊗ 𝟙⟦n⟧`, a tensor product of dualizable objects. -/
theorem IsDualizable.shift {L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (hL : IsDualizable L) (n : ℤ) :
    IsDualizable ((shiftFunctor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).obj L) := by
  have e := boundedConstructibleShiftTensorShiftIso ℓ X L (𝟙_ _) 0 n
  refine IsDualizable.of_iso (e ≪≫ (shiftFunctor _ (0 + n)).mapIso (ρ_ L) ≪≫
    eqToIso (by rw [zero_add])) ?_
  exact IsDualizable.tensorObj (IsDualizable.of_iso ((shiftFunctorZero _ ℤ).app L).symm hL)
    (isDualizable_shift_unit ℓ X n)

end AlgebraicGeometry.ProEtale.CondensedRing
