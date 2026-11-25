/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.TraceFormula.PointTrace

/-!
# Every object of the point category is dualizable

Let `k` be a separably closed field and `s = Spec k`. Every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite
direct sum of shifts `𝟙⟦n⟧` of the unit
(`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), and each `𝟙⟦n⟧` is invertible,
with inverse `𝟙⟦-n⟧`, and a finite biproduct of dualizable objects is dualizable
(`CategoryTheory.Limits.Bicone.nonempty_hasRightDual_pt`). Hence every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is
dualizable (`ProEtale.CondensedRing.nonempty_hasRightDual_point`): the bounded complexes of
`ℚ̄_ℓ`-vector spaces with finite-dimensional cohomology are the perfect complexes over `ℚ̄_ℓ`
(blueprint `lemma-perfect-complexes-geometric-point`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.ShiftDecomposition

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C] [HasShift C ℤ]

/-- An object which is a finite direct sum of shifts of an object `E` all of whose shifts are
dualizable is dualizable. -/
theorem isDualizable {E P : C} (D : ShiftDecomposition E P)
    (hE : ∀ n : ℤ, IsDualizable ((shiftFunctor C n).obj E)) : IsDualizable P :=
  Bicone.nonempty_hasRightDual_pt D.isBilimitBicone fun j ↦ hE (D.deg j)

end CategoryTheory.ShiftDecomposition

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]

/-- The tensor product `𝟙⟦a⟧ ⊗ 𝟙⟦b⟧` of two shifts of the unit of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is `𝟙` when
`a + b = 0`: the corresponding isomorphism `𝟙⟦a⟧ ⊗ᴸ 𝟙⟦b⟧ ≅ (𝟙 ⊗ᴸ 𝟙)⟦a + b⟧ ≅ 𝟙` of
`D(Mod_{ℚ̲̄_ℓ,s})` (`DerivedCategory.shiftTensorShiftIso`), restricted to the full subcategory. -/
noncomputable def shiftUnitTensorShiftUnitIsoPoint (a b : ℤ) (h : a + b = 0) :
    (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).obj (𝟙_ _) ⊗
        (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) b).obj (𝟙_ _) ≅
      𝟙_ _ :=
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    (point k).left)).ι
  let U := 𝟙_ (DerivedCategory (PointMod ℓ k))
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((((ι.commShiftIso a).app (𝟙_ _)) ⊗ᵢ ((ι.commShiftIso b).app (𝟙_ _))) ≪≫
      DerivedCategory.shiftTensorShiftIso (PointMod ℓ k) U U a b ≪≫
      (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [h]) ≪≫ (shiftFunctorZero _ ℤ).app U)

/-- The shifts `𝟙⟦n⟧` of the unit of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` are dualizable: they are invertible, with
inverse `𝟙⟦-n⟧`. -/
theorem isDualizable_shift_unit_point (n : ℤ) :
    IsDualizable ((shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).obj
      (𝟙_ _)) :=
  isDualizable_of_tensorIso (shiftUnitTensorShiftUnitIsoPoint ℓ k n (-n) (add_neg_cancel n))
    (shiftUnitTensorShiftUnitIsoPoint ℓ k (-n) n (neg_add_cancel n))

/-- **Every object of the point category is dualizable** (blueprint
`lemma-perfect-complexes-geometric-point`): over a separably closed field `k`, every object `P` of
`Dᵇc(s)⟦ℚ̲̄_ℓ⟧` has a right dual. Indeed `P` is a finite direct sum of shifts of the unit
(`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), and these are invertible. -/
theorem nonempty_hasRightDual_point [Fact (ringChar k).Prime] [IsSepClosed k]
    (P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (HasRightDual P) :=
  (nonempty_shiftDecomposition_point ℓ k P).some.isDualizable (isDualizable_shift_unit_point ℓ k)

end AlgebraicGeometry.ProEtale.CondensedRing
