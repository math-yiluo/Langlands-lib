/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.WeilSheaf.BifunctorHomTriangulated

/-!
# The derived hom of a bifunctor is exact

Let `H : Aᵒᵖ ⥤ B ⥤ C` be a bifunctor between abelian categories, additive in each variable, with
`A` having K-injective resolutions. The derived hom `RHom_H(-, L) : D(A)ᵒᵖ ⥤ D(C)`
(`DerivedCategory.bifunctorRHom`) is computed by the hom complex out of K-injective complexes,
and the hom complex is a triangulated functor on homotopy categories
(`HomotopyCategory.bifunctorHomOpFunctor`). Since K-injective complexes form a triangulated
subcategory of the homotopy category equivalent to `D(A)`, the derived hom commutes with the
shifts and is triangulated, `D(A)ᵒᵖ` being equipped with the triangulated structure of
`CategoryTheory.Pretriangulated.Opposite`
(`DerivedCategory.exists_commShift_isTriangulated_bifunctorRHom`).

This is the exactness of the Verdier dual `RHom(-, ω_X)` of Weil complexes (blueprint
`theorem-verdier-biduality`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Abelian Pretriangulated Pretriangulated.Opposite

namespace DerivedCategory

variable {A B C : Type*} [Category A] [Category B] [Category C] [Abelian A] [Abelian B]
  [Abelian C] [HasCountableProducts C] [HasDerivedCategory A] [HasDerivedCategory C]
  [HasKInjectiveResolutions A] (H : Aᵒᵖ ⥤ B ⥤ C) [∀ X, (H.obj X).Additive] [H.Additive]

/-- The derived hom `K ↦ op RHom_H(K, Y)` into a fixed cochain complex `Y`, as a functor
`D(A) ⥤ D(C)ᵒᵖ`: a K-injective complex representing `K`, followed by the hom complex. -/
noncomputable def bifunctorRHomOpFunctor (Y : CochainComplex B ℤ) :
    DerivedCategory A ⥤ (DerivedCategory C)ᵒᵖ :=
  (HomotopyCategory.KInjectives.equivalence A).inverse ⋙ ObjectProperty.ι _ ⋙
    HomotopyCategory.bifunctorHomOpFunctor H Y ⋙ DerivedCategory.Qh.op

noncomputable instance (Y : CochainComplex B ℤ) : (bifunctorRHomOpFunctor H Y).CommShift ℤ := by
  dsimp only [bifunctorRHomOpFunctor]
  infer_instance

instance (Y : CochainComplex B ℤ) : (bifunctorRHomOpFunctor H Y).IsTriangulated := by
  dsimp only [bifunctorRHomOpFunctor]
  infer_instance

/-- The hom complex functor `CochainComplex.bifunctorHomHomotopyFunctor` into the opposite of the
derived category is `HomotopyCategory.bifunctorHomOpFunctor` followed by the localization. -/
noncomputable def bifunctorHomHomotopyFunctorIso (Y : CochainComplex B ℤ) :
    CochainComplex.bifunctorHomHomotopyFunctor H Y ≅
      HomotopyCategory.bifunctorHomOpFunctor H Y ⋙ DerivedCategory.Qh.op :=
  let e : CochainComplex.bifunctorHomComplexFunctor H Y ≅
      CochainComplex.bifunctorHomOpFunctor H Y ⋙ (HomotopyCategory.quotient C _).op ⋙
        DerivedCategory.Qh.op :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl)
  Quotient.natIsoLift _ (Quotient.lift.isLift _ _ _ ≪≫ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.bifunctorHomOpFunctorFactors H Y).symm _ ≪≫
    Functor.associator _ _ _)

/-- The derived hom `RHom_H(-, Y)` is the functor `DerivedCategory.bifunctorRHomOpFunctor`
composed with the opposite. -/
noncomputable def bifunctorRHomOfComplexIso (Y : CochainComplex B ℤ) :
    bifunctorRHomOfComplex H Y ≅ (bifunctorRHomOpFunctor H Y).op ⋙ unopUnop _ :=
  let α : (HomotopyCategory.KInjectives.Qh (C := A)).inv ⋙ HomotopyCategory.KInjectives.ι ⋙
      CochainComplex.bifunctorHomHomotopyFunctor H Y ≅ bifunctorRHomOpFunctor H Y :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (bifunctorHomHomotopyFunctorIso H Y))
  { hom := NatTrans.leftOp α.inv
    inv := NatTrans.leftOp α.hom
    hom_inv_id := by rw [← NatTrans.leftOp_comp, Iso.hom_inv_id, NatTrans.leftOp_id]; rfl
    inv_hom_id := by rw [← NatTrans.leftOp_comp, Iso.inv_hom_id, NatTrans.leftOp_id]; rfl }

/-- **The derived hom is exact** in its first variable: `RHom_H(-, Y) : D(A)ᵒᵖ ⥤ D(C)` commutes
with the shifts and is triangulated. -/
theorem exists_commShift_isTriangulated_bifunctorRHomOfComplex (Y : CochainComplex B ℤ) :
    ∃ _ : (bifunctorRHomOfComplex H Y).CommShift ℤ, (bifunctorRHomOfComplex H Y).IsTriangulated :=
  letI := Functor.CommShift.ofIso (bifunctorRHomOfComplexIso H Y).symm ℤ
  have := Functor.CommShift.ofIso_compatibility (bifunctorRHomOfComplexIso H Y).symm ℤ
  ⟨inferInstance, Functor.isTriangulated_of_iso (bifunctorRHomOfComplexIso H Y).symm⟩

/-- **The derived hom is exact** in its first variable: `RHom_H(-, L) : D(A)ᵒᵖ ⥤ D(C)` commutes
with the shifts and is triangulated. -/
theorem exists_commShift_isTriangulated_bifunctorRHom [HasDerivedCategory B]
    [HasKInjectiveResolutions B] (L : DerivedCategory B) :
    ∃ _ : (bifunctorRHom H L).CommShift ℤ, (bifunctorRHom H L).IsTriangulated :=
  exists_commShift_isTriangulated_bifunctorRHomOfComplex H _

end DerivedCategory
