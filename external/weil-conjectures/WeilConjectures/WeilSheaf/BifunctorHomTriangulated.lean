/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import WeilConjectures.WeilSheaf.BifunctorHomShift

/-!
# The hom complex of a bifunctor is a triangulated functor on homotopy categories

Let `H : Cᵒᵖ ⥤ D ⥤ E` be a bifunctor and `Y` a cochain complex in `D`. The hom complex
`K ↦ op Hom_H(K, Y)` (`CochainComplex.bifunctorHomOpFunctor`) induces a functor
`HomotopyCategory.bifunctorHomOpFunctor H Y : K(C) ⥤ K(E)ᵒᵖ` which commutes with the shifts and is
triangulated, `K(E)ᵒᵖ` being equipped with the triangulated structure of
`CategoryTheory.Pretriangulated.Opposite`.

The proof: for a morphism `φ : K ⟶ L` the hom complex turns the degreewise split short exact
sequence `L ⟶ cone(φ) ⟶ K⟦1⟧` into the degreewise split short exact sequence
`Hom_H(K⟦1⟧, Y) ⟶ Hom_H(cone(φ), Y) ⟶ Hom_H(L, Y)`
(`CochainComplex.bifunctorHomMappingConeSplitting`), whose triangle in the homotopy category is
distinguished (`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`); its rotation
is identified with the image of the standard triangle of `φ`
(`CochainComplex.bifunctorHomMappingConeTriangleIso`).

This is used for the exactness of the Verdier dual of Weil complexes (blueprint
`theorem-verdier-biduality`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated Pretriangulated.Opposite

namespace CochainComplex

open HomComplex

variable {C D E : Type*} [Category C] [Category D] [Category E] [Preadditive C] [Preadditive D]
  [Preadditive E] [HasCountableProducts E] [HasBinaryBiproducts C] (H : Cᵒᵖ ⥤ D ⥤ E)
  [∀ X, (H.obj X).Additive] [H.Additive] (Y : CochainComplex D ℤ)

omit [HasBinaryBiproducts C] in
variable {H} in
@[simp]
lemma bifunctorHomMapLeft_zero (K K' : CochainComplex C ℤ) :
    bifunctorHomMapLeft (H := H) (Y := Y) (0 : K' ⟶ K) = 0 := by
  ext n p q hpq
  simp

omit [Preadditive C] [Preadditive D] [Preadditive E] [HasCountableProducts E]
  [HasBinaryBiproducts C] [∀ X, (H.obj X).Additive] [H.Additive] in
@[reassoc]
lemma map_op_app_comp_map_op_app {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (Z : D) :
    (H.map g.op).app Z ≫ (H.map f.op).app Z = (H.map (f ≫ g).op).app Z := by
  rw [op_comp, Functor.map_comp, NatTrans.comp_app]

omit [Preadditive D] [HasCountableProducts E] [HasBinaryBiproducts C]
  [∀ X, (H.obj X).Additive] in
lemma map_op_app_add_map_op_app {X₁ X₂ : C} (f g : X₁ ⟶ X₂) (Z : D) :
    (H.map f.op).app Z + (H.map g.op).app Z = (H.map (f + g).op).app Z := by
  rw [op_add, Functor.map_add, NatTrans.app_add]

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The short complex `Hom_H(K⟦1⟧, Y) ⟶ Hom_H(cone(φ), Y) ⟶ Hom_H(L, Y)` obtained by applying the
hom complex to `L ⟶ cone(φ) ⟶ K⟦1⟧`. -/
@[simps]
noncomputable def bifunctorHomMappingConeShortComplex : ShortComplex (CochainComplex E ℤ) :=
  ShortComplex.mk (bifunctorHomMapLeft (H := H) (Y := Y) (K := K⟦(1 : ℤ)⟧) (K' := mappingCone φ)
      (mappingCone.triangle φ).mor₃)
    (bifunctorHomMapLeft (H := H) (Y := Y) (K := mappingCone φ) (K' := L) (mappingCone.inr φ)) (by
      rw [← bifunctorHomMapLeft_comp, show mappingCone.inr φ ≫ (mappingCone.triangle φ).mor₃ = 0 by
        ext n; simp, bifunctorHomMapLeft_zero])

/-- The splitting in each degree of `CochainComplex.bifunctorHomMappingConeShortComplex`, induced
by the splitting of the mapping cone. -/
@[simps r s]
noncomputable def bifunctorHomMappingConeSplitting (n : ℤ) :
    ((bifunctorHomMappingConeShortComplex H Y φ).map
      (HomologicalComplex.eval E _ n)).Splitting where
  r := bifunctorHomLift H (K⟦(1 : ℤ)⟧) Y n fun p q hpq ↦
    bifunctorHomπ H (mappingCone φ) Y n p q hpq ≫
      (H.map (-((K.shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
        (mappingCone.inl φ).v (p + 1) p (by lia))).op).app _
  s := bifunctorHomLift H (mappingCone φ) Y n fun p q hpq ↦
    bifunctorHomπ H L Y n p q hpq ≫
      (H.map ((mappingCone.snd φ).v p p (add_zero p)).op).app _
  f_r := by
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    have e : (-((K.shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
        (mappingCone.inl φ).v (p + 1) p (by lia))) ≫ (mappingCone.triangle φ).mor₃.f p = 𝟙 _ := by
      rw [Preadditive.neg_comp, assoc, mappingCone.inl_v_triangle_mor₃_f, Preadditive.comp_neg,
        neg_neg, Iso.hom_inv_id]
    simp only [ShortComplex.map_f, HomologicalComplex.eval_map,
      bifunctorHomMappingConeShortComplex_f, assoc, bifunctorHomLift_π,
      bifunctorHomMapLeft_f_π_assoc]
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, e, op_id]
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, comp_id, id_comp]
  s_g := by
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    simp only [ShortComplex.map_g, HomologicalComplex.eval_map,
      bifunctorHomMappingConeShortComplex_g, assoc, bifunctorHomMapLeft_f_π,
      bifunctorHomLift_π_assoc]
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, mappingCone.inr_f_snd_v, op_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, comp_id, id_comp]
  id := by
    refine bifunctorHomObj_hom_ext fun p q hpq ↦ ?_
    have e : @HAdd.hAdd ((mappingCone φ).X p ⟶ (mappingCone φ).X p) _ _ _
        ((mappingCone.triangle φ).mor₃.f p ≫ (-((K.shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
          (mappingCone.inl φ).v (p + 1) p (by lia))))
        ((mappingCone.snd φ).v p p (add_zero p) ≫ (mappingCone.inr φ).f p) = 𝟙 _ := by
      refine mappingCone.ext_from φ (p + 1) p (by lia) ?_ ?_
      · simp only [Preadditive.comp_add, mappingCone.inl_v_triangle_mor₃_f_assoc,
          Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Iso.inv_hom_id_assoc,
          mappingCone.inl_v_snd_v_assoc, zero_comp, add_zero, comp_id]
      · simp only [Preadditive.comp_add, mappingCone.inr_f_triangle_mor₃_f_assoc, zero_comp,
          mappingCone.inr_f_snd_v_assoc, zero_add, comp_id]
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      bifunctorHomMappingConeShortComplex_f, bifunctorHomMappingConeShortComplex_g,
      Preadditive.add_comp, assoc, bifunctorHomMapLeft_f_π, bifunctorHomLift_π_assoc,
      bifunctorHomLift_π, bifunctorHomMapLeft_f_π_assoc, map_op_app_comp_map_op_app]
    rw [← Preadditive.comp_add, map_op_app_add_map_op_app, e, op_id]
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, comp_id, id_comp]

/-- The triangle `Hom_H(cone(φ), Y) ⟶ Hom_H(L, Y) ⟶ Hom_H(K, Y) ⟶ Hom_H(cone(φ), Y)⟦1⟧` of cochain
complexes corresponding, under `CategoryTheory.Pretriangulated.triangleOpEquivalence`, to the
image of the standard triangle of `φ` by `CochainComplex.bifunctorHomOpFunctor`. -/
noncomputable abbrev bifunctorHomMappingConeTriangle : Triangle (CochainComplex E ℤ) :=
  ((triangleOpEquivalence _).inverse.obj
    ((bifunctorHomOpFunctor H Y).mapTriangle.obj (mappingCone.triangle φ))).unop

/-- The isomorphism `Hom_H(K, Y) ≅ Hom_H(K⟦1⟧, Y)⟦1⟧`, up to sign, used to identify
`CochainComplex.bifunctorHomMappingConeTriangle` with a rotated degreewise split triangle. -/
noncomputable def bifunctorHomMappingConeTriangleIso₃ :
    bifunctorHomObj H K Y ≅ (bifunctorHomObj H (K⟦(1 : ℤ)⟧) Y)⟦(1 : ℤ)⟧ :=
  let e := ((opShiftFunctorEquivalence (CochainComplex E ℤ) 1).unitIso.app
      (op (bifunctorHomObj H K Y))).unop.symm ≪≫
    (CategoryTheory.shiftFunctor _ (1 : ℤ)).mapIso
      (((shiftFunctorOpIso _ 1 (-1) (by lia)).app (op (bifunctorHomObj H K Y))).unop.symm ≪≫
        bifunctorHomShiftIso H K Y 1 (-1) (by lia))
  { hom := -e.hom
    inv := -e.inv
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- The identification of `CochainComplex.bifunctorHomMappingConeTriangle` with the rotation of the
triangle of the degreewise split short exact sequence
`CochainComplex.bifunctorHomMappingConeShortComplex`. -/
noncomputable def bifunctorHomMappingConeTriangleIso :
    bifunctorHomMappingConeTriangle H Y φ ≅
      (triangleOfDegreewiseSplit _ (bifunctorHomMappingConeSplitting H Y φ)).rotate :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (bifunctorHomMappingConeTriangleIso₃ H Y)
    (by
      dsimp [bifunctorHomMappingConeTriangle, triangleOpEquivalence]
      simp only [comp_id, id_comp]
      rfl)
    (by
      rw [Iso.refl_hom, id_comp]
      change bifunctorHomMapLeft φ ≫ (bifunctorHomMappingConeTriangleIso₃ H Y).hom =
        homOfDegreewiseSplit _ (bifunctorHomMappingConeSplitting H Y φ)
      ext m : 1
      refine bifunctorHomObj_hom_ext (n := m + 1) fun P Q hPQ ↦ ?_
      have h₁ : (-((K.shiftFunctorObjXIso 1 P (P + 1) rfl).hom ≫
          (mappingCone.inl φ).v (P + 1) P (by lia))) ≫
            (mappingCone.snd φ).v P P (add_zero P) = 0 := by
        simp
      have h₂ : (-((K.shiftFunctorObjXIso 1 P (P + 1) rfl).hom ≫
          (mappingCone.inl φ).v (P + 1) P (by lia))) ≫ (mappingCone φ).d P (P + 1) ≫
            (mappingCone.snd φ).v (P + 1) (P + 1) (add_zero _) =
              -((K.shiftFunctorObjXIso 1 P (P + 1) rfl).hom ≫ φ.f (P + 1)) := by
        rw [Preadditive.neg_comp, assoc, mappingCone.inl_v_d_assoc φ (P + 1) P (P + 2) (by lia)
          (by lia)]
        simp
      simp only [HomologicalComplex.comp_f, homOfDegreewiseSplit_f, assoc]
      change _ = ((bifunctorHomMappingConeSplitting H Y φ m).s ≫
        (bifunctorHomObj H (mappingCone φ) Y).d m (m + 1) ≫
          (bifunctorHomMappingConeSplitting H Y φ (m + 1)).r) ≫ _
      simp only [assoc, bifunctorHomMappingConeSplitting_r, bifunctorHomLift_π,
        bifunctorHomObj_d_π_assoc H (mappingCone φ) Y m (m + 1) P Q hPQ (Q - 1) (P + 1) (by lia)
          (by lia), Linear.comp_units_smul, Linear.units_smul_comp, Preadditive.comp_sub,
        Preadditive.sub_comp, bifunctorHomMappingConeSplitting_s,
        bifunctorHomLift_π_assoc, NatTrans.naturality, map_op_app_comp_map_op_app,
        map_op_app_comp_map_op_app_assoc, h₁, h₂,
        op_zero, Functor.map_zero, NatTrans.app_zero, zero_comp, comp_zero, zero_sub]
      dsimp only [bifunctorHomMappingConeTriangleIso₃]
      simp only [HomologicalComplex.neg_f_apply, HomologicalComplex.comp_f, Iso.trans_hom,
        Iso.symm_hom, Iso.unop_inv, Iso.app_inv, Functor.mapIso_hom,
        shiftFunctor_map_f', opShiftFunctorEquivalence_unitIso_inv_app _ 1 (-1),
        shiftFunctorOpIso_inv_app_neg, shiftFunctorOpIso_hom_app_neg, unop_comp,
        Quiver.Hom.unop_op, shiftFunctorCompIsoId, Iso.symm_inv, Iso.trans_inv,
        shiftFunctorZero_inv_app_f, shiftFunctorAdd'_hom_app_f', Preadditive.neg_comp,
        Preadditive.comp_neg, assoc, NatTrans.comp_app]
      repeat erw [unop_id]
      repeat erw [HomologicalComplex.id_f]
      repeat erw [id_comp]
      rw [bifunctorHomShiftIso_hom_f_π]
      simp only [Linear.comp_units_smul,
        bifunctorHomObj_XIsoOfEq_hom_π, bifunctorHomMapLeft_f_π, op_neg, Functor.map_neg,
        NatTrans.app_neg, Preadditive.comp_neg, neg_neg, bifunctorHomShiftSign_one,
        Int.negOnePow_succ, Units.neg_smul])
    (by
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, comp_id]
      dsimp only [bifunctorHomMappingConeTriangleIso₃]
      simp only [Functor.map_comp, Preadditive.neg_comp,
        Preadditive.comp_neg, neg_neg, Iso.trans_hom, Iso.symm_hom, Iso.unop_inv, Iso.app_inv,
        Functor.mapIso_hom, assoc, Triangle.rotate_mor₃, triangleOfDegreewiseSplit_mor₁,
        bifunctorHomMappingConeShortComplex_f, shiftFunctorOpIso_inv_app_neg]
      erw [unop_id, CategoryTheory.Functor.map_id, id_comp]
      change ((opShiftFunctorEquivalence _ 1).unitIso.inv.app _).unop ≫
        ((bifunctorHomShiftIso H K Y 1 (-1) (by lia)).hom ≫
          bifunctorHomMapLeft (mappingCone.triangle φ).mor₃)⟦(1 : ℤ)⟧' = _
      rw [Functor.map_comp]
      rfl)

variable [HasZeroObject E] [HasBinaryBiproducts E]

/-- The image by the hom complex of the standard triangle of `φ` is, in the homotopy category,
a distinguished triangle of the opposite category. -/
lemma bifunctorHomMappingConeTriangle_distinguished :
    (HomotopyCategory.quotient E (.up ℤ)).mapTriangle.obj (bifunctorHomMappingConeTriangle H Y φ) ∈
      distTriang (HomotopyCategory E (.up ℤ)) := by
  refine isomorphic_distinguished _ (rot_of_distTriang _
    ((HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
      ⟨_, bifunctorHomMappingConeSplitting H Y φ, ⟨Iso.refl _⟩⟩)) _ ?_
  exact (HomotopyCategory.quotient E (.up ℤ)).mapTriangle.mapIso
    (bifunctorHomMappingConeTriangleIso H Y φ) ≪≫
      ((HomotopyCategory.quotient E (.up ℤ)).mapTriangleRotateIso.app _).symm

end CochainComplex

namespace HomotopyCategory

variable {C D E : Type*} [Category C] [Category D] [Category E] [Preadditive C] [Preadditive D]
  [Preadditive E] [HasCountableProducts E] [HasBinaryBiproducts C] (H : Cᵒᵖ ⥤ D ⥤ E)
  [∀ X, (H.obj X).Additive] [H.Additive] (Y : CochainComplex D ℤ)

/-- The hom complex `K ↦ op Hom_H(K, Y)` on homotopy categories. -/
noncomputable def bifunctorHomOpFunctor :
    HomotopyCategory C (.up ℤ) ⥤ (HomotopyCategory E (.up ℤ))ᵒᵖ :=
  CategoryTheory.Quotient.lift _
    (CochainComplex.bifunctorHomOpFunctor H Y ⋙ (HomotopyCategory.quotient E _).op)
    (fun _ _ _ _ ⟨h⟩ ↦ by
      simp only [Functor.comp_map, Functor.op_map, CochainComplex.bifunctorHomOpFunctor_map,
        Quiver.Hom.unop_op]
      rw [HomotopyCategory.eq_of_homotopy _ _ (CochainComplex.bifunctorHomMapLeftHomotopy h)])

/-- `HomotopyCategory.bifunctorHomOpFunctor` lifts `CochainComplex.bifunctorHomOpFunctor`. -/
noncomputable def bifunctorHomOpFunctorFactors :
    HomotopyCategory.quotient C _ ⋙ HomotopyCategory.bifunctorHomOpFunctor H Y ≅
      CochainComplex.bifunctorHomOpFunctor H Y ⋙ (HomotopyCategory.quotient E _).op :=
  CategoryTheory.Quotient.lift.isLift _ _ _

noncomputable instance : (HomotopyCategory.bifunctorHomOpFunctor H Y).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift _ _ _ _

instance : NatTrans.CommShift (bifunctorHomOpFunctorFactors H Y).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility _ _ _ _

variable [HasZeroObject C] [HasZeroObject E] [HasBinaryBiproducts E]

/-- **The hom complex is a triangulated functor** `K(C) ⥤ K(E)ᵒᵖ`. -/
instance : (HomotopyCategory.bifunctorHomOpFunctor H Y).IsTriangulated where
  map_distinguished := by
    rintro T ⟨K, L, φ, ⟨e⟩⟩
    let Q := HomotopyCategory.quotient E (.up ℤ)
    rw [Pretriangulated.distinguished_iff_of_iso
      ((HomotopyCategory.bifunctorHomOpFunctor H Y).mapTriangle.mapIso e ≪≫
        ((Functor.mapTriangleCompIso _ _).app _).symm ≪≫
        (Functor.mapTriangleIso (bifunctorHomOpFunctorFactors H Y)).app _ ≪≫
        (Functor.mapTriangleCompIso _ _).app _ ≪≫
        Q.op.mapTriangle.mapIso ((triangleOpEquivalence _).counitIso.app _).symm ≪≫
        (Q.mapTriangleOpCompTriangleOpEquivalenceFunctorApp _).symm)]
    exact op_distinguished _ (CochainComplex.bifunctorHomMappingConeTriangle_distinguished H Y φ)

end HomotopyCategory
