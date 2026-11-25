/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Coordinates for a tensor with a two-term coefficient complex
Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 0A8X and 08J7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] SheafOfModules.monoidalCategory

local instance twoTermTensorCoordinatesLocal1 : MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.monoidalCategory R

local instance twoTermTensorCoordinatesLocal2 : HasBinaryBiproducts (Modules.{t, u} Y R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

variable (A Q : CochainComplex (Modules.{t, u} Y R) ℤ)
  (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))

local instance (priority :=
  2000) twoTermTensorCoordinatesLocal3 :
    HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  countableColimits Y R

local instance (priority :=
  2000) twoTermTensorCoordinatesLocal4 :
    (ordinaryTensor Y R).PreservesZeroMorphisms :=
  ordinaryTensorZero Y R

local instance (priority := 2000) twoTermTensorCoordinatesLocal5 (M : Modules.{t, u} Y R) :
    ((ordinaryTensor Y R).obj M).PreservesZeroMorphisms := ordinaryTensorObjZero Y R M

local instance twoTermTensorCoordinatesLocal6 (K L : CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex.HasMapBifunctor K L (ordinaryTensor Y R) := fun _j ↦
  @HasColimitsOfShape.has_colimit _ _ _ _
    ((countableColimits.{t, u} Y R).has_colimits_of_shape _) _

/-- The inclusions jointly detect maps out of a total tensor term.
Source: the coproduct universal property, Stacks 06YL.
(blueprint: lem-sf-two-term-tensor-coordinates). -/
theorem totalTensor_hom_ext (N : Modules.{t, u} Y R) (n : ℤ)
    (f g : (((totalTensor Y R).obj A).obj Q).X n ⟶ N)
    (h : ∀ (a b : ℤ) (hab : a + b = n),
      CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b n hab ≫ f =
        CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b n hab ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  exact h

/-- Deleting zero summands in a two-term total tensor. The inverse is the two coproduct
inclusions, so this construction imposes no condition on the differential.
Source: Stacks 06YL and the finite-free calculation in the blueprint.
(blueprint: lem-sf-two-term-tensor-coordinates). -/
def twoTermTensorRawIso (n : ℤ) :
    (((totalTensor Y R).obj A).obj Q).X n ≅
      (((ordinaryTensor Y R).obj (A.X (n + 1))).obj (Q.X (-1))) ⊞
        (((ordinaryTensor Y R).obj (A.X n)).obj (Q.X 0)) := by
  classical
  let := countableColimits.{t, u} Y R
  let := ordinaryTensorZero.{t, u} Y R
  let : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  letI : CochainComplex.HasMapBifunctor A Q (ordinaryTensor Y R) := fun _j ↦
    @HasColimitsOfShape.has_colimit _ _ _ _
      ((countableColimits.{t, u} Y R).has_colimits_of_shape _) _
  let f := fun (a b : ℤ) (hab : a + b = n) ↦
    if hb : b = -1 then
      eqToHom (congrArg₂ (fun i k ↦ ((ordinaryTensor Y R).obj (A.X i)).obj (Q.X k))
        (show a = n + 1 by omega) hb) ≫ biprod.inl
    else if hb' : b = 0 then
      eqToHom (congrArg₂ (fun i k ↦ ((ordinaryTensor Y R).obj (A.X i)).obj (Q.X k))
        (show a = n by omega) hb') ≫ biprod.inr
    else 0
  refine ⟨HomologicalComplex.mapBifunctorDesc
      (K₁ := A) (K₂ := Q) (F := ordinaryTensor Y R) (c := .up ℤ) f,
    biprod.desc (CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R)
      (n + 1) (-1) n (by omega))
      (CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) n 0 n (by simp)), ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    change a + b = n at hab
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hb : b = -1
    · subst b
      obtain rfl : a = n + 1 := by omega
      simp only [f, dite_eq_left rfl, eqToHom_refl, Category.id_comp,
        biprod.inl_desc, CochainComplex.ιMapBifunctor]
      exact (Category.comp_id _).symm
    · by_cases hb' : b = 0
      · subst b
        obtain rfl : a = n := by omega
        simp only [f, dite_eq_right (by omega : (0 : ℤ) ≠ -1), dite_true,
          eqToHom_refl, Category.id_comp, biprod.inr_desc, CochainComplex.ιMapBifunctor]
        exact (Category.comp_id _).symm
      · have hz := ((ordinaryTensor Y R).obj (A.X a)).map_isZero (hzero b hb hb')
        exact hz.eq_of_src _ _
  · apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc, f,
        dite_true, eqToHom_refl, Category.id_comp, Category.comp_id]
    · simp only [biprod.inr_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc, f,
        dite_eq_right (by omega : (0 : ℤ) ≠ -1), dite_true, eqToHom_refl,
        Category.id_comp, Category.comp_id]
@[reassoc]
theorem twoTermTensorRawIso_inl_inv (n : ℤ) :
    biprod.inl ≫ (twoTermTensorRawIso Y R A Q hzero n).inv =
      CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R)
        (n + 1) (-1) n (by omega) := by
  exact biprod.inl_desc _ _
@[reassoc]
theorem twoTermTensorRawIso_inr_inv (n : ℤ) :
    biprod.inr ≫ (twoTermTensorRawIso Y R A Q hzero n).inv =
      CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) n 0 n (by simp) := by
  exact biprod.inr_desc _ _

/-- The two surviving rank-one coefficients identify the total term with two terms of A.
Source: Stacks 03EK, unitors, and the blueprint finite-free calculation.
(blueprint: lem-sf-two-term-tensor-coordinates). -/
def twoTermTensorIso
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (n : ℤ) :
    (((totalTensor Y R).obj A).obj Q).X n ≅ A.X (n + 1) ⊞ A.X n :=
  twoTermTensorRawIso Y R A Q hzero n ≪≫
    biprod.mapIso
      (((ordinaryTensor Y R).obj (A.X (n + 1))).mapIso eNeg ≪≫
        (ρ_ (A.X (n + 1))))
      (((ordinaryTensor Y R).obj (A.X n)).mapIso eZero ≪≫
        (ρ_ (A.X n)))
@[reassoc]
theorem twoTermTensorIso_ι_neg_hom
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (n : ℤ) :
    CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R)
        (n + 1) (-1) n (by omega) ≫
      (twoTermTensorIso Y R A Q hzero eNeg eZero n).hom =
    ((ordinaryTensor Y R).obj (A.X (n + 1))).map eNeg.hom ≫
      (ρ_ (A.X (n + 1))).hom ≫ biprod.inl := by
  rw [← twoTermTensorRawIso_inl_inv Y R A Q hzero n]
  simp only [twoTermTensorIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.inl_map,
    Functor.mapIso_hom]
@[reassoc]
theorem twoTermTensorIso_ι_zero_hom
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (n : ℤ) :
    CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) n 0 n (by simp) ≫
      (twoTermTensorIso Y R A Q hzero eNeg eZero n).hom =
    ((ordinaryTensor Y R).obj (A.X n)).map eZero.hom ≫
      (ρ_ (A.X n)).hom ≫ biprod.inr := by
  rw [← twoTermTensorRawIso_inr_inv Y R A Q hzero n]
  simp only [twoTermTensorIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.inr_map,
    Functor.mapIso_hom]

end WeilConjectures.IntegralHom
