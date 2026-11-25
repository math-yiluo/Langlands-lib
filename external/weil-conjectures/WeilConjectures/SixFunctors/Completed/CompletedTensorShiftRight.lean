/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.SixFunctors.Completed.CompletedTensorFiniteShift
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Right shifts of the completed integral tensor

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4), and the last sentence
of the main-20261015 blueprint proof of `theorem-poincare-duality--2`;
Stacks Project, Tags 011G, 012Z, 014E and 08TC
(blueprint: lem-sf-completed-tensor-shift-right).

The finite comparison has the same signed formula as Mathlib's right tensor shift.
Its formula is imposed directly on the recorded reduced tensor generators, without
extra tensor structure hypotheses. The strict tower comparison and the product and
cone formulas normalize the derived natural isomorphism on every good model.
-/

@[expose] public section

attribute [local irreducible] CategoryTheory.constantSheaf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b c d e f

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace WeilConjectures

attribute [local irreducible] unrestrictedIntegralReductionFunctor
  unrestrictedIntegralReductionExistence
  integralCompletedTensor

/-- Shift the second input of a bifunctor, retaining the first input.
Source: Stacks Tag 011G (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable abbrev completedTensorShiftSecond (A : Type a) [Category.{b} A] [HasShift A ℤ]
    (r : ℤ) : A × A ⥤ A × A :=
  (𝟭 A).prod (shiftFunctor A r)

section ProductCone

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The degreewise product shift identification, after the specified tower comparison.
Source: Stacks Tags 011G and 08TC (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftProductIso
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r) :
    (∏ᶜ fun n : ℕ ↦ D.obj (op n)) ≅ (∏ᶜ fun n : ℕ ↦ C.obj (op n))⟦r⟧ :=
  Limits.Pi.mapIso (fun n ↦ α.app (op n)) ≪≫
    (PreservesProduct.iso (shiftFunctor (CochainComplex A ℤ) r)
      (fun n : ℕ ↦ C.obj (op n))).symm

/-- The actual endomorphism 1-s of the product of a strict tower.
Source: Stacks Tag 08TC (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftOneSub
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C)

/-- Cone compatibility: the unshifted summand has coefficient 1 and the shifted
summand has coefficient (-1)^r, after the product identification. Mathlib orders
these summands as A[1], B, opposite to the written B ⊕ A[1].
Source: Stacks Tag 014E (blueprint: lem-sf-completed-tensor-shift-right). -/
def completedTensorShiftConeFormula
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (δ : CochainComplex.mappingCone (completedTensorShiftOneSub D) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))⟦r⟧) : Prop :=
  (∀ j : ℤ,
    (CochainComplex.mappingCone.inr (completedTensorShiftOneSub D)).f j ≫ δ.hom.f j =
      (completedTensorShiftProductIso C D r α).hom.f j ≫
        (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C)).f (j + r) ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (completedTensorShiftOneSub C)) r j (j + r) rfl).inv) ∧
  (∀ (i j : ℤ) (h : i + (-1) = j),
    (CochainComplex.mappingCone.inl (completedTensorShiftOneSub D)).v i j h ≫
        δ.hom.f j =
      r.negOnePow • ((completedTensorShiftProductIso C D r α).hom.f i ≫
        (CochainComplex.mappingCone.inl (completedTensorShiftOneSub C)).v
          (i + r) (j + r) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (completedTensorShiftOneSub C)) r j (j + r) rfl).inv))

/-- Shift the cone comparison by -1 and interchange the two shifts. This is the
specified comparison of the product mapping-fiber complexes, without cone choices.
Source: Stacks Tags 014E and 08TC (blueprint: lem-sf-completed-tensor-shift-right). -/
noncomputable def completedTensorShiftRoosIso
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (δ : CochainComplex.mappingCone (completedTensorShiftOneSub D) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))⟦r⟧) :
    integralOperationsRoos D ≅ (integralOperationsRoos C)⟦r⟧ :=
  (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).mapIso δ ≪≫
    (shiftFunctorComm (CochainComplex A ℤ) r (-1 : ℤ)).app
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))

private theorem complexProducts : HasProductsOfShape ℕ (CochainComplex A ℤ) :=
  inferInstance
attribute [local instance] complexProducts

private theorem productIso_π
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r) (n : ℕ) :
    (completedTensorShiftProductIso C D r α).hom ≫
      (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π (fun n ↦ C.obj (op n)) n) =
    Pi.π (fun n ↦ D.obj (op n)) n ≫ (α.app (op n)).hom := by
  rw [show (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π (fun n ↦ C.obj (op n)) n) =
      (PreservesProduct.iso (shiftFunctor (CochainComplex A ℤ) r)
        (fun n ↦ C.obj (op n))).hom ≫ Pi.π _ n from
      (piComparison_comp_π _ _ _).symm]
  dsimp only [completedTensorShiftProductIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, ← Category.assoc _ _ (Pi.π _ n), Iso.inv_hom_id]
  simp [Pi.mapIso]

private theorem productIso_square
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r) :
    completedTensorShiftOneSub D ≫ (completedTensorShiftProductIso C D r α).hom =
    (completedTensorShiftProductIso C D r α).hom ≫
      (completedTensorShiftOneSub C)⟦r⟧' := by
  apply (isLimitOfHasProductOfPreservesLimit
    (shiftFunctor (CochainComplex A ℤ) r) (fun n : ℕ ↦ C.obj (op n))).hom_ext
  intro ⟨n⟩
  change _ ≫ (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π _ n) =
    _ ≫ (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π _ n)
  rw [Category.assoc, productIso_π, ← Category.assoc]
  simp only [completedTensorShiftOneSub, towerTransitionEndomorphism, towerProductShift,
    Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π, Category.assoc]
  rw [← Functor.map_comp]
  simp only [Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π, Functor.map_sub,
    Functor.map_comp, Preadditive.comp_sub, productIso_π]
  rw [← Category.assoc (completedTensorShiftProductIso C D r α).hom, productIso_π]
  simp only [Category.assoc]
  congr 2
  exact (α.hom.naturality (homOfLE (Nat.le_succ n)).op)

private noncomputable def coneIso
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r) :
    CochainComplex.mappingCone (completedTensorShiftOneSub D) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))⟦r⟧ :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
    (Arrow.isoMk (completedTensorShiftProductIso C D r α)
      (completedTensorShiftProductIso C D r α) (productIso_square C D r α).symm) ≪≫
    (CochainComplex.mappingCone.shiftIso (completedTensorShiftOneSub C) r).symm

private theorem coneIso_formula
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r) :
    completedTensorShiftConeFormula C D r α (coneIso C D r α) := by
  constructor
  · intro j
    simp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.mappingCone.inr,
      HomologicalComplex.homotopyCofiber.inr_f, coneIso, CochainComplex.mappingCone.shiftIso,
      Int.reduceNeg, Iso.symm_mk, Iso.trans_hom,
      HomologicalComplex.homotopyCofiber.mapArrowIso_hom,
      HomologicalComplex.homotopyCofiber.mapArrowHom, Arrow.mk_right, Arrow.isoMk_hom_right,
      Arrow.mk_left, HomologicalComplex.comp_f,
      HomologicalComplex.homotopyCofiber_X,
      HomologicalComplex.homotopyCofiber.inrX_desc_f_assoc, Category.assoc,
      CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id]
    change (completedTensorShiftProductIso C D r α).hom.f j ≫
      (CochainComplex.mappingCone.inr ((completedTensorShiftOneSub C)⟦r⟧')).f j ≫ _ = _
    dsimp only [CochainComplex.mappingCone]
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl
  · intro i j h
    simp only [CochainComplex.shiftFunctor_obj_X', Int.reduceNeg,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v, coneIso,
      CochainComplex.mappingCone.shiftIso, Iso.symm_mk, Iso.trans_hom,
      HomologicalComplex.homotopyCofiber.mapArrowIso_hom,
      HomologicalComplex.homotopyCofiber.mapArrowHom, Arrow.mk_right,
      Arrow.mk_left, Arrow.isoMk_hom_left, HomologicalComplex.comp_f,
      HomologicalComplex.homotopyCofiber_X,
      HomologicalComplex.homotopyCofiber.inlX_desc_f_assoc, Homotopy.trans_hom,
      Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.compLeft_hom, add_zero, zero_add,
      Category.assoc, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ i j
      (show (ComplexShape.up ℤ).Rel j i from by change j + 1 = i; omega)]
    change (completedTensorShiftProductIso C D r α).hom.f i ≫
      (CochainComplex.mappingCone.inl ((completedTensorShiftOneSub C)⟦r⟧')).v i j h ≫ _ = _
    simp [CochainComplex.HomComplex.Cochain.shift_v']

private theorem productIso_naturality
    {C D C' D' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (α' : D' ≅ C' ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (c : C ⟶ C') (d : D ⟶ D')
    (h : d ≫ α'.hom = α.hom ≫ whiskerRight c (shiftFunctor _ r)) :
    Limits.Pi.map (fun n ↦ d.app (op n)) ≫ (completedTensorShiftProductIso C' D' r α').hom =
      (completedTensorShiftProductIso C D r α).hom ≫
        (Limits.Pi.map (fun n ↦ c.app (op n)))⟦r⟧' := by
  apply (isLimitOfHasProductOfPreservesLimit
    (shiftFunctor (CochainComplex A ℤ) r) (fun n : ℕ ↦ C'.obj (op n))).hom_ext
  intro ⟨n⟩
  change _ ≫ (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π _ n) =
    _ ≫ (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π _ n)
  rw [Category.assoc, productIso_π]
  simp only [← Category.assoc, Pi.map_π]
  rw [Category.assoc (completedTensorShiftProductIso C D r α).hom,
    ← Functor.map_comp, Pi.map_π, Functor.map_comp,
    ← Category.assoc, productIso_π, Category.assoc]
  simpa only [NatTrans.comp_app, whiskerRight_app, Iso.app_hom, Category.assoc] using
    congrArg (fun k ↦ Pi.π (fun m : ℕ ↦ D.obj (op m)) n ≫ k.app (op n)) h

private noncomputable def coneMap {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (c : C ⟶ C') :
    CochainComplex.mappingCone (completedTensorShiftOneSub C) ⟶
      CochainComplex.mappingCone (completedTensorShiftOneSub C') :=
  HomologicalComplex.homotopyCofiber.mapArrowHom _ _
    (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
    (Arrow.homMk (Limits.Pi.map (fun n ↦ c.app (op n)))
      (Limits.Pi.map (fun n ↦ c.app (op n))) (integralOperationsRoos_square c).symm)

private theorem coneMap_inr {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (c : C ⟶ C') (j : ℤ) :
    (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C)).f j ≫
      (coneMap c).f j = (Limits.Pi.map (fun n ↦ c.app (op n))).f j ≫
        (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C')).f j := by
  dsimp only [coneMap, HomologicalComplex.homotopyCofiber.mapArrowHom]
  change (HomologicalComplex.homotopyCofiber.inr _).f j ≫ _ = _
  rw [← HomologicalComplex.comp_f, HomologicalComplex.homotopyCofiber.inr_desc]
  rfl

private theorem coneMap_inl {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (c : C ⟶ C') (i j : ℤ) (h : i + (-1) = j) :
    (CochainComplex.mappingCone.inl (completedTensorShiftOneSub C)).v i j h ≫
      (coneMap c).f j = (Limits.Pi.map (fun n ↦ c.app (op n))).f i ≫
        (CochainComplex.mappingCone.inl (completedTensorShiftOneSub C')).v i j h := by
  dsimp only [coneMap, HomologicalComplex.homotopyCofiber.mapArrowHom]
  change HomologicalComplex.homotopyCofiber.inlX _ i j
    (show (ComplexShape.up ℤ).Rel j i from by change j + 1 = i; omega) ≫ _ = _
  rw [HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ i j
    (show (ComplexShape.up ℤ).Rel j i from by change j + 1 = i; omega)]
  rfl

attribute [local irreducible] coneIso coneMap completedTensorShiftProductIso
  completedTensorShiftOneSub

private theorem coneIso_naturality
    {C D C' D' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (α' : D' ≅ C' ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (c : C ⟶ C') (d : D ⟶ D')
    (h : d ≫ α'.hom = α.hom ≫ whiskerRight c (shiftFunctor _ r)) :
    coneMap d ≫ (coneIso C' D' r α').hom =
      (coneIso C D r α).hom ≫ (coneMap c)⟦r⟧' := by
  have e := productIso_naturality r α α' c d h
  ext j
  apply CochainComplex.mappingCone.ext_from _ (j + 1) j rfl
  · have h₁ := (coneIso_formula C D r α).2 (j + 1) j (by omega)
    have h₂ := (coneIso_formula C' D' r α').2 (j + 1) j (by omega)
    dsimp only [HomologicalComplex.comp_f]
    rw [← Category.assoc, coneMap_inl d (j + 1) j (by omega), Category.assoc, h₂]
    rw [reassoc_of% h₁]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.comp_id, CochainComplex.shiftFunctor_map_f',
      Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
    rw [← Category.assoc, coneMap_inl c (j + 1 + r) (j + r) (by omega),
      ← Category.assoc]
    exact congrArg (fun k ↦ r.negOnePow •
      (k ≫ (CochainComplex.mappingCone.inl (completedTensorShiftOneSub C')).v
        (j + 1 + r) (j + r) (by omega)))
      (congrArg (fun k ↦ k.f (j + 1)) e)
  · have h₁ := (coneIso_formula C D r α).1 j
    have h₂ := (coneIso_formula C' D' r α').1 j
    dsimp only [HomologicalComplex.comp_f]
    rw [← Category.assoc, coneMap_inr d j, Category.assoc, h₂]
    rw [reassoc_of% h₁]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.comp_id, CochainComplex.shiftFunctor_map_f']
    change (Limits.Pi.map (fun n ↦ d.app (op n))).f j ≫
        (completedTensorShiftProductIso C' D' r α').hom.f j ≫
          (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C')).f (j + r) =
      (completedTensorShiftProductIso C D r α).hom.f j ≫
        (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C)).f (j + r) ≫
          𝟙 _ ≫ (coneMap c).f (j + r)
    rw [Category.id_comp, coneMap_inr c (j + r), ← Category.assoc, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫
      (CochainComplex.mappingCone.inr (completedTensorShiftOneSub C')).f (j + r))
      (congrArg (fun k ↦ k.f j) e)

attribute [local semireducible] coneMap completedTensorShiftOneSub

private theorem roosIso_naturality
    {C D C' D' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (α' : D' ≅ C' ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (c : C ⟶ C') (d : D ⟶ D')
    (h : d ≫ α'.hom = α.hom ≫ whiskerRight c (shiftFunctor _ r)) :
    integralOperationsRoosMap d ≫
        (completedTensorShiftRoosIso C' D' r (coneIso C' D' r α')).hom =
      (completedTensorShiftRoosIso C D r (coneIso C D r α)).hom ≫
        (integralOperationsRoosMap c)⟦r⟧' := by
  change (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map (coneMap d) ≫
      ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (coneIso C' D' r α').hom ≫
          (shiftFunctorComm (CochainComplex A ℤ) r (-1 : ℤ)).hom.app _) =
    ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map (coneIso C D r α).hom ≫
      (shiftFunctorComm (CochainComplex A ℤ) r (-1 : ℤ)).hom.app _) ≫
        (shiftFunctor (CochainComplex A ℤ) r).map
          ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map (coneMap c))
  rw [← Category.assoc, ← Functor.map_comp, coneIso_naturality r α α' c d h,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
    (coneIso C D r α).hom ≫ ·)
    ((shiftFunctorComm (CochainComplex A ℤ) r (-1 : ℤ)).hom.naturality (coneMap c))

private noncomputable def roosShiftNaturalIso
    {B : Type c} [Category.{d} B] (F : B ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (V : B ⥤ B) (r : ℤ)
    (β : V ⋙ F ≅ F ⋙
      (whiskeringRight ℕᵒᵖ (CochainComplex A ℤ) (CochainComplex A ℤ)).obj
        (shiftFunctor (CochainComplex A ℤ) r)) :
    V ⋙ F ⋙ integralOperationsRoosFunctor ≅
      (F ⋙ integralOperationsRoosFunctor) ⋙ shiftFunctor (CochainComplex A ℤ) r :=
  NatIso.ofComponents (fun X ↦ completedTensorShiftRoosIso _ _ r
    (coneIso _ _ r (β.app X))) (by
      intro X Y f
      exact roosIso_naturality r (β.app X) (β.app Y)
        (F.map f) (F.map (V.map f)) (β.hom.naturality f))

end ProductCone

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The signed formula on every finite-level total-tensor generator. The source
uses Q[r], so its q-th term is Q^(q+r); the target is reindexed by the displayed
shift identification. The tower isomorphism itself asserts transition compatibility.
Source: Stacks Tags 011G and 012Z (blueprint: lem-sf-completed-tensor-shift-right). -/
def integralCompletedTensorFiniteShiftFormula (W : AlgebraicGeometry.Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α : (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r) : Prop :=
  ∀ (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (j + r)).val.obj U),
    (((α.hom.app (op n)).f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) (i + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow •
        integralOperationsTotalTensorSection l E W n P Q i (j + r) U x y)

section NormalizationStatement
attribute [local irreducible] integralOperationsTensorTowerFunctor
  integralOperationsGoodComplex completedTensorShiftOneSub completedTensorShiftRoosIso
  integralCompletedTensorComparison integralOperationsRoos

/-- Normalization on every flat-term K-flat pair. The finite signed tower map
induces the product map, then the specified cone map, then its [-1] shift.
The last equality identifies this concrete map with the derived natural comparison.
It quantifies over all resolutions, rather than selecting a special pair.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4); Stacks Tags 014E,
08TC and 06YT (blueprint: lem-sf-completed-tensor-shift-right). -/
def integralCompletedTensorRightShiftProperty (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ)
    (σ : completedTensorShiftSecond (DerivedCategory (integralTowerModules l E W)) r ⋙
        integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙
        shiftFunctor (DerivedCategory (integralTowerModules l E W)) r) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
    ∃ (hQ : integralOperationsGoodComplex l E W (Q.obj⟦r⟧))
      (α : (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧) ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r),
      integralCompletedTensorFiniteShiftFormula l E W P.obj Q.obj r α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧)) r α δ ∧
        (integralCompletedTensor l E W).map
            (𝟙 (DerivedCategory.Q.obj P.obj),
              ((DerivedCategory.Q.commShiftIso r).hom.app Q.obj)) ≫
          σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (shiftFunctor (DerivedCategory (integralTowerModules l E W)) r).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) =
        (integralCompletedTensorComparison l E W).hom.app (P, ⟨Q.obj⟦r⟧, hQ⟩) ≫
          DerivedCategory.Q.map
            (completedTensorShiftRoosIso
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj⟦r⟧)) r δ).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))

end NormalizationStatement

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] SheafOfModules.monoidalCategory

section TensorShift
variable {A : Type a} [Category.{b} A] [Preadditive A] [CategoryWithHomology A]
  (T : A ⥤ A ⥤ A) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).Additive]
private theorem tensorAcyclicShift (F K : CochainComplex A ℤ)
    [CochainComplex.HasMapBifunctor F K T]
    (h : (CochainComplex.mapBifunctor F K T).Acyclic) (r : ℤ) :
    (CochainComplex.mapBifunctor F (K⟦r⟧) T).Acyclic := by
  intro j
  apply HomologicalComplex.ExactAt.of_iso _
    (CochainComplex.mapBifunctorShift₂Iso F K T r).symm
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (h (r + j)).isZero_homology.of_iso
    ((CochainComplex.ShiftSequence.shiftIso A r j (r + j) rfl).app
      (CochainComplex.mapBifunctor F K T))
end TensorShift

section Generic
universe v w z
variable {C : Type v} [Category.{w} C] [EssentiallySmall.{z} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{z}}

private theorem kFlatShift (K : CochainComplex (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients.{v, w, z} (J := J) (R := R) K) (r : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients.{v, w, z} (J := J) (R := R) (K⟦r⟧) := by
  let A := SheafOfModules.{z} ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let : MonoidalCategory A := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let (M : A) : ((MonoidalCategory.curriedTensor A).obj M).Additive := by
    change (MonoidalCategory.tensorLeft M).Additive
    exact SheafOfModules.tensorLeft_additive_independent R M
  -- Supply the discrete colimits directly: unguided instance search times out here.
  have (I : Type) : HasColimitsOfShape (Discrete I) A :=
    have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{z}
        ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  intro F hF
  exact tensorAcyclicShift (MonoidalCategory.curriedTensor A) F K (h F hF) r
end Generic

private theorem goodShift (W : AlgebraicGeometry.Scheme.{t})
    (Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (r : ℤ) : integralOperationsGoodComplex l E W (Q.obj⟦r⟧) :=
  ⟨kFlatShift (R := completedIntegralCommRingSheafUnrestricted l E W)
    (J := AlgebraicGeometry.Scheme.ProEt.topology W) Q.obj Q.property.1 r,
    fun i ↦ Q.property.2 (i + r)⟩

private noncomputable def quotientShiftOnSite (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (integralTowerModules l E W)) r :=
  DerivedCategory.Q.commShiftIso r

private theorem quotientShiftOnSite_eq (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    quotientShiftOnSite l E W r = DerivedCategory.Q.commShiftIso r := rfl

private noncomputable abbrev goodShiftFunctor (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      (integralOperationsGoodComplex l E W).FullSubcategory :=
  (integralOperationsGoodComplex l E W).lift
    ((integralOperationsGoodComplex l E W).ι ⋙
      shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r)
    (fun Q ↦ goodShift l E W Q r)

private noncomputable def goodShiftInclusionIso
    (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    goodShiftFunctor l E W r ⋙ (integralOperationsGoodComplex l E W).ι ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r :=
  (integralOperationsGoodComplex l E W).liftCompιIso
    ((integralOperationsGoodComplex l E W).ι ⋙
      shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r)
    (fun Q ↦ goodShift l E W Q r)

private theorem goodShiftInclusionIso_hom_app (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (goodShiftInclusionIso l E W r).hom.app Q = 𝟙 (Q.obj⟦r⟧) := rfl

private noncomputable def goodShiftLocalizationIso
    (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    goodShiftFunctor l E W r ⋙ integralOperationsGoodLocalization l E W ≅
      integralOperationsGoodLocalization l E W ⋙
        shiftFunctor (DerivedCategory (integralTowerModules l E W)) r :=
  isoWhiskerRight (goodShiftInclusionIso l E W r) DerivedCategory.Q ≪≫
      isoWhiskerLeft (integralOperationsGoodComplex l E W).ι
        (quotientShiftOnSite l E W r)

set_option backward.isDefEq.respectTransparency false in
private theorem goodShiftLocalizationIso_hom_app (W : AlgebraicGeometry.Scheme.{t})
    (r : ℤ) (Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (goodShiftLocalizationIso l E W r).hom.app Q =
      (quotientShiftOnSite l E W r).hom.app Q.obj := by
  dsimp only [goodShiftLocalizationIso, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [goodShiftInclusionIso_hom_app]
  exact (congrArg (fun f ↦ f ≫ (quotientShiftOnSite l E W r).hom.app Q.obj)
    (DerivedCategory.Q.map_id (Q.obj⟦r⟧))).trans (Category.id_comp _)

section WhiskerShift
universe g h
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
  {C : Type e} [Category.{f} C] {D : Type g} [Category.{h} D]
private noncomputable def modelShiftIso (I : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (S : C ⥤ C) (Z : D ⥤ D) (T : B ⥤ C) (Q : C ⥤ D)
    (γ : U ⋙ I ≅ I ⋙ V) (τ : V ⋙ T ≅ T ⋙ S) (q : S ⋙ Q ≅ Q ⋙ Z) :
    U ⋙ (I ⋙ (T ⋙ Q)) ≅ (I ⋙ (T ⋙ Q)) ⋙ Z :=
  isoWhiskerRight γ (T ⋙ Q) ≪≫
    isoWhiskerRight (isoWhiskerLeft I τ) Q ≪≫ isoWhiskerLeft (I ⋙ T) q

private theorem modelShiftIso_hom_app (I : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (S : C ⥤ C) (Z : D ⥤ D) (T : B ⥤ C) (Q : C ⥤ D)
    (γ : U ⋙ I ≅ I ⋙ V) (τ : V ⋙ T ≅ T ⋙ S) (q : S ⋙ Q ≅ Q ⋙ Z) (X : A) :
    (modelShiftIso I U V S Z T Q γ τ q).hom.app X =
      (T ⋙ Q).map (γ.hom.app X) ≫ Q.map (τ.hom.app (I.obj X)) ≫
        q.hom.app (T.obj (I.obj X)) := rfl
end WhiskerShift

private abbrev finiteShiftIsoType (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :=
  completedTensorShiftSecond (CochainComplex (integralTowerModules l E W) ℤ) r ⋙
    integralOperationsTensorTowerFunctor l E W ≅
  integralOperationsTensorTowerFunctor l E W ⋙
    (whiskeringRight ℕᵒᵖ (CochainComplex (integralTowerModules l E W) ℤ)
      (CochainComplex (integralTowerModules l E W) ℤ)).obj
        (shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r)

private noncomputable abbrev goodSecondShift (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :=
  (𝟭 (integralOperationsGoodComplex l E W).FullSubcategory).prod
    (goodShiftFunctor l E W r)

private noncomputable def goodInputShiftIso (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    goodSecondShift l E W r ⋙ (integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W) ≅
    (integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W) ⋙
        completedTensorShiftSecond (DerivedCategory (integralTowerModules l E W)) r :=
  NatIso.prod (Iso.refl (integralOperationsGoodLocalization l E W))
    (goodShiftLocalizationIso l E W r)

set_option backward.isDefEq.respectTransparency false in
private theorem goodInputShiftIso_hom_app (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (goodInputShiftIso l E W r).hom.app (P, Q) =
      (𝟙 (DerivedCategory.Q.obj P.obj), (DerivedCategory.Q.commShiftIso r).hom.app Q.obj) := by
  change (𝟙 _, (goodShiftLocalizationIso l E W r).hom.app Q) = _
  rw [goodShiftLocalizationIso_hom_app, quotientShiftOnSite_eq]
  rfl

section RoosSiteConstruction
attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos

private noncomputable def roosShiftOnSite (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ)
    (β : finiteShiftIsoType l E W r) :
    completedTensorShiftSecond (CochainComplex (integralTowerModules l E W) ℤ) r ⋙
      integralOperationsTensorComplexFunctor l E W ≅
    integralOperationsTensorComplexFunctor l E W ⋙
      shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r :=
  by
  unfold integralOperationsTensorComplexFunctor
  exact roosShiftNaturalIso (integralOperationsTensorTowerFunctor l E W)
    (completedTensorShiftSecond (CochainComplex (integralTowerModules l E W) ℤ) r) r β

end RoosSiteConstruction

private theorem goodShiftInclusionEq (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ) :
    goodSecondShift l E W r ⋙ ((integralOperationsGoodComplex l E W).ι.prod
      (integralOperationsGoodComplex l E W).ι) =
    ((integralOperationsGoodComplex l E W).ι.prod
      (integralOperationsGoodComplex l E W).ι) ⋙
        completedTensorShiftSecond (CochainComplex (integralTowerModules l E W) ℤ) r := rfl

section OutputConstruction
attribute [local irreducible] roosShiftNaturalIso quotientShiftOnSite
  roosShiftOnSite integralOperationsTensorComplexFunctor
  goodShiftInclusionIso goodShiftLocalizationIso
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  integralOperationsRoos integralOperationsRoosMap DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private noncomputable def goodOutputShiftIso (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ)
    (β : finiteShiftIsoType l E W r) :
    goodSecondShift l E W r ⋙ integralOperationsTensorOnGood l E W ≅
      integralOperationsTensorOnGood l E W ⋙
        shiftFunctor (DerivedCategory (integralTowerModules l E W)) r :=
  by
  let A := CochainComplex (integralTowerModules l E W) ℤ
  let P := integralOperationsGoodComplex l E W
  let I := P.ι.prod P.ι
  exact modelShiftIso I (goodSecondShift l E W r)
    (completedTensorShiftSecond A r) (shiftFunctor A r)
    (shiftFunctor (DerivedCategory (integralTowerModules l E W)) r)
    (integralOperationsTensorComplexFunctor l E W) DerivedCategory.Q
    (eqToIso (goodShiftInclusionEq l E W r))
    (roosShiftOnSite l E W r β) (quotientShiftOnSite l E W r)

end OutputConstruction

section OutputComponents
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsGoodLocalization
  CategoryTheory.prod' CategoryTheory.uniformProd
  completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
attribute [local irreducible] integralOperationsTensorComplexFunctor
  integralOperationsTensorTowerFunctor roosShiftOnSite DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private theorem goodOutputShiftIso_hom_app (W : AlgebraicGeometry.Scheme.{t}) (r : ℤ)
    (β : finiteShiftIsoType l E W r)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (goodOutputShiftIso l E W r β).hom.app (P, Q) =
      DerivedCategory.Q.map
        ((roosShiftOnSite l E W r β).hom.app (P.obj, Q.obj)) ≫
      (quotientShiftOnSite l E W r).hom.app
        ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) := by
  simp only [goodOutputShiftIso, modelShiftIso_hom_app, eqToIso.hom, eqToHom_app,
    eqToHom_map]
  change (𝟙 _) ≫ _ ≫ _ = _
  exact Category.id_comp _

end OutputComponents

section Descent
set_option backward.isDefEq.respectTransparency false
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
  {C : Type e} [Category.{f} C]
private theorem liftIso (L : A ⥤ B) (G H : B ⥤ C) (T : A ⥤ C)
    (ε : L ⋙ G ≅ T) (S : C ⥤ C) [S.IsEquivalence]
    (hG : ∀ (G' : B ⥤ C) (ε' : L ⋙ G' ≅ T),
      ∃ ι : G ≅ G', isoWhiskerLeft L ι ≪≫ ε' = ε)
    (θ : L ⋙ H ≅ L ⋙ G ⋙ S) :
    ∃ σ : H ≅ G ⋙ S, isoWhiskerLeft L σ = θ := by
  let K := S.asEquivalence.inverse
  let η := S.asEquivalence.unitIso
  let ε' : L ⋙ H ⋙ K ≅ T :=
    isoWhiskerRight θ K ≪≫ (isoWhiskerLeft (L ⋙ G) η).symm ≪≫ ε
  obtain ⟨ι, hι⟩ := hG (H ⋙ K) ε'
  let μ : H ⋙ K ≅ (G ⋙ S) ⋙ K := ι.symm ≪≫ isoWhiskerLeft G η
  let ff := Functor.FullyFaithful.ofFullyFaithful ((whiskeringRight B C C).obj K)
  let σ : H ≅ G ⋙ S := ff.preimageIso μ
  refine ⟨σ, ?_⟩
  apply Iso.ext
  ext X
  apply K.map_injective
  have hσ := congrArg (fun n ↦ n.app (L.obj X)) (ff.map_preimage μ.hom)
  change K.map (σ.hom.app (L.obj X)) = _ at hσ
  change K.map (σ.hom.app (L.obj X)) = K.map (θ.hom.app X)
  rw [hσ]
  have h := congrArg (fun n ↦ n.hom.app X) hι
  dsimp only [ε', Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_inv, whiskerLeft_app, whiskerRight_app,
    NatTrans.comp_app] at h
  change ι.inv.app (L.obj X) ≫ η.hom.app (G.obj (L.obj X)) = K.map (θ.hom.app X)
  apply (cancel_epi (ι.hom.app (L.obj X))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply (cancel_mono (η.inv.app (G.obj (L.obj X)) ≫ ε.hom.app X)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.comp_obj, Functor.id_obj] using h.symm

private theorem descendShift (L : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B) (S : C ⥤ C) [S.IsEquivalence]
    (G : B ⥤ C) (T : A ⥤ C) (ε : L ⋙ G ≅ T) (κ : U ⋙ L ≅ L ⋙ V)
    (τ : U ⋙ T ≅ T ⋙ S)
    (hG : ∀ (G' : B ⥤ C) (ε' : L ⋙ G' ≅ T),
      ∃ ι : G ≅ G', isoWhiskerLeft L ι ≪≫ ε' = ε) :
    ∃ σ : V ⋙ G ≅ G ⋙ S, ∀ X,
      G.map (κ.hom.app X) ≫ σ.hom.app (L.obj X) ≫ S.map (ε.hom.app X) =
        ε.hom.app (U.obj X) ≫ τ.hom.app X := by
  let θ : L ⋙ V ⋙ G ≅ L ⋙ G ⋙ S :=
    isoWhiskerRight κ.symm G ≪≫ isoWhiskerLeft U ε ≪≫ τ ≪≫ isoWhiskerRight ε.symm S
  obtain ⟨σ, hσ⟩ := liftIso L G (V ⋙ G) T ε S hG θ
  refine ⟨σ, ?_⟩
  intro X
  have h := congrArg (fun k ↦ k.hom.app X) hσ
  change σ.hom.app (L.obj X) = _ at h
  rw [h]
  dsimp [θ]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.assoc,
    ← S.map_comp, Iso.inv_hom_id_app,
    S.map_id, Category.comp_id]
  change G.map (𝟙 (L.obj (U.obj X))) ≫ _ = _
  rw [G.map_id, Category.id_comp]

end Descent

section Universal
attribute [local semireducible] integralCompletedTensor
attribute [local irreducible] integralCompletedTensorDescent
set_option backward.isDefEq.respectTransparency false in
private theorem completedTensorUniversal (W : AlgebraicGeometry.Scheme.{t})
    (G' : (DerivedCategory (integralTowerModules l E W)) ×
      (DerivedCategory (integralTowerModules l E W)) ⥤
        DerivedCategory (integralTowerModules l E W))
    (ε' : ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
        integralOperationsTensorOnGood l E W) :
    ∃ ι : integralCompletedTensor l E W ≅ G', isoWhiskerLeft
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ι ≪≫ ε' =
          integralCompletedTensorComparison l E W := by
  exact ((integralCompletedTensorDescent l E W).universal G' ε').exists

end Universal

attribute [local irreducible] goodOutputShiftIso goodInputShiftIso
  roosShiftNaturalIso quotientShiftOnSite
  goodShiftInclusionIso goodShiftLocalizationIso integralCompletedTensorDescent
  integralOperationsTensorTowerFunctor
  integralCompletedTensorComparison coneIso
  integralCompletedTensorFiniteShiftFormula completedTensorShiftConeFormula
  integralOperationsGoodComplex completedTensorShiftOneSub completedTensorShiftProductIso
  completedTensorShiftRoosIso integralOperationsRoos integralOperationsRoosMap DerivedCategory.Q

end WeilConjectures
