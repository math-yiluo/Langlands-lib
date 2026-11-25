/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Condensed scalar balancing and its unbounded chain normalization

Source: lemma-sp-reduction--1, proof Step 1, ordinary pullback/tensor comparison
(blueprint: lem-sp-proetale-scalar-balancing-chain).

The scalar-last tensor is the recorded relative tensor with the restricted regular coefficient
module. Its scalar-first presentation uses the existing projection formula and symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The coefficient `r_Z S_Z`, with its canonical restricted regular action.
Source: lemma-sp-reduction--1, Step 1
(blueprint: lem-sp-proetale-scalar-balancing-chain). -/
abbrev balancingCoefficient (Z : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) :=
  (Mod.comap (coefficientMap a Z)).obj (Mod.regular (condensedRingObj Λ' Z))

/-- The ordinary scalar-last tensor, using the existing relative tensor functor.
Source: lemma-sp-reduction--1, Step 1
(blueprint: lem-sp-proetale-scalar-balancing-chain). -/
abbrev balancingTensor (Z : Scheme.{u}) := tensorRight (balancingCoefficient a Z)

/-- The scalar-last to scalar-first presentation, with the scalar action on the scalar factor.
Source: lemma-sp-reduction--1, Step 1
(blueprint: lem-sp-proetale-scalar-balancing-chain). -/
def balancingExtensionIso (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    M ⊗ balancingCoefficient a Z ≅
      (Mod.comap (coefficientMap a Z)).obj ((Mod.extendScalars (coefficientMap a Z)).obj M) :=
  (β_ M (balancingCoefficient a Z)) ≪≫
    Mod.projectionIso (coefficientMap a Z) (Mod.regular (condensedRingObj Λ' Z)) M ≪≫
    (Mod.comap (coefficientMap a Z)).mapIso (λ_ _)

attribute [local irreducible] pullIso comapUpperStarIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The full pairing equation for the inverse-image unit-section formula. Applying the sheaf
inverse-image adjunction and then evaluating pure local tensors gives exactly
`f⁻¹(x ⊗ s) ↦ f⁻¹x ⊗ α_S(f⁻¹s)`; this equation also covers tensors which are only locally pure.
Source: lemma-sp-reduction--1, Step 1
(blueprint: lem-sp-proetale-scalar-balancing-chain). -/
def IsCondensedScalarBalancing
    (t : balancingTensor a Y ⋙ upperStar Λ f ≅ upperStar Λ f ⋙ balancingTensor a X) : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y),
    (f)^*[Ab.{u + 1}].map (Mod.tensorObjπ M (balancingCoefficient a Y)) ≫
        upperStarUnitHom Λ f (M ⊗ balancingCoefficient a Y) ≫ (t.hom.app M).hom =
      Functor.OplaxMonoidal.δ (f)^*[Ab.{u + 1}] M.X (condensedRingObj Λ' Y) ≫
        (upperStarUnitHom Λ f M ⊗ₘ condensedPullbackHom Λ' f) ≫
        Mod.tensorObjπ ((upperStar Λ f).obj M) (balancingCoefficient a X)

private def balancingCoefficientIso :
    (upperStar Λ f).obj (balancingCoefficient a Y) ≅ balancingCoefficient a X :=
  ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app _) ≪≫
    Mod.isoMk (asIso (condensedPullbackHom Λ' f)) (by
      have hs : inv (condensedPullbackHom Λ f) ≫
          (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
          coefficientMap a X := by
        rw [map_coefficientMap_comp_condensedPullbackHom,
          IsIso.inv_hom_id_assoc]
      change (inv (condensedPullbackHom Λ f) ▷ _ ≫
          Functor.LaxMonoidal.μ (f)^*[Ab.{u + 1}] _ _ ≫
            (f)^*[Ab.{u + 1}].map (coefficientMap a Y ▷ _ ≫ MonObj.mul)) ≫
          condensedPullbackHom Λ' f = _
      rw [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc]
      change (inv (condensedPullbackHom Λ f) ▷ _ ≫
          (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ▷ _ ≫
            MonObj.mul) ≫ condensedPullbackHom Λ' f =
          condensedRingObj Λ X ◁ condensedPullbackHom Λ' f ≫
            coefficientMap a X ▷ condensedRingObj Λ' X ≫ MonObj.mul
      rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def,
        Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
        Category.assoc, hs]
      rw [whisker_exchange_assoc])

-- Avoid repeatedly expanding the concrete coefficient transports during elaboration.
omit [IsCommMonObj Λ'] in
private lemma balancingCoefficientIso_unit :
    upperStarUnitHom Λ f (balancingCoefficient a Y) ≫
      (balancingCoefficientIso a f).hom.hom = condensedPullbackHom Λ' f := by
  let N := ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
    (balancingCoefficient a Y)
  change Mod.extendUnitHom (condensedPullbackHom Λ f) N ≫
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app N).hom ≫
      condensedPullbackHom Λ' f = condensedPullbackHom Λ' f
  rw [Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app_assoc]

attribute [local irreducible] balancingCoefficientIso

private def balancingIso :
    balancingTensor a Y ⋙ upperStar Λ f ≅ upperStar Λ f ⋙ balancingTensor a X :=
  NatIso.ofComponents (fun M ↦
    (asIso (Functor.OplaxMonoidal.δ (upperStar Λ f) M (balancingCoefficient a Y))) ≪≫
      whiskerLeftIso _ (balancingCoefficientIso a f)) (by
        intro M N g
        change (upperStar Λ f).map (g ▷ balancingCoefficient a Y) ≫
          (Functor.OplaxMonoidal.δ (upperStar Λ f) N (balancingCoefficient a Y) ≫
            (upperStar Λ f).obj N ◁ (balancingCoefficientIso a f).hom) =
          (Functor.OplaxMonoidal.δ (upperStar Λ f) M (balancingCoefficient a Y) ≫
            (upperStar Λ f).obj M ◁ (balancingCoefficientIso a f).hom) ≫
              (upperStar Λ f).map g ▷ balancingCoefficient a X
        rw [← Functor.OplaxMonoidal.δ_natural_left_assoc,
          Category.assoc, whisker_exchange])

-- Avoid repeatedly expanding the concrete coefficient transports during elaboration.
omit [IsCommMonObj Λ'] in
private lemma balancingIso_pairing : IsCondensedScalarBalancing a f (balancingIso a f) := by
  intro M
  change _ ≫ _ ≫ ((Functor.OplaxMonoidal.δ (upperStar Λ f) M
    (balancingCoefficient a Y)).hom ≫
      (((upperStar Λ f).obj M) ◁ (balancingCoefficientIso a f).hom).hom) = _
  erw [map_tensorObjπ_upperStarUnitHom_δ_hom_assoc,
    Mod.tensorObjπ_whiskerLeft]
  change _ ≫ _ ≫ ((upperStar Λ f).obj M).X ◁
    (balancingCoefficientIso a f).hom.hom ≫ _ = _
  erw [tensorHom_comp_whiskerLeft_assoc, balancingCoefficientIso_unit a f]
  rfl

omit [IsCommMonObj Λ'] in
private lemma balancingIso_hom_eq :
    (balancingIso a f).hom =
      Functor.OplaxMonoidal.δRightNatTrans (upperStar Λ f) (balancingCoefficient a Y) ≫
        Functor.whiskerLeft (upperStar Λ f)
          ((curriedTensor _).flip.map (balancingCoefficientIso a f).hom) := rfl

attribute [local irreducible] balancingIso

omit [IsCommMonObj Λ'] in
private lemma balancingIso_unique
    (t' : balancingTensor a Y ⋙ upperStar Λ f ≅ upperStar Λ f ⋙ balancingTensor a X)
    (ht' : IsCondensedScalarBalancing a f t') : t' = balancingIso a f := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  apply (cancel_epi ((f)^*[Ab.{u + 1}].map
    (Mod.tensorObjπ M (balancingCoefficient a Y)) ≫
      upperStarUnitHom Λ f (M ⊗ balancingCoefficient a Y))).1
  exact (ht' M).trans ((balancingIso_pairing a f M).symm)

private lemma balancingExtensionIso_pairing (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    Mod.tensorObjπ M (balancingCoefficient a Z) ≫ (balancingExtensionIso a Z M).hom.hom =
      (β_ M.X (condensedRingObj Λ' Z)).hom ≫ Mod.extendπ (coefficientMap a Z) M := by
  dsimp only [balancingExtensionIso, Iso.trans_hom, Mod.comp_hom', Functor.mapIso_hom,
    Mod.comap_map_hom]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc]
  exact congrArg ((β_ M.X (condensedRingObj Λ' Z)).hom ≫ ·)
    (Mod.tensorObjπ_unit_projectionHom_hom_leftUnitor_hom (coefficientMap a Z) M)

-- Avoid repeatedly expanding the concrete coefficient transports during elaboration.
private lemma balancingPull_unit
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a Y) M) ≫
      upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
        ((pullIso a f).inv.app M).hom =
      upperStarUnitHom Λ f M ≫
        Mod.extendUnitHom (coefficientMap a X) ((upperStar Λ f).obj M) := by
  have hc := congrArg Mod.Hom.hom (Iso.hom_inv_id_app (pullIso a f) M)
  simp only [Mod.comp_hom', Mod.id_hom'] at hc
  have h := congrArg (fun k ↦ k ≫ ((pullIso a f).inv.app M).hom)
    (upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom a f M)
  simp only [Category.assoc, hc] at h
  exact h.symm

private lemma balancingPull_action
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    (f)^*[Ab.{u + 1}].map (Mod.act N.X) ≫ upperStarUnitHom Λ' f N =
      Functor.OplaxMonoidal.δ (f)^*[Ab.{u + 1}] (condensedRingObj Λ' Y) N.X ≫
        condensedPullbackHom Λ' f ▷ (f)^*[Ab.{u + 1}].obj N.X ≫
          condensedRingObj Λ' X ◁ upperStarUnitHom Λ' f N ≫
            Mod.act ((upperStar Λ' f).obj N).X := by
  rw [upperStarUnitHom, ← extendScalarsIsoComapInv_inv_app_hom]
  rw [← Mod.act_hom]
  change _ = Functor.OplaxMonoidal.δ (f)^*[Ab.{u + 1}] _ _ ≫
    condensedPullbackHom Λ' f ▷ _ ≫
      (inv (condensedPullbackHom Λ' f) ▷ _ ≫
        Functor.LaxMonoidal.μ (f)^*[Ab.{u + 1}] _ _ ≫
          (f)^*[Ab.{u + 1}].map (Mod.act N.X)) ≫ _
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight,
    Category.id_comp, Functor.Monoidal.δ_μ_assoc]

private lemma balancingPull_projection
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*[Ab.{u + 1}].map (Mod.extendπ (coefficientMap a Y) M) ≫
        upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
          ((pullIso a f).inv.app M).hom =
      Functor.OplaxMonoidal.δ (f)^*[Ab.{u + 1}] (condensedRingObj Λ' Y) M.X ≫
        (condensedPullbackHom Λ' f ⊗ₘ upperStarUnitHom Λ f M) ≫
          Mod.extendπ (coefficientMap a X) ((upperStar Λ f).obj M) := by
  have ha := balancingPull_action (Λ' := Λ') f
    ((Mod.extendScalars (coefficientMap a Y)).obj M)
  rw [← Mod.whiskerLeft_extendUnitHom_smul', Functor.map_comp]
  erw [Category.assoc, reassoc_of% ha]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc, whisker_exchange_assoc, Mod.act_hom]
  simp only [← whiskerLeft_comp_assoc]
  rw [balancingPull_unit, whiskerLeft_comp_assoc, Mod.whiskerLeft_extendUnitHom_smul']
  rw [MonoidalCategory.tensorHom_def, Category.assoc]

private lemma balancingIso_scalar_projection
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStar Λ f).map (balancingExtensionIso a Y M).hom ≫
      (comapUpperStarIso a f).inv.app _ ≫
        (Mod.comap (coefficientMap a X)).map ((pullIso a f).inv.app M) =
    (balancingIso a f).hom.app M ≫
      (balancingExtensionIso a X ((upperStar Λ f).obj M)).hom := by
  apply Mod.hom_ext
  apply (cancel_epi ((f)^*[Ab.{u + 1}].map
    (Mod.tensorObjπ M (balancingCoefficient a Y)) ≫
      upperStarUnitHom Λ f (M ⊗ balancingCoefficient a Y))).1
  simp only [Mod.comp_hom', Mod.comap_map_hom, Category.assoc]
  rw [upperStarUnitHom_map_hom_assoc, ← Functor.map_comp_assoc,
    balancingExtensionIso_pairing a Y M, Functor.map_comp]
  have hb := congrArg (fun k ↦ k ≫ ((pullIso a f).inv.app M).hom)
    (upperStarUnitHom_comapUpperStarIso_inv_app_hom a f
      ((Mod.extendScalars (coefficientMap a Y)).obj M))
  simp only [Category.assoc] at hb
  trans ((f)^*[Ab.{u + 1}].map (β_ M.X (condensedRingObj Λ' Y)).hom ≫
    (f)^*[Ab.{u + 1}].map (Mod.extendπ (coefficientMap a Y) M)) ≫
      upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
        ((pullIso a f).inv.app M).hom
  · exact congrArg (((f)^*[Ab.{u + 1}].map
      (β_ M.X (condensedRingObj Λ' Y)).hom ≫
        (f)^*[Ab.{u + 1}].map (Mod.extendπ (coefficientMap a Y) M)) ≫ ·) hb
  rw [Category.assoc]
  erw [balancingPull_projection a f M]
  conv_rhs =>
    erw [reassoc_of% (balancingIso_pairing a f M),
      balancingExtensionIso_pairing a X ((upperStar Λ f).obj M)]
  rw [Functor.map_braiding, Category.assoc, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, BraidedCategory.braiding_naturality_assoc]

-- Identify the scalar-first map on the entire tensor projection.
private lemma balancingIso_scalar
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ∃ s : (upperStar Λ' f).obj ((Mod.extendScalars (coefficientMap a Y)).obj M) ≅
        (Mod.extendScalars (coefficientMap a X)).obj ((upperStar Λ f).obj M),
      (Mod.comap (coefficientMap a X)).map s.hom =
        (comapUpperStarIso a f).hom.app _ ≫
          (upperStar Λ f).map (balancingExtensionIso a Y M).inv ≫
            (balancingIso a f).hom.app M ≫
              (balancingExtensionIso a X ((upperStar Λ f).obj M)).hom := by
  have h := balancingIso_scalar_projection a f M
  refine ⟨(pullIso a f).symm.app M, ?_⟩
  have h' := congrArg (fun k ↦ (comapUpperStarIso a f).hom.app
    ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
      (upperStar Λ f).map (balancingExtensionIso a Y M).inv ≫ k) h
  rw [← (upperStar Λ f).map_comp_assoc, (balancingExtensionIso a Y M).inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc (comapUpperStarIso a f)] at h'
  exact h'

private lemma balancingChain_normalization
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    (M : C) (N : D) (c : F.obj M ≅ N)
    (t : tensorRight M ⋙ F ≅ F ⋙ tensorRight N)
    (ht : t.hom = Functor.OplaxMonoidal.δRightNatTrans F M ≫
      Functor.whiskerLeft F ((curriedTensor D).flip.map c.hom))
    (P : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P).hom ≫
          (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P =
      HomologicalComplex.mapBifunctorComparison
          (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P
          ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
        HomologicalComplex.mapBifunctorMap
          (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P))
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
            (HomologicalComplex.single D (.up ℤ) 0).map c.hom)
          (curriedTensor D) (.up ℤ) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) N
          ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  let K := (F.mapHomologicalComplex (.up ℤ)).obj P
  let e := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) (F.obj M) K
  let e' := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N K
  let d := HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M)
  let q := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M
  let r := (HomologicalComplex.single _ (.up ℤ) 0).map c.hom
  have h₁ : (F.mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P).inv ≫ d ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K) q (curriedTensor _) (.up ℤ) ≫ e.hom =
      (NatTrans.mapHomologicalComplex
        (Functor.OplaxMonoidal.δRightNatTrans F M) (.up ℤ)).app P :=
    CochainComplex.mapBifunctorComparison_δNatTrans_single₂ F P M
  have h₂ : (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map c.hom)
      (.up ℤ)).app K ≫ e'.inv =
      e.inv ≫ HomologicalComplex.mapBifunctorMap (𝟙 K) r (curriedTensor _) (.up ℤ) :=
    CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂ (curriedTensor _) c.hom K
  have h₂' : HomologicalComplex.mapBifunctorMap (𝟙 K) r (curriedTensor _) (.up ℤ) ≫
      e'.hom = e.hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map c.hom) (.up ℤ)).app K := by
    rw [← cancel_epi e.inv, ← reassoc_of% h₂, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have h₃ : (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P =
      (NatTrans.mapHomologicalComplex
        (Functor.OplaxMonoidal.δRightNatTrans F M) (.up ℤ)).app P ≫
      (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map c.hom) (.up ℤ)).app K := by
    change (NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app P = _
    rw [ht]
    rfl
  have hcomp : HomologicalComplex.mapBifunctorMap (𝟙 K) (q ≫ r)
      (curriedTensor _) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 K) q (curriedTensor _) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K) r (curriedTensor _) (.up ℤ) := by
    simp only [HomologicalComplex.mapBifunctorMap, CategoryTheory.Functor.map_id,
      NatTrans.id_app, Category.id_comp, CategoryTheory.Functor.map_comp,
      HomologicalComplex₂.total.map_comp]
  change (F.mapHomologicalComplex (.up ℤ)).map
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P).hom ≫
      (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P =
    d ≫ HomologicalComplex.mapBifunctorMap (𝟙 K) (q ≫ r) (curriedTensor _) (.up ℤ) ≫ e'.hom
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P).inv)).1
  rw [Iso.inv_hom_id_map_assoc, h₃, hcomp, Category.assoc, h₂']
  rw [reassoc_of% h₁]

-- The proof compares several presentations of the degree-zero coefficient total.
/-- Ordinary condensed scalar balancing, its transported scalar action and chain normalization.
Source: lemma-sp-reduction--1, proof Step 1
(blueprint: lem-sp-proetale-scalar-balancing-chain).

Proof:
1. Naturality of the coefficient comparison gives the coefficient square. Transport extension
   along each coefficient isomorphism to restriction along its inverse. The two actions then
   agree by that square, and beta is the identity on the inverse-image sheaf.
2. The strong monoidal abelian inverse image preserves coequalizers. Its relative tensor
   comparison, followed by the coefficient isomorphism on the second factor, gives t.
3. The tensorator's adjunction-unit equation gives the full pairing equation below. Adjunction
   and the balanced tensor universal property show this determines t uniquely.
4. After projection to the scalar-first presentations, t beta respects the scalar action:
   both action pairings send (m,s,b) to m tensor sb. Descend through the tensor coequalizers.
5. Naturality at each differential gives the chain equation and the inverse equation. The
   components and their inverses therefore give a natural chain isomorphism for every complex.
6. In total tensor with the coefficient in degree zero only (i,0) contributes in degree i;
   its differential is d tensor 1. Hence the signed-total comparison is this degreewise map.
No flatness, K-flatness, torsion or boundedness is used.
-/
theorem condensedScalarBalancingChain :
    ((f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
      condensedPullbackHom Λ f ≫ coefficientMap a X) ∧
    (∀ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y),
      upperStarUnitHom Λ' f N ≫ ((comapUpperStarIso a f).hom.app N).hom =
        upperStarUnitHom Λ f ((Mod.comap (coefficientMap a Y)).obj N)) ∧
    ∃ c : (upperStar Λ f).obj (balancingCoefficient a Y) ≅ balancingCoefficient a X,
      upperStarUnitHom Λ f (balancingCoefficient a Y) ≫ c.hom.hom =
        condensedPullbackHom Λ' f ∧
    ∃ t : balancingTensor a Y ⋙ upperStar Λ f ≅ upperStar Λ f ⋙ balancingTensor a X,
      IsCondensedScalarBalancing a f t ∧
      (∀ t' : balancingTensor a Y ⋙ upperStar Λ f ≅ upperStar Λ f ⋙ balancingTensor a X,
        IsCondensedScalarBalancing a f t' → t' = t) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y),
        ∃ s : (upperStar Λ' f).obj ((Mod.extendScalars (coefficientMap a Y)).obj M) ≅
            (Mod.extendScalars (coefficientMap a X)).obj ((upperStar Λ f).obj M),
          (Mod.comap (coefficientMap a X)).map s.hom =
            (comapUpperStarIso a f).hom.app _ ≫
              (upperStar Λ f).map (balancingExtensionIso a Y M).inv ≫ t.hom.app M ≫
              (balancingExtensionIso a X ((upperStar Λ f).obj M)).hom) ∧
      ∃ T : (balancingTensor a Y ⋙ upperStar Λ f).mapHomologicalComplex (.up ℤ) ≅
          (upperStar Λ f ⋙ balancingTensor a X).mapHomologicalComplex (.up ℤ),
        (∀ (P : CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (condensedRingObj Λ Y)) ℤ) (i : ℤ),
          (T.hom.app P).f i = t.hom.app (P.X i) ∧
            (T.inv.app P).f i = t.inv.app (P.X i)) ∧
        (∀ (P : CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (condensedRingObj Λ Y)) ℤ) (i j : ℤ),
          (balancingTensor a Y ⋙ upperStar Λ f).map (P.d i j) ≫ t.hom.app (P.X j) =
            t.hom.app (P.X i) ≫ (upperStar Λ f ⋙ balancingTensor a X).map (P.d i j)) ∧
        (∀ P : CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (condensedRingObj Λ Y)) ℤ,
          ((upperStar Λ f).mapHomologicalComplex (.up ℤ)).map
              (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
                (balancingCoefficient a Y) P).hom ≫ T.hom.app P =
            HomologicalComplex.mapBifunctorComparison
                (Functor.OplaxMonoidal.δNatTrans (upperStar Λ f)) (.up ℤ) P
                ((HomologicalComplex.single _ (.up ℤ) 0).obj (balancingCoefficient a Y)) ≫
              HomologicalComplex.mapBifunctorMap
                (𝟙 (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P))
                (((HomologicalComplex.singleMapHomologicalComplex
                    (upperStar Λ f) (.up ℤ) 0).hom.app (balancingCoefficient a Y)) ≫
                  (HomologicalComplex.single _ (.up ℤ) 0).map c.hom)
                (curriedTensor _) (.up ℤ) ≫
              (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
                (balancingCoefficient a X)
                (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)).hom)
    := by
  refine ⟨map_coefficientMap_comp_condensedPullbackHom a f, ?_,
    balancingCoefficientIso a f, balancingCoefficientIso_unit a f,
    balancingIso a f, balancingIso_pairing a f, balancingIso_unique a f,
    balancingIso_scalar a f,
    NatIso.mapHomologicalComplex (balancingIso a f) (.up ℤ), ?_, ?_, ?_⟩
  · intro N
    simpa only [Mod.extendRestrictAdjunction_unit_app_hom] using
      extendUnit_comapUpperStarIso_hom_app_hom a f N
  · intro P i
    exact ⟨rfl, rfl⟩
  · intro P i j
    exact (balancingIso a f).hom.naturality (P.d i j)
  · exact balancingChain_normalization (upperStar Λ f) (balancingCoefficient a Y)
      (balancingCoefficient a X) (balancingCoefficientIso a f) (balancingIso a f)
      (balancingIso_hom_eq a f)
end AlgebraicGeometry.ProEtale.CondensedRing
