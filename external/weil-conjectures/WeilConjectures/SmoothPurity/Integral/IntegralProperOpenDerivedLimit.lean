/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.SmoothPurity.Sf.SfCompactSupportTowerPresentation
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorOrdinaryTransport
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # The proper/open integral realization is a derived limit

Source: Bhatt--Scholze, Lemma 6.1.13, Definition 6.7.6 and Lemma 6.7.7;
Stacks Tags 0941 and 0F7J.
(blueprint: lem-pur-integral-proper-open-derived-limit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
open PurCompactSupport
open Opposite

private theorem transportDerivedLimit
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K L : ℕᵒᵖ ⥤ C}
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    [HasProduct (fun n : ℕ ↦ L.obj (op n))]
    (a : K ≅ L) {M N : C} (b : M ≅ N)
    (h : IsDerivedLimit (K := fun n : ℕ ↦ K.obj (op n))
      (fun n ↦ K.map (homOfLE n.le_succ).op) M) :
    IsDerivedLimit (K := fun n : ℕ ↦ L.obj (op n))
      (fun n ↦ L.map (homOfLE n.le_succ).op) N := by
  obtain ⟨p, δ, hc⟩ := h
  let d : (∏ᶜ (fun n : ℕ ↦ K.obj (op n))) ≅
      ∏ᶜ (fun n : ℕ ↦ L.obj (op n)) :=
    { hom := Limits.Pi.map (fun n ↦ a.hom.app (op n))
      inv := Limits.Pi.map (fun n ↦ a.inv.app (op n))
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  refine ⟨b.inv ≫ p ≫ d.hom, d.inv ≫ δ ≫ b.hom⟦(1 : ℤ)⟧', ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hc _
  refine Pretriangulated.Triangle.isoMk _ _ b.symm d.symm d.symm ?_ ?_ ?_
  · simp [Category.assoc]
  · exact (towerTransitionEndomorphism_natural_backward
      (fun n ↦ L.map (homOfLE n.le_succ).op)
      (fun n ↦ K.map (homOfLE n.le_succ).op)
      (fun n ↦ a.inv.app (op n))
      (fun n ↦ (a.inv.naturality (homOfLE n.le_succ).op).symm)).symm
  · simp [Category.assoc, ← Functor.map_comp]

private theorem directImageDerivedLimit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K) :
    let := integralOperationsDerivedCountableProducts l E Y
    IsDerivedLimit (sfDirectImageTransition l E f K)
      ((sfCompletedDerivedDirectImage l E f).obj K) := by
  let := integralOperationsDerivedCountableProducts l E Y
  let F := sfCompletedDerivedDirectImage l E f
  let := completed_derived_products l E f
  let a (n : ℕ) := (sfDerivedRestrictionComparison l E f n).app
    ((scalarReductionDerivedExtension l E X n).obj K)
  obtain ⟨hprod, δ, hδ⟩ := hK
  let := hprod
  let : HasProduct (fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj K)) :=
    hasProduct_of_equiv_of_iso (sfDirectImageTerm l E f K) _ (Equiv.refl ℕ) a
  obtain ⟨ε, hε⟩ := map_roos F
    (fun n ↦ (sfDerivedReductionTransition l E X n).app K) K
    (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app K)) δ hδ
  let p (n : ℕ) := F.map ((sfDerivedReductionUnit l E X n).app K) ≫ (a n).hom
  have hR : ∃ hp : HasProduct (sfDirectImageTerm l E f K), letI := hp
      ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K)
        (F.obj K) (Pi.lift p) ε := by
    apply roos_transport
      (X := fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj K))
      (Y := sfDirectImageTerm l E f K)
      (fun n ↦ F.map ((sfDerivedReductionTransition l E X n).app K))
      (sfDirectImageTransition l E f K) (Iso.refl (F.obj K)) a
      (fun n ↦ F.map ((sfDerivedReductionUnit l E X n).app K)) p
    · intro n
      dsimp only [sfDirectImageTransition, a, Iso.app_hom, Iso.app_inv]
      simp only [Iso.hom_inv_id_app_assoc]
      rfl
    · intro n
      simp only [p, Iso.refl_hom, Category.id_comp]
    · refine ⟨inferInstance, ε, ?_⟩
      simpa only [Pi.lift_comp_π] using hε
  obtain ⟨hp, ε', hε'⟩ := hR
  exact ⟨Pi.lift p, ε', hε'⟩

/-- The ambient proper/open realization is a derived limit of its finite support tower.

Source: Bhatt--Scholze, Lemma 6.1.13, Definition 6.7.6 and Lemma 6.7.7;
Stacks Tags 0941 and 0F7J.
(blueprint: lem-pur-integral-proper-open-derived-limit).

Proof: present the complete constructible input by its strict quotient-reduction
system, retaining the canonical scalar-adjunction units and quotient transitions.
Quasi-compact open extension commutes with homotopy limits by Bhatt--Scholze
Lemma 6.1.13: the open/closed recollement triangle expresses it using product-
preserving functors. Its ringed slice presentation has the same property. Apply
this to the input reduction system. Exact open extension commutes with quotient
tensor; hence its value is the total inverse limit of the finite open extensions.
Apply the separately derived proper image.
Its right-adjoint comparison commutes with total inverse limits, including their
units. The resulting finite terms are the recorded finite compact-support terms:
identify constant-coefficient direct images sectionwise and identify the open
extensions by their unit-normalized adjunctions. These identifications respect the
quotient-induced transitions, because scalar restriction and proper/open comparison
maps preserve their adjunction units. The strict Roos model gives a distinguished
triangle with transition endomorphism one minus shift. Transport this triangle
along the term and transition identifications. Its vertex is the ambient proper/open
image, and the resulting triangle is precisely its asserted derived-limit property.
Only the existence of this triangle is asserted; no faithfulness of finite reduction
on arbitrary morphisms, and no uniqueness of triangle extensions, is used. -/
theorem integralProperOpen_isDerivedLimit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hunit : IsUnit (l : D.k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    letI : HasCountableProducts (DerivedCategory (scalarReductionSource l E Y)) :=
      integralOperationsDerivedCountableProducts l E Y
    IsDerivedLimit (fun n : ℕ ↦ sfCompactSupportTransition l E c M n)
      ((image (completed l E) c).obj M) := by
  classical
  let := integralOperationsDerivedCountableProducts l E Y
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨o, SV, SX, tensor, r, d, e, htower⟩ :=
    CompactSupportProperImageTower.compactSupportProperImageTower l E D.k f hunit c
  let K : (IntegralOpenReduction.complete l E X).FullSubcategory :=
    ⟨M, (complete_unrestricted l E X M).mp hM.1.1⟩
  let J := (IntegralOpenReduction.shriek l E c.i o).obj M
  have hJ : IsSfDerivedComplete l E c.Z J :=
    (complete_unrestricted l E c.Z J).mpr (r.extensionComplete K)
  obtain ⟨_, hpresentation⟩ := sfCompactSupportTower_presentation l E c o d e
  obtain ⟨b, _⟩ := (htower K).2
  obtain ⟨⟨left⟩, ⟨right⟩⟩ := hpresentation K
  obtain ⟨eJ₀, _⟩ := OpenFactorCoherence.openFactorOrdinaryTransport l E c.i o
  let eJ : IntegralOpenReduction.shriek l E c.i o ≅
      (openExtension (completed l E) c.i).mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso eJ₀
  have hpush : proEtaleRingModuleDirectImage c.g ((completed l E).ring Y)
      ((completed l E).ring c.Z) ((completed l E).pull c.g) =
      sfCompletedModuleDirectImage l E c.g := by
    have hc : proEtaleRingDirectImageMap c.g ((completed l E).ring Y)
        ((completed l E).ring c.Z) ((completed l E).pull c.g) =
        sfCompletedCoefficientMap l E c.g :=
      ((proEtaleSheafAdjunction c.g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
    unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
    rw [hc]
  let := sfCompletedModuleDirectImage_additive l E c.g
  let eP : proEtaleRingDerivedDirectImage c.g ((completed l E).ring Y)
      ((completed l E).ring c.Z) ((completed l E).pull c.g) ≅
      sfCompletedDerivedDirectImage l E c.g :=
    Functor.rightDerivedFunctorNatIso (eqToIso hpush)
  let v : (sfCompletedDerivedDirectImage l E c.g).obj J ≅
      (image (completed l E) c).obj M :=
    (sfCompletedDerivedDirectImage l E c.g).mapIso (eJ.app M) ≪≫
      (eP.app ((openExtension (completed l E) c.i).mapDerivedCategory.obj M)).symm
  simpa only [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_obj] using
    transportDerivedLimit (left ≪≫ b ≪≫ right) v
      (by simpa only [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_obj] using
        directImageDerivedLimit l E c.g J hJ)

end WeilConjectures
