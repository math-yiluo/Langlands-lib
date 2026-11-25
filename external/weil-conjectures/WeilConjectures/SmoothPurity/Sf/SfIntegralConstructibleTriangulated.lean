/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-!
# Triangulation of the intrinsic integral constructible category

Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1, for the uniform-reduction
variant in blueprint order 1459; Stacks Project, Tag 0999
(blueprint: lem-weil-integral-constructible-triangulated).

The predicate is the recorded `sfIntegralConstructible`, over the completed coefficient
sheaf on the small pro-etale site. The two instances below make Mathlib's inherited
shift, pretriangulation, triangulation and exact full-subcategory inclusion available
on `sfIntegralConstructibleCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem reflective_triangulated {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : ObjectProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
    [F.CommShift ℤ] [NatTrans.CommShift η ℤ]
    (hout : ∀ X, P (F.obj X))
    (hfix : ∀ X, P X ↔ IsIso (η.app X))
    (href : ∀ X L, P L → Function.Bijective (fun f : F.obj X ⟶ L ↦ η.app X ≫ f)) :
    P.IsTriangulated := by
  have hshift (X : C) (n : ℤ) :
      (η.app X)⟦n⟧' = η.app (X⟦n⟧) ≫ (F.commShiftIso n).hom.app X := by
    simpa using NatTrans.shift_app_comm η n X
  have : P.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro X hX
    apply (hfix _).mpr
    have := (hfix X).mp hX
    rw [NatTrans.app_shift η n X]
    infer_instance
  have hle : P ≤ P.leftOrthogonal.rightOrthogonal := fun _ hX _ f hL ↦ hL f hX
  have heq : P = P.leftOrthogonal.rightOrthogonal := by
    apply le_antisymm hle
    intro X hX
    obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (η.app X)
    let T := Triangle.mk (η.app X) g δ
    have hZ : P.leftOrthogonal Z := by
      intro L f hL
      have hgf : g ≫ f = 0 := by
        apply (href X L hL).1
        change η.app X ≫ (g ≫ f) = η.app X ≫ 0
        rw [← Category.assoc]
        have hzero : η.app X ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT
        simp only [hzero, zero_comp, comp_zero]
      obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ T hT f hgf
      obtain ⟨b, hb⟩ := (href (X⟦(1 : ℤ)⟧) L hL).2 a
      have hab : a = (η.app X)⟦(1 : ℤ)⟧' ≫
          ((F.commShiftIso (1 : ℤ)).inv.app X ≫ b) := by
        rw [hshift]
        simpa [Category.assoc] using hb.symm
      rw [ha, hab, ← Category.assoc]
      have hzero : δ ≫ (η.app X)⟦(1 : ℤ)⟧' = 0 :=
        comp_distTriang_mor_zero₃₁ T hT
      simpa [T] using congrArg (fun z ↦ z ≫
        ((F.commShiftIso (1 : ℤ)).inv.app X ≫ b)) hzero
    have hR := hle _ (hout X)
    have hZ' : P.leftOrthogonal.rightOrthogonal Z :=
      P.leftOrthogonal.rightOrthogonal.ext_of_isTriangulatedClosed₃ T hT hX hR
    have hz : IsZero Z := (IsZero.iff_id_eq_zero Z).mpr (hZ' (𝟙 Z) hZ)
    apply (hfix X).mpr
    exact (Triangle.isZero₃_iff_isIso₁ T hT).mp hz
  rw [heq]
  infer_instance

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem augmentedRoos_iso {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (F : ℕ → C ⥤ C)
    (η : ∀ n, 𝟭 C ⟶ F n) (τ : ∀ n, F (n + 1) ⟶ F n)
    {K L : C} (e : K ≅ L)
    (h : ∃ hp : HasProduct (fun n ↦ (F n).obj K),
      let := hp
      ∃ δ : (∏ᶜ fun n ↦ (F n).obj K) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n ↦ (τ n).app K) K
          (Pi.lift (fun n ↦ (η n).app K)) δ) :
    ∃ hp : HasProduct (fun n ↦ (F n).obj L),
      let := hp
      ∃ δ : (∏ᶜ fun n ↦ (F n).obj L) ⟶ L⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n ↦ (τ n).app L) L
          (Pi.lift (fun n ↦ (η n).app L)) δ := by
  obtain ⟨hp, δ, hδ⟩ := h
  let := hp
  let : HasProduct (fun n ↦ (F n).obj L) :=
    hasProduct_of_equiv_of_iso (fun n ↦ (F n).obj K)
      (fun n ↦ (F n).obj L) (Equiv.refl ℕ) (fun n ↦ (F n).mapIso e.symm)
  let p : (∏ᶜ fun n ↦ (F n).obj K) ≅ (∏ᶜ fun n ↦ (F n).obj L) :=
    { hom := Limits.Pi.map (fun n ↦ (F n).map e.hom)
      inv := Limits.Pi.map (fun n ↦ (F n).map e.inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc, ← Functor.map_comp]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc, ← Functor.map_comp] }
  refine ⟨inferInstance, p.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, ?_⟩
  apply isomorphic_distinguished _ hδ _
  refine Triangle.isoMk _ _ e.symm p.symm p.symm ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simpa [p, Category.assoc] using ((η n).naturality e.inv).symm
  · exact towerTransitionEndomorphism_natural_backward
      (fun n ↦ (τ n).app L) (fun n ↦ (τ n).app K)
      (fun n ↦ (F n).map e.inv) (fun n ↦ (τ n).naturality e.inv) |>.symm
  · simp [p, Category.assoc, ← Functor.map_comp]

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem intrinsic_iso (Y : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete Y d) := by
  constructor
  intro K L e hK
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison Y d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem intrinsic_tri (Y : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsTriangulated (PbcIsIntrinsicallyComplete Y d) := by
  let P : ObjectProperty (PbcCompletedDerived Y d) := PbcIsIntrinsicallyComplete Y d
  let F := pbcActualCompletion d Y
  let η := pbcActualCompletionUnit d Y
  let adj := Adjunction.ofIsRightAdjoint P.ι
  have := intrinsic_iso Y d
  have : NatTrans.CommShift η ℤ :=
    (pbcActualCompletionShift_exists d Y).exists.choose_spec
  apply reflective_triangulated P F η
  · intro X
    exact (P.ι.leftAdjoint.obj X).property
  · intro X
    rw [show IsIso (η.app X) ↔ P.ι.essImage X from
      adj.isIso_unit_app_iff_mem_essImage]
    constructor
    · intro h
      exact ⟨⟨X, h⟩, ⟨Iso.refl _⟩⟩
    · rintro ⟨L, ⟨e⟩⟩
      exact P.prop_of_iso e L.property
  · intro X L hL
    have hb := (ObjectProperty.isLocal_adj_unit_app adj X) L ⟨⟨L, hL⟩, rfl⟩
    exact hb

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem sf_complete_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (WeilConjectures.IsSfDerivedComplete l E Y) := by
  constructor
  intro K L e hK
  exact augmentedRoos_iso (WeilConjectures.sfDerivedReductionRestricted l E Y)
    (WeilConjectures.sfDerivedReductionUnit l E Y)
    (WeilConjectures.sfDerivedReductionTransition l E Y) e hK

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem sf_complete_tri (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsTriangulated (IsSfDerivedComplete l E Y) := by
  let P : ObjectProperty (PbcCompletedDerived Y (pbcIntegralDatum l E)) :=
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
  let e := purCoefficientModel l E Y
  let := (integralDetailedCoefficientRestriction_exact Y l E).1
  let := (integralDetailedCoefficientRestriction_exact Y l E).2
  let F := (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison Y l E).hom).mapDerivedCategory
  let : F.CommShift ℤ := inferInstance
  have : F.IsTriangulated := inferInstance
  have := intrinsic_iso Y (pbcIntegralDatum l E)
  have := intrinsic_tri Y (pbcIntegralDatum l E)
  have := sf_complete_iso l E Y
  have heq : (IsSfDerivedComplete l E Y : ObjectProperty _) = P.inverseImage F := by
    ext K
    have h := (purCoefficientModel_predicates l E Y (F.obj K)).2
    have hi := ObjectProperty.prop_iff_of_iso (IsSfDerivedComplete l E Y)
      (e.counitIso.app K)
    exact hi.symm.trans h.symm
  rw [heq]
  infer_instance

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private noncomputable def reductionProperty (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
    intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj K) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj K) ⊆ Set.Icc a b

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem reductionProperty_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    (reductionProperty l E Y).IsClosedUnderIsomorphisms := by
  constructor
  intro K L e hK
  obtain ⟨a, b, hab, hred⟩ := hK
  refine ⟨a, b, hab, fun n ↦ ?_⟩
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let en := (scalarReductionDerivedExtension.{u, u} l E Y n).mapIso e
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y) :=
    (proEtale_bounded_constructible_isTriangulated Y A).1
  refine ⟨ObjectProperty.prop_of_iso _ en (hred n).1, ?_⟩
  intro i hi
  apply (hred n).2
  intro hz
  exact hi (((DerivedCategory.homologyFunctor _ i).mapIso en).isZero_iff.mp hz)

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem reductionProperty_zero (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    (reductionProperty l E Y).ContainsZero := by
  let : Zero (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    HasZeroObject.zero' _
  refine ⟨0, isZero_zero _, 0, 0, le_refl _, fun n ↦ ?_⟩
  let F := scalarReductionDerivedExtension.{u, u} l E Y n
  obtain ⟨hshift, htri⟩ :=
    (scalarReductionDerivedExistence.{u, u} l E Y n).choose_spec.choose_spec.2.1
  let : F.CommShift ℤ := hshift
  have : F.IsTriangulated := htri
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let P := intrinsicFiniteTorsionConstructible l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) Y
  have : P.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated Y A).1
  have : P.IsTriangulated :=
    (proEtale_bounded_constructible_isTriangulated Y A).2
  have hz := F.map_isZero (isZero_zero _)
  refine ⟨P.prop_of_isZero hz, fun i hi ↦ ?_⟩
  exact (hi ((DerivedCategory.homologyFunctor _ i).map_isZero hz)).elim

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem reductionProperty_shift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    (reductionProperty l E Y).IsStableUnderShift ℤ := by
  constructor
  intro m
  constructor
  intro K hK
  obtain ⟨a, b, hab, hred⟩ := hK
  refine ⟨a - m, b - m, sub_le_sub_right hab m, fun n ↦ ?_⟩
  let F := scalarReductionDerivedExtension.{u, u} l E Y n
  obtain ⟨hshift, htri⟩ :=
    (scalarReductionDerivedExistence.{u, u} l E Y n).choose_spec.choose_spec.2.1
  let : F.CommShift ℤ := hshift
  have : F.IsTriangulated := htri
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let P := intrinsicFiniteTorsionConstructible l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) Y
  have : P.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated Y A).1
  have : P.IsTriangulated :=
    (proEtale_bounded_constructible_isTriangulated Y A).2
  refine ⟨P.prop_of_iso ((F.commShiftIso m).symm.app K)
    (P.le_shift m _ (hred n).1), ?_⟩
  intro i hi
  have hi' : i + m ∈ proEtaleCohomologicalSupport (F.obj K) := by
    intro hz
    apply hi
    let e₁ := (DerivedCategory.homologyFunctor _ i).mapIso ((F.commShiftIso m).app K)
    let e₂ := ((DerivedCategory.homologyFunctor _ 0).shiftIso m i (i + m)
      (add_comm m i)).app (F.obj K)
    exact (e₁ ≪≫ e₂).isZero_iff.mpr hz
  obtain ⟨ha, hb⟩ := (hred n).2 hi'
  exact ⟨(sub_le_iff_le_add).mpr ha,
    (le_sub_iff_add_le).mpr hb⟩

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem reductionProperty_middle (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    (reductionProperty l E Y).IsTriangulatedClosed₂ := by
  have := reductionProperty_iso l E Y
  apply ObjectProperty.IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₃
  obtain ⟨a₁, b₁, hab₁, hred₁⟩ := h₁
  obtain ⟨a₃, b₃, hab₃, hred₃⟩ := h₃
  refine ⟨min a₁ a₃, max b₁ b₃, (min_le_left _ _).trans (hab₁.trans
    (le_max_left _ _)), fun n ↦ ?_⟩
  let F := scalarReductionDerivedExtension.{u, u} l E Y n
  obtain ⟨hshift, htri⟩ :=
    (scalarReductionDerivedExistence.{u, u} l E Y n).choose_spec.choose_spec.2.1
  let : F.CommShift ℤ := hshift
  have : F.IsTriangulated := htri
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let P := intrinsicFiniteTorsionConstructible l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) Y
  have : P.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated Y A).1
  have : P.IsTriangulated :=
    (proEtale_bounded_constructible_isTriangulated Y A).2
  have hFT := F.map_distinguished T hT
  refine ⟨P.ext_of_isTriangulatedClosed₂ (F.mapTriangle.obj T) hFT
    (hred₁ n).1 (hred₃ n).1, ?_⟩
  intro i hi
  by_contra hout
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor _ i).obj (F.obj T.obj₁)) := by
    by_contra hn
    have hb := (hred₁ n).2 hn
    exact hout ⟨(min_le_left _ _).trans hb.1, hb.2.trans (le_max_left _ _)⟩
  have hz₃ : IsZero ((DerivedCategory.homologyFunctor _ i).obj (F.obj T.obj₃)) := by
    by_contra hn
    have hb := (hred₃ n).2 hn
    exact hout ⟨(min_le_right _ _).trans hb.1, hb.2.trans (le_max_right _ _)⟩
  exact hi ((DerivedCategory.HomologySequence.exact₂ (F.mapTriangle.obj T) hFT i).isZero_X₂
    (hz₁.eq_of_src _ _) (hz₃.eq_of_tgt _ _))

open CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry.Scheme in
private theorem triangulated_of_complete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u})
    (hc : ObjectProperty.IsTriangulated (IsSfDerivedComplete l E Y)) :
    ObjectProperty.IsTriangulated (sfIntegralConstructible l E Y) := by
  have := hc
  have := reductionProperty_iso l E Y
  have := reductionProperty_zero l E Y
  have := reductionProperty_shift l E Y
  have := reductionProperty_middle l E Y
  have : (reductionProperty l E Y).IsTriangulated := {}
  change ObjectProperty.IsTriangulated
    ((IsSfDerivedComplete l E Y) ⊓ reductionProperty l E Y)
  infer_instance

/-- The intrinsic integral constructible predicate is closed under isomorphisms.
Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1; blueprint order 1459
(blueprint: lem-weil-integral-constructible-triangulated).

Proof: an isomorphism induces isomorphisms of all reductions and intertwines their
canonical units and transitions. Transport a product witness and its distinguished
Roos triangle to obtain derived completeness of the isomorphic object. At every
positive level, cohomology sheaves are isomorphic, preserving finite-torsion
constructibility and the same uniform cohomological interval. These are precisely
the defining clauses of `sfIntegralConstructible` (proof steps 2 and 5 of the node).
-/
@[instance]
theorem sfIntegralConstructible_isClosedUnderIsomorphisms
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (sfIntegralConstructible l E Y) := by
  constructor
  intro K L e hK
  obtain ⟨hcomplete, a, b, hab, hred⟩ := hK
  refine ⟨augmentedRoos_iso (sfDerivedReductionRestricted l E Y)
    (sfDerivedReductionUnit l E Y) (sfDerivedReductionTransition l E Y) e hcomplete,
    a, b, hab, fun n ↦ ?_⟩
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let en := (scalarReductionDerivedExtension.{u, u} l E Y n).mapIso e
  have hi : ObjectProperty.IsClosedUnderIsomorphisms
      (AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y) :=
    (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated Y A).1
  refine ⟨ObjectProperty.prop_of_iso _ en (hred n).1, ?_⟩
  intro i hi
  apply (hred n).2
  intro hz
  exact hi (((DerivedCategory.homologyFunctor _ i).mapIso en).isZero_iff.mp hz)

/-- Derived-complete integral objects whose constructible reductions have a common
finite cohomological interval form a triangulated object property. Together with
isomorphism closure above, this states zero, integer-shift and extension closure
for the actual predicate. Mathlib's full-subcategory construction supplies the
inherited distinguished triangles and makes the inclusion exact.
Source: Bhatt--Scholze, Section 6.5, after Definition 6.5.1, for the variant of
blueprint order 1459; Stacks Project, Tag 0999
(blueprint: lem-weil-integral-constructible-triangulated).

Proof:
1. The recorded completed-coefficient presentation equivalence identifies intrinsic
completeness with the actual canonical augmented-Roos predicate. It has no geometric
finiteness hypothesis. Isomorphism closure transports the product, unit components,
transition endomorphism and connecting map directly.
2. The intrinsic complete subcategory has its recorded completion reflection and the
shift comparison commuting with its unit. A generic argument identifies this predicate P
with P.leftOrthogonal.rightOrthogonal: complete objects belong to that orthogonal;
the cone of each reflection unit belongs to P.leftOrthogonal by the reflection Hom
bijections, the shifted bijection and exactness of Hom on a triangle. If the source lies
in the double orthogonal then so does this cone. Its identity vanishes, so the cone is
zero and the unit is invertible. Mathlib's orthogonal instances give triangulation.
3. Exact restriction along the completed coefficient isomorphism is triangulated.
The counit of the presentation equivalence and the recorded completeness comparison
identify IsSfDerivedComplete with the inverse image of the intrinsic predicate.
Mathlib's inverse-image instance transfers the triangulation from step 2.
4. At each positive exponent the reduction functor
(`def-weil-integral-derived-reduction`, `scalarReductionDerivedExtension`)
is exact triangulated by
`lem-pur-derived-change-of-rings` applied to the identity site and B to B_n.
It preserves zero, isomorphisms, shifts and distinguished triangles. Flatness of
B_n over B is not required for a derived functor.
5. The zero object's reductions have empty support, in [0,0]. Isomorphisms
preserve cohomology and constructibility. For a shift by m,
`lem-sp-derived-cohomology-shift` translates a uniform interval [r,s] to
[r-m,s-m]. `lem-weil-proetale-dbc-triangulated` supplies finite-level zero,
isomorphism and shift closure. Its constructibility agrees with
`definition-constructible-sheaves` and
`def-weil-proetale-constructible-sheaf`: finite locally closed constructible
partitions, locally constant restrictions with finite stalks, and bounded
cohomology. Combine this with step 3 and
`def-weil-derived-complete-integral-detailed` for the integral closure assertions.
6. Reduce a distinguished triangle with integral constructible outside vertices.
Each coefficient quotient is finite. Thus
`lem-weil-proetale-dbc-triangulated` gives bounded constructibility of the middle
reduction at every level, and step 3 gives completeness of the middle object.
7. If the outside uniform intervals are [r',s'] and [r'',s''], use
[min(r',r''),max(s',s'')]. Outside this interval the exact cohomology segment has
zero outside terms, hence zero middle term, by
`lem-sf-derived-homology-long-exact`. This proves the common support bound of
`def-weil-cohomological-support`, independently of the reduction level. No common
stratification or rank bound across levels is required.
8. The category is full by definition. The preceding closure properties make its
object property triangulated and isomorphism-closed. Cone closure follows by
rotation and shifts. `def-weil-triangulated-subcategory` supplies the inherited
triangulated structure and exact inclusion. -/
@[instance]
theorem sfIntegralConstructible_isTriangulated
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsTriangulated (sfIntegralConstructible l E Y) := by
  exact triangulated_of_complete l E Y (sf_complete_tri l E Y)

end WeilConjectures
