/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Descent of a normalized completion comparison

Source: Stacks Tags 06YY and 0941: localization and the two coordinates of the Roos cone.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {S T : Scheme.{t}} (r : S ⟶ T)

private theorem descendConjugatedIso
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W]
    {F G : B ⥤ C} {H : A ⥤ C} (a : q ⋙ F ≅ H) (b : q ⋙ G ≅ H) :
    ∃ e : F ≅ G, ∀ P, e.hom.app (q.obj P) ≫ b.hom.app P = a.hom.app P := by
  let ff := Localization.fullyFaithfulWhiskeringLeft q W C
  let e : F ≅ G := ff.preimageIso (a ≪≫ b.symm)
  refine ⟨e, ?_⟩
  intro P
  have hh := congr_app (ff.map_preimage (a ≪≫ b.symm).hom) P
  change e.hom.app (q.obj P) = (a ≪≫ b.symm).hom.app P at hh
  rw [hh]
  simp

private theorem descendCompletionComparison
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    (P₀ : ObjectProperty C₀) (P₁ : ObjectProperty C₁)
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (FC₀ : C₀ ⥤ C₁) (FD : D₀ ⥤ D₁)
    (R₀ : C₀ ⥤ C₀) (R₁ : C₁ ⥤ C₁) (CT₀ : D₀ ⥤ D₀) (CS₀ : D₁ ⥤ D₁)
    (W : MorphismProperty P₀.FullSubcategory) [(P₀.ι ⋙ Q₀).IsLocalization W]
    (a₀ : (P₀.ι ⋙ Q₀) ⋙ CT₀ ≅ P₀.ι ⋙ (R₀ ⋙ Q₀))
    (a₁ : (P₁.ι ⋙ Q₁) ⋙ CS₀ ≅ P₁.ι ⋙ (R₁ ⋙ Q₁))
    (ε₀ : Q₀ ⋙ FD ≅ FC₀ ⋙ Q₁) (χ : R₀ ⋙ FC₀ ≅ FC₀ ⋙ R₁)
    (hgood : ∀ X : P₀.FullSubcategory, P₁ (FC₀.obj X.obj)) :
    ∃ α : CT₀ ⋙ FD ≅ FD ⋙ CS₀, ∀ X : P₀.FullSubcategory,
      FD.map (a₀.hom.app X) ≫ ε₀.hom.app (R₀.obj X.obj) ≫
          Q₁.map (χ.hom.app X.obj) =
        α.hom.app ((P₀.ι ⋙ Q₀).obj X) ≫ CS₀.map (ε₀.hom.app X.obj) ≫
          a₁.hom.app ⟨FC₀.obj X.obj, hgood X⟩ := by
  let F := FD
  let FC := FC₀
  let CT := CT₀
  let CS := CS₀
  let J := P₀.ι
  let G := P₁.lift (J ⋙ FC) hgood
  let ε := ε₀
  let A : (P₀.ι ⋙ Q₀) ⋙ (CT ⋙ F) ≅
      J ⋙ (FC ⋙ (R₁ ⋙ Q₁)) :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (a₀) F ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (J ⋙ R₀) ε ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator J (R₀) FC ≪≫
        Functor.isoWhiskerLeft J χ ≪≫ (Functor.associator _ _ _).symm)
      Q₁ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.associator _ _ _
  let B₀ : (P₀.ι ⋙ Q₀) ⋙ (F ⋙ CS) ≅
      G ⋙ (P₁.ι ⋙ (R₁ ⋙ Q₁)) :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J ε) CS ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (a₁)
  let B : (P₀.ι ⋙ Q₀) ⋙ (F ⋙ CS) ≅
      J ⋙ (FC ⋙ (R₁ ⋙ Q₁)) :=
    B₀ ≪≫ (Functor.associator G P₁.ι
      (R₁ ⋙ Q₁)).symm ≪≫
    Functor.isoWhiskerRight (P₁.liftCompιIso (J ⋙ FC) hgood)
      (R₁ ⋙ Q₁) ≪≫
    Functor.associator J FC (R₁ ⋙ Q₁)
  obtain ⟨α, hα⟩ := descendConjugatedIso ((P₀.ι ⋙ Q₀)) W A B
  refine ⟨α, ?_⟩
  intro P
  have he := hα P
  simp only [A, B, B₀, ε, G, J, F, FC, CT, CS, Functor.comp_obj,
    ObjectProperty.ι_obj, ObjectProperty.lift, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc] at he
  dsimp only [ObjectProperty.lift, ObjectProperty.ι, Functor.comp_obj] at he
  erw [(R₁ ⋙ Q₁).map_id] at he
  erw [Category.comp_id] at he
  exact he.symm

private def ordinaryCounitNat :
    DerivedCategory.Q ⋙ ordinaryDerivedPull l E r ⟶
      ordinaryComplexPull l E r ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
      (ordinaryDerivedPull l E r)).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _)
      (((ordinaryPull l E r).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Mod l E T none) (.up ℤ))) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight ((ordinaryPull l E r).mapHomotopyCategoryFactors
      (.up ℤ)) DerivedCategory.Qh).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ordinaryComplexPull l E r)
      (DerivedCategory.quotientCompQhIso _).hom

private lemma ordinaryCounitNat_app (P : Cx l E T none) :
    (ordinaryCounitNat l E r).app P = ordinaryComplexCounit l E r P := by
  simp only [ordinaryCounitNat, ordinaryComplexCounit, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Category.id_comp]

@[reassoc]
private lemma ordinaryComplexCounit_naturality {P Q : Cx l E T none} (f : P ⟶ Q) :
    (ordinaryDerivedPull l E r).map (DerivedCategory.Q.map f) ≫
        ordinaryComplexCounit l E r Q =
      ordinaryComplexCounit l E r P ≫
        DerivedCategory.Q.map ((ordinaryComplexPull l E r).map f) := by
  simpa only [ordinaryCounitNat_app, Functor.comp_map] using
    (ordinaryCounitNat l E r).naturality f

attribute [local irreducible] ordinaryPull

private lemma ordinaryComplexCounit_isIso
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)] (P : Cx l E T none) :
    IsIso (ordinaryComplexCounit l E r P) := by
  let F := (ordinaryPull l E r).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso (Mod l E T none) (.up ℤ)
  have hF : W.IsInvertedBy F := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W
      (ordinaryPull l E r).mapDerivedCategoryFactorsh]
    intro X Y f hf
    let := Localization.inverts DerivedCategory.Qh W f hf
    exact inferInstanceAs (IsIso ((ordinaryPull l E r).mapDerivedCategory.map
      (DerivedCategory.Qh.map f)))
  have hε := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (F.totalLeftDerived DerivedCategory.Qh W)
    (F.totalLeftDerivedCounit DerivedCategory.Qh W) hF
  dsimp only [ordinaryComplexCounit]
  infer_instance

private lemma completionUnit_normalization
    (X : Scheme.{t}) (P : (Good l E X none).FullSubcategory) :
    (completionUnit l E X none).app ((qGood l E X none).obj P) ≫
        (completionComparison l E X none).hom.app P =
      DerivedCategory.Q.map (roosUnit l E X none P.obj) := by
  simpa only [completionUnit] using
    (completionUnit_existsUnique l E X none).exists.choose_spec P

attribute [local irreducible] ordinaryDerivedPull completion completionComparison
  ordinaryComplexCounit tower augmentation completionUnit
  ordinaryCounitNat ordinaryComplexPull roos

private def ordinaryCounitIso
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)] :
    DerivedCategory.Q ⋙ ordinaryDerivedPull l E r ≅
      ordinaryComplexPull l E r ⋙ DerivedCategory.Q := by
  let (P : Cx l E T none) : IsIso ((ordinaryCounitNat l E r).app P) := by
    rw [ordinaryCounitNat_app]
    exact ordinaryComplexCounit_isIso l E r P
  exact NatIso.ofComponents (fun P ↦ asIso ((ordinaryCounitNat l E r).app P))
    (fun f ↦ (ordinaryCounitNat l E r).naturality f)

private lemma ordinaryCounitIso_hom_app
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)] (P : Cx l E T none) :
    (ordinaryCounitIso l E r).hom.app P = ordinaryComplexCounit l E r P := by
  exact ordinaryCounitNat_app l E r P

attribute [local irreducible] ordinaryCounitIso

/-- Exact ordinary restriction descends a chain Roos comparison uniquely to completion.
Source: Stacks 06YY and 0941
(blueprint: lem-fix-qcqs-completion-comparison-unit).
Proof: the ordinary derived counit is an isomorphism on every complex. On good
representatives conjugate the chain comparison by this counit and the two
completion comparisons. Fully faithful restriction along the good localization
descends this natural isomorphism. Its component equation is the stated normalization. -/
theorem ordinaryCompletionComparison_exists
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)]
    (χ : roos l E T none ⋙ ordinaryComplexPull l E r ≅
      ordinaryComplexPull l E r ⋙ roos l E S none)
    (hgood : ∀ P : (Good l E T none).FullSubcategory,
      Good l E S none ((ordinaryComplexPull l E r).obj P.obj)) :
    ∃ α : completion l E T none ⋙ ordinaryDerivedPull l E r ≅
        ordinaryDerivedPull l E r ⋙ completion l E S none,
      ∀ P : (Good l E T none).FullSubcategory,
        (ordinaryDerivedPull l E r).map ((completionComparison l E T none).hom.app P) ≫
            ordinaryComplexCounit l E r ((roos l E T none).obj P.obj) ≫
            DerivedCategory.Q.map (χ.hom.app P.obj) =
          α.hom.app ((qGood l E T none).obj P) ≫
            (completion l E S none).map (ordinaryComplexCounit l E r P.obj) ≫
            (completionComparison l E S none).hom.app
              ⟨(ordinaryComplexPull l E r).obj P.obj, hgood P⟩ := by
  let := goodLocalization l E T none
  let W := (HomologicalComplex.quasiIso (Mod l E T none) (.up ℤ)).inverseImage
    (Good l E T none).ι
  let : ((Good l E T none).ι ⋙ DerivedCategory.Q).IsLocalization W :=
    goodLocalization l E T none
  obtain ⟨α, hα⟩ := descendCompletionComparison (Good l E T none) (Good l E S none)
    DerivedCategory.Q DerivedCategory.Q (ordinaryComplexPull l E r)
    (ordinaryDerivedPull l E r) (roos l E T none) (roos l E S none)
    (completion l E T none) (completion l E S none) W
    (completionComparison l E T none) (completionComparison l E S none)
    (ordinaryCounitIso l E r) χ hgood
  refine ⟨α, ?_⟩
  intro P
  simpa only [qGood, ordinaryCounitIso_hom_app] using hα P

attribute [local semireducible] ordinaryComplexPull roos

private lemma cocone_hom_ext {A : Type*} [Category* A] [Abelian A]
    {P Q M : CochainComplex A ℤ} (φ : P ⟶ Q)
    (a b : M ⟶ CochainComplex.mappingCocone φ)
    (hf : a ≫ CochainComplex.mappingCocone.fst φ =
      b ≫ CochainComplex.mappingCocone.fst φ)
    (hs : ∀ i : ℤ, a.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i + -1) rfl =
      b.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i + -1) rfl) : a = b := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun z ↦ z.f i) hf
  change a.f i ≫ _ = b.f i ≫ _ at h
  have hid := CochainComplex.mappingCocone.id_X φ i (i + -1) rfl
  have haid := congrArg (fun z ↦ a.f i ≫ z) hid
  have hbid := congrArg (fun z ↦ b.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at haid hbid
  rw [h, hs i] at haid
  exact haid.symm.trans hbid

private lemma ordinaryRoosUnit_fst (P : Cx l E T none) :
    roosUnit l E T none P ≫
        CochainComplex.mappingCocone.fst (ordinaryRoosEndomorphism l E P) =
      productAugmentation l E T none P := by
  dsimp only [roosUnit, ordinaryRoosEndomorphism]
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

private lemma ordinaryRoosUnit_snd (P : Cx l E T none) (i : ℤ) :
    (roosUnit l E T none P).f i ≫
      (CochainComplex.mappingCocone.snd (ordinaryRoosEndomorphism l E P)).v
        i (i + -1) rfl = 0 := by
  dsimp only [roosUnit, ordinaryRoosEndomorphism]
  simp only [CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v]

variable
    (τ : tower l E T none ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Cx l E T none) (Cx l E S none)).obj
        (ordinaryComplexPull l E r) ≅
      ordinaryComplexPull l E r ⋙ tower l E S none)
    (χ : roos l E T none ⋙ ordinaryComplexPull l E r ≅
      ordinaryComplexPull l E r ⋙ roos l E S none)
    (haug : ∀ (P : Cx l E T none) (n : ℕ),
      (ordinaryComplexPull l E r).map (((augmentation l E T none).app P).app (op n)) ≫
          (τ.hom.app P).app (op n) =
        ((augmentation l E S none).app ((ordinaryComplexPull l E r).obj P)).app (op n))
    (hfst : ∀ P : Cx l E T none,
      χ.hom.app P ≫ CochainComplex.mappingCocone.fst
          (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P)) =
        (ordinaryComplexPull l E r).map
            (CochainComplex.mappingCocone.fst (ordinaryRoosEndomorphism l E P)) ≫
          piComparison (ordinaryComplexPull l E r)
            (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n)) ≫
          Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n)))
    (hsnd : ∀ (P : Cx l E T none) (i : ℤ),
      (χ.hom.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P))).v
              i (i + -1) rfl =
        (ordinaryPull l E r).map
            ((CochainComplex.mappingCocone.snd (ordinaryRoosEndomorphism l E P)).v
              i (i + -1) rfl) ≫
          (piComparison (ordinaryComplexPull l E r)
            (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n))).f (i + -1) ≫
          (Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))).f (i + -1))

include τ haug hfst hsnd in
private lemma ordinaryRoosUnit_comparison (P : Cx l E T none) :
    (ordinaryComplexPull l E r).map (roosUnit l E T none P) ≫ χ.hom.app P =
      roosUnit l E S none ((ordinaryComplexPull l E r).obj P) := by
  apply cocone_hom_ext
    (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P))
  · rw [Category.assoc, hfst]
    simp only [← Category.assoc, ← Functor.map_comp, ordinaryRoosUnit_fst]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, productAugmentation, Pi.lift_comp_π]
    erw [Pi.map_π, piComparison_comp_π_assoc, ← Functor.map_comp_assoc, Pi.lift_comp_π]
    exact haug P n
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc, hsnd]
    change (ordinaryPull l E r).map ((roosUnit l E T none P).f i) ≫ _ = _
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ordinaryRoosUnit_snd, Functor.map_zero, zero_comp, zero_comp,
      ordinaryRoosUnit_snd]

include τ haug hfst hsnd in
/-- A comparison normalized on good representatives and both Roos coordinates
preserves the specified completion unit.

Source: Stacks Tags 06YY and 0941
(blueprint: lem-fix-qcqs-completion-comparison-unit).
Proof: the two chain coordinates identify the image of the (quotient, zero) lift
with that same lift on the pulled representative. Compose the representative
comparison equation with the source unit. Naturality of the derived counit moves
that unit to the chain level. The normalization of both completion units then gives
the desired square after the target counit and completion comparison. Exactness
makes those maps invertible. Finally good representatives localize to the entire
derived category, so equality of natural transformations on them proves equality
everywhere. -/
theorem ordinaryCompletionComparison_unit
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)]
    (hgood : ∀ P : (Good l E T none).FullSubcategory,
      Good l E S none ((ordinaryComplexPull l E r).obj P.obj))
    (α : completion l E T none ⋙ ordinaryDerivedPull l E r ≅
      ordinaryDerivedPull l E r ⋙ completion l E S none)
    (hα : ∀ P : (Good l E T none).FullSubcategory,
      (ordinaryDerivedPull l E r).map ((completionComparison l E T none).hom.app P) ≫
          ordinaryComplexCounit l E r ((roos l E T none).obj P.obj) ≫
          DerivedCategory.Q.map (χ.hom.app P.obj) =
        α.hom.app ((qGood l E T none).obj P) ≫
          (completion l E S none).map (ordinaryComplexCounit l E r P.obj) ≫
          (completionComparison l E S none).hom.app
            ⟨(ordinaryComplexPull l E r).obj P.obj, hgood P⟩)
    (H : D l E T none) :
    (ordinaryDerivedPull l E r).map ((completionUnit l E T none).app H) ≫
        α.hom.app H =
      (completionUnit l E S none).app ((ordinaryDerivedPull l E r).obj H) := by
  let F := ordinaryDerivedPull l E r
  let η := completionUnit l E T none
  let ε := completionUnit l E S none
  let a : F ⟶ F ⋙ completion l E S none :=
    (Functor.leftUnitor F).inv ≫ Functor.whiskerRight η F ≫ α.hom
  let b : F ⟶ F ⋙ completion l E S none :=
    (Functor.rightUnitor F).inv ≫ Functor.whiskerLeft F ε
  have hab : a = b := by
    let := goodLocalization l E T none
    apply Localization.natTrans_ext (qGood l E T none)
      ((HomologicalComplex.quasiIso (Mod l E T none) (.up ℤ)).inverseImage
        (Good l E T none).ι)
    intro P
    simp only [a, b, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp]
    change F.map (η.app _) ≫ α.hom.app _ = ε.app _
    let P' : (Good l E S none).FullSubcategory :=
      ⟨(ordinaryComplexPull l E r).obj P.obj, hgood P⟩
    have := ordinaryComplexCounit_isIso l E r P.obj
    apply (cancel_mono ((completion l E S none).map
      (ordinaryComplexCounit l E r P.obj) ≫
        (completionComparison l E S none).hom.app P')).mp
    simp only [Category.assoc]
    erw [← hα]
    have hn : η.app ((qGood l E T none).obj P) ≫
        (completionComparison l E T none).hom.app P =
      DerivedCategory.Q.map (roosUnit l E T none P.obj) :=
      completionUnit_normalization l E T P
    have hm : ε.app ((qGood l E S none).obj P') ≫
        (completionComparison l E S none).hom.app P' =
      DerivedCategory.Q.map (roosUnit l E S none P'.obj) :=
      completionUnit_normalization l E S P'
    calc
      _ = F.map (DerivedCategory.Q.map (roosUnit l E T none P.obj)) ≫
          ordinaryComplexCounit l E r ((roos l E T none).obj P.obj) ≫
          DerivedCategory.Q.map (χ.hom.app P.obj) := by
        change F.map (η.app _) ≫ F.map
          ((completionComparison l E T none).hom.app P) ≫ _ = _
        erw [← Functor.map_comp_assoc, hn]
      _ = ordinaryComplexCounit l E r P.obj ≫
          DerivedCategory.Q.map (roosUnit l E S none P'.obj) := by
        dsimp only [F]
        erw [ordinaryComplexCounit_naturality_assoc, ← Functor.map_comp,
          ordinaryRoosUnit_comparison l E r τ χ haug hfst hsnd]
      _ = _ := by
        erw [← hm]
        have hh := congrArg (fun f ↦ f ≫
          (completionComparison l E S none).hom.app P')
            (ε.naturality (ordinaryComplexCounit l E r P.obj))
        simp only [Functor.id_map, Category.assoc] at hh
        exact hh
  simpa only [a, b, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp] using congr_app hab H

end WeilConjectures.IntegralOnSlice
