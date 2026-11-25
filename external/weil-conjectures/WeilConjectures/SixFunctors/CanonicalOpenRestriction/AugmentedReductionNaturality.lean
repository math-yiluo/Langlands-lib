/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions

/-! # Naturality of augmented reduction presentations

Source: Stacks Project, Tags 03CZ, 06YY and 0941. The strict scalar-unit
augmentations determine the comparison of an ordinary map in the whole derived
system category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
attribute [local irreducible] HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem eqIsoSection {I : Type*} [Category I]
    {F G : I ⥤ scalarReductionSource l E W} (h : F = G) (P : I)
    (V : W.ProEtᵒᵖ) (x : (F.obj P).val.obj V) :
    HEq (((eqToIso h).hom.app P).val.app V x) x := by
  cases h
  rfl

private theorem scalar_comp_apply (n : ℕ)
    {M : scalarReductionSource l E W} {N P : normalizedDVRModules l E W n}
    (f : M ⟶ (scalarReductionRestriction l E W n).obj N) (g : N ⟶ P)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((f ≫ (scalarReductionRestriction l E W n).map g).val.app V) x =
      g.val.app V (f.val.app V x) := rfl

private theorem sheaf_comp_apply
    {A : Sheaf (Scheme.ProEt.topology W) RingCat.{max u (t + 1)}}
    {M N P : SheafOfModules.{max u (t + 1)} A} (f : M ⟶ N) (g : N ⟶ P)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((f ≫ g).val.app V) x = g.val.app V (f.val.app V x) := rfl

private theorem augmentation_component
    (M : scalarReductionSource l E W) (N : coefficientSequenceModules l E W) (n : ℕ)
    (κ : (coefficientSequenceEvaluation l E W n).obj N ≅
      (scalarReductionExtension l E W n).obj M)
    (a : M ⟶ ((coefficientSequenceRestriction l E W).obj N).obj (op n))
    (ha : ∀ (V : W.ProEtᵒᵖ) (x : M.val.obj V),
      HEq (a.val.app V x)
        (κ.inv.val.app V (coefficientIntegralScalarUnitSection l E W n M V x))) :
    a ≫ (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app M ≫
        (scalarReductionRestriction l E W n).map κ.inv := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  have hh := (eqIsoSection l E W (coefficientSequenceRestriction_evaluation l E W n)
    N V (a.val.app V x)).trans (ha V x)
  have hs := scalar_comp_apply l E W n
    ((scalarReductionExtension_adjunction l E W n).choose.unit.app M) κ.inv V x
  have ht := sheaf_comp_apply.{t, u} W a
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N) V x
  dsimp only [coefficientIntegralScalarUnitSection] at hh
  apply eq_of_heq
  refine (heq_of_eq ht).trans ?_
  refine hh.trans ?_
  exact heq_of_eq hs.symm

private theorem unitPresentation_natural
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {M R : A} {C D : B} (κC : C ≅ F.obj M) (κD : D ≅ F.obj R)
    (a : M ⟶ G.obj C) (b : R ⟶ G.obj D) (h : M ⟶ R) (f : C ⟶ D)
    (ha : a = adj.unit.app M ≫ G.map κC.inv)
    (hb : b = adj.unit.app R ≫ G.map κD.inv)
    (hf : f ≫ κD.hom = κC.hom ≫ F.map h) : h ≫ b = a ≫ G.map f := by
  have hk : κC.inv ≫ f = F.map h ≫ κD.inv := by
    apply (cancel_mono κD.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hf, Iso.inv_hom_id_assoc]
  rw [ha, hb, Category.assoc, ← G.map_comp, hk, G.map_comp]
  have hu := adj.unit.naturality h
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ G.map κD.inv) hu

/-- An ordinary map between augmented quotient presentations computes reduction
of the integral map when its finite tensor components do.
Source: Stacks Project, Tags 03CZ, 06YY and 0941; the augmentation calculation
in step 1 of `lem-sf-open-restriction-counit-on-good-complexes`.
(blueprint: lem-sf-augmented-reduction-naturality).

Proof: transport the strict augmentations through the finite presentation
isomorphisms. Their components are the scalar-adjunction units. Naturality of
those units and the assumed finite squares show that the augmentations commute
with the two chain maps. This is an equality of ordinary tower maps, checked
sectionwise in every degree and at every level. Localize the equality and use
naturality of the exact-functor factorization isomorphisms. Transpose along the
constant-tower/total-limit adjunction and then along the reduction/limit
adjunction. The two augmentation normalization equations give the stated equality
in the entire system derived category. -/
theorem augmentedReductionNaturality
    (S : CoefficientDerivedSystemCalculus l E W)
    (Q R : CochainComplex (scalarReductionSource l E W) ℤ)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (eC : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj R) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj R)
    (hC : AugmentedPresentation l E W S Q C eC κC)
    (hD : AugmentedPresentation l E W S R D eD κD)
    (h : Q ⟶ R) (f : C ⟶ D)
    (hf : ∀ (n : ℕ) (i : ℤ),
      (coefficientSequenceEvaluation l E W n).map (f.f i) ≫ (κD n).hom.f i =
        (κC n).hom.f i ≫ (scalarReductionExtension l E W n).map (h.f i)) :
    S.reduction.map (DerivedCategory.Q.map h) ≫ eD.hom =
      eC.hom ≫ DerivedCategory.Q.map f := by
  obtain ⟨a, ha, hea⟩ := hC
  obtain ⟨b, hb, heb⟩ := hD
  let δ : scalarReductionSource l E W ⥤ ℕᵒᵖ ⥤ scalarReductionSource l E W :=
    Functor.const ℕᵒᵖ
  let T := coefficientSequenceRestriction l E W
  have hab : (δ.mapHomologicalComplex (.up ℤ)).map h ≫ b =
      a ≫ (T.mapHomologicalComplex (.up ℤ)).map f := by
    apply HomologicalComplex.hom_ext
    intro i
    apply NatTrans.ext
    funext n
    apply (cancel_mono
      ((eqToIso (coefficientSequenceRestriction_evaluation l E W n.unop)).hom.app
        (D.X i))).1
    have hn := (eqToIso (coefficientSequenceRestriction_evaluation l E W n.unop)).hom.naturality
      (f.f i)
    change (T.map (f.f i)).app n ≫ _ = _ at hn
    change h.f i ≫ (b.f i).app n ≫ _ = (a.f i).app n ≫ (T.map (f.f i)).app n ≫ _
    have hbc := augmentation_component l E W (R.X i) (D.X i) n.unop
      ((HomologicalComplex.eval _ _ i).mapIso (κD n.unop))
      ((b.f i).app n) (hb i n.unop)
    have hac := augmentation_component l E W (Q.X i) (C.X i) n.unop
      ((HomologicalComplex.eval _ _ i).mapIso (κC n.unop))
      ((a.f i).app n) (ha i n.unop)
    have hn' := unitPresentation_natural
      (scalarReductionExtension_adjunction l E W n.unop).choose
      ((HomologicalComplex.eval _ _ i).mapIso (κC n.unop))
      ((HomologicalComplex.eval _ _ i).mapIso (κD n.unop))
      _ _ (h.f i) ((coefficientSequenceEvaluation l E W n.unop).map (f.f i))
      hac hbc (hf n.unop i)
    calc
      _ = (a.f i).app n ≫
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n.unop)).hom.app
            (C.X i) ≫
          (scalarReductionRestriction l E W n.unop).map
            ((coefficientSequenceEvaluation l E W n.unop).map (f.f i)) := by
        simpa only [Category.assoc] using hn'
      _ = _ := congrArg (fun g ↦ (a.f i).app n ≫ g) hn.symm
  apply (S.adjunction.homEquiv _ _).injective
  rw [S.adjunction.homEquiv_naturality_left,
    S.adjunction.homEquiv_naturality_right, hea, heb]
  have hδ := δ.mapDerivedCategoryFactors.hom.naturality h
  have hT := T.mapDerivedCategoryFactors.inv.naturality f
  change DerivedCategory.Q.map h ≫
      (integralComparisonConstantAdjunction l E W).homEquiv _ _
        (δ.mapDerivedCategoryFactors.hom.app R ≫ DerivedCategory.Q.map b ≫
          T.mapDerivedCategoryFactors.inv.app D) =
    (integralComparisonConstantAdjunction l E W).homEquiv _ _
        (δ.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map a ≫
          T.mapDerivedCategoryFactors.inv.app C) ≫
      (coefficientConstantTowerLimit l E W).map
        (T.mapDerivedCategory.map (DerivedCategory.Q.map f))
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  apply congrArg ((integralComparisonConstantAdjunction l E W).homEquiv _ _)
  dsimp only [Functor.comp_map] at hδ hT
  simp only [Category.assoc]
  dsimp only [integralComparisonConstantTower]
  change δ.mapDerivedCategory.map (DerivedCategory.Q.map h) ≫
      δ.mapDerivedCategoryFactors.hom.app R ≫ DerivedCategory.Q.map b ≫
        T.mapDerivedCategoryFactors.inv.app D = _
  rw [reassoc_of% hδ, ← hT]
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc, hab]

end WeilConjectures.CanonicalOpenRestriction
