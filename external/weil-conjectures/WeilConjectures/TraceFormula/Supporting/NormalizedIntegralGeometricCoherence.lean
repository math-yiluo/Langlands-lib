/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence

/-! # NormalizedIntegralGeometricCoherence

(blueprint: lem-trf-normalized-integral-geometric-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option synthInstance.maxSize 128
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSystemComposition integralComparisonSystemUnit
  integralComparisonDerivedSequencePullback integralDerivedPullback

private theorem mateSquare
    {C T : Type*} [Category C] [Category T]
    {R : C ⥤ T} {L : T ⥤ C} (adj : R ⊣ L)
    {A B : C} {U V W : T} (c : A ⟶ B) (b : B ⟶ L.obj U)
    (d : U ⟶ V) (a : A ⟶ L.obj W) (e : W ⟶ V)
    (h : c ≫ b ≫ L.map d = a ≫ L.map e) :
    R.map c ≫ (R.map b ≫ adj.counit.app U) ≫ d =
      (R.map a ≫ adj.counit.app W) ≫ e := by
  have h' := congrArg ((adj.homEquiv A V).symm) h
  simpa only [← Category.assoc, adj.homEquiv_naturality_right_symm,
    adj.homEquiv_naturality_left_symm, adj.homEquiv_counit] using h'

private theorem unitMapInjective
    {C T : Type*} [Category C] [Category T]
    {R : C ⥤ T} {L : T ⥤ C} (adj : R ⊣ L)
    {A B : C} [IsIso (adj.unit.app B)] (f g : A ⟶ B)
    (h : R.map f = R.map g) : f = g := by
  apply (cancel_mono (adj.unit.app B)).1
  rw [← adj.unit_naturality f, ← adj.unit_naturality g, h]

variable (l : ℕ) [Fact l.Prime] (D : IntegralComparisonSystem.{u} l)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def etaTransformation {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    integralDerivedPullback l E k ⋙ integralDerivedPullback l E h ⟶
      ((D.coefficient E).system V).reduction ⋙
        integralComparisonDerivedSequencePullback l E k ⋙
          integralComparisonDerivedSequencePullback l E h ⋙ coefficientSequenceLimit l E Z :=
  Functor.whiskerLeft (integralDerivedPullback l E k)
      ((D.coefficient E).pullback h).realization.hom ≫
    Functor.whiskerRight (integralComparisonPullbackCounit l E k
      ((D.coefficient E).system V) ((D.coefficient E).system W)
      ((D.coefficient E).roos W) ((D.coefficient E).pullback k))
      (integralComparisonDerivedSequencePullback l E h ⋙ coefficientSequenceLimit l E Z)

private theorem etaTransformation_app {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (etaTransformation l D E h k).app K.obj = (integralComparisonEta l E D h k K).hom := by
  rfl

attribute [local irreducible] integralComparisonComposition integralComparisonEta
  integralComparisonUnit

private theorem composition_square {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonComposition l E D h k K).hom ≫
        (etaTransformation l D E h k).app K.obj =
      ((D.coefficient E).pullback (h ≫ k)).realization.hom.app K.obj ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonSystemComposition l E h k).hom.app
            (((D.coefficient E).system V).reduction.obj K.obj)) := by
  rw [etaTransformation_app]
  simp only [integralComparisonComposition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.mapIso_hom, Iso.app_hom]

private abbrev reductionCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  integralComparisonPullbackCounit l E f
    ((D.coefficient E).system Y) ((D.coefficient E).system X)
    ((D.coefficient E).roos X) ((D.coefficient E).pullback f)

private theorem composition_reduction {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    ((D.coefficient E).system Z).reduction.map
        (integralComparisonComposition l E D h k K).hom ≫
        (reductionCounit l D E h).app ((integralDerivedPullback l E k).obj K.obj) ≫
        (integralComparisonDerivedSequencePullback l E h).map
          ((reductionCounit l D E k).app K.obj) =
      (reductionCounit l D E (h ≫ k)).app K.obj ≫
        (integralComparisonSystemComposition l E h k).hom.app
          (((D.coefficient E).system V).reduction.obj K.obj) := by
  have hc := composition_square l D E h k K
  simp only [etaTransformation, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map] at hc
  have hm := mateSquare ((D.coefficient E).system Z).adjunction _ _ _ _ _ hc
  simpa only [reductionCounit, integralComparisonPullbackCounit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Category.assoc]
    using hm

private theorem unit_reduction (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X) :
    ((D.coefficient E).system X).reduction.map (integralComparisonUnit l E D X K).hom =
      (reductionCounit l D E (𝟙 X)).app K.obj ≫
        (integralComparisonSystemUnit l E X).hom.app
          (((D.coefficient E).system X).reduction.obj K.obj) := by
  have hc : (integralComparisonUnit l E D X K).hom ≫
      ((D.coefficient E).system X).adjunction.unit.app K.obj =
        ((D.coefficient E).pullback (𝟙 X)).realization.hom.app K.obj ≫
          (coefficientSequenceLimit l E X).map
            ((integralComparisonSystemUnit l E X).hom.app
              (((D.coefficient E).system X).reduction.obj K.obj)) := by
    have := (D.coefficient E).complete X K
    simp only [integralComparisonUnit, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id, Iso.app_hom]
  have hm := congrArg ((((D.coefficient E).system X).adjunction.homEquiv _ _).symm) hc
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.left_triangle_components, Category.comp_id] at hm
  rw [((D.coefficient E).system X).adjunction.counit_naturality] at hm
  simpa only [reductionCounit, integralComparisonPullbackCounit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Category.assoc]
    using hm

private theorem reduction_transport {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (e : f = g) (K : sfIntegralConstructibleCategory l E Y) :
    ((D.coefficient E).system X).reduction.map
        (eqToHom (congrArg (fun a : X ⟶ Y ↦ (integralDerivedPullback l E a).obj K.obj) e)) ≫
        (reductionCounit l D E g).app K.obj =
      (reductionCounit l D E f).app K.obj ≫
        eqToHom (congrArg (fun a : X ⟶ Y ↦
          (integralComparisonDerivedSequencePullback l E a).obj
            (((D.coefficient E).system Y).reduction.obj K.obj)) e) := by
  cases e
  simp

private theorem composition_associative {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonComposition l E D (j ≫ h) k K).hom ≫
        (integralComparisonComposition l E D j h
          ((constructibleIntegralPullback l E k).obj K)).hom =
      eqToHom (congrArg (fun f : Y ⟶ V ↦
        (integralDerivedPullback l E f).obj K.obj) (Category.assoc j h k).symm) ≫
        (integralComparisonComposition l E D j (h ≫ k) K).hom ≫
        (integralDerivedPullback l E j).map
          ((integralComparisonComposition l E D h k K).hom) := by
  let Kk : sfIntegralConstructibleCategory l E W :=
    ⟨(integralDerivedPullback l E k).obj K.obj,
      ((constructibleIntegralPullback l E k).obj K).property⟩
  let Khk : sfIntegralConstructibleCategory l E Z :=
    ⟨(integralDerivedPullback l E h).obj Kk.obj,
      ((constructibleIntegralPullback l E h).obj Kk).property⟩
  let Kjhk : sfIntegralConstructibleCategory l E Y :=
    ⟨(integralDerivedPullback l E j).obj Khk.obj,
      ((constructibleIntegralPullback l E j).obj Khk).property⟩
  change (integralComparisonComposition l E D (j ≫ h) k K).hom ≫
    (integralComparisonComposition l E D j h Kk).hom =
      eqToHom (congrArg (fun f : Y ⟶ V ↦ (integralDerivedPullback l E f).obj K.obj)
        (Category.assoc j h k)) ≫
      (integralComparisonComposition l E D j (h ≫ k) K).hom ≫
      (integralDerivedPullback l E j).map (integralComparisonComposition l E D h k K).hom
  have := (D.coefficient E).complete Y Kjhk
  have := (D.coefficient E).effective j Khk
  have := (D.coefficient E).effective h Kk
  have := (D.coefficient E).effective k K
  apply unitMapInjective ((D.coefficient E).system Y).adjunction
  simp only [Functor.map_comp]
  apply (cancel_mono ((reductionCounit l D E j).app Khk.obj)).1
  apply (cancel_mono ((integralComparisonDerivedSequencePullback l E j).map
    ((reductionCounit l D E h).app Kk.obj))).1
  apply (cancel_mono ((integralComparisonDerivedSequencePullback l E j).map
    ((integralComparisonDerivedSequencePullback l E h).map
      ((reductionCounit l D E k).app K.obj)))).1
  simp only [Category.assoc]
  have hn := (reductionCounit l D E j).naturality
    (integralComparisonComposition l E D h k K).hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hm := congrArg (integralComparisonDerivedSequencePullback l E j).map
    (composition_reduction l D E h k K)
  simp only [Functor.map_comp] at hm
  rw [hm, reassoc_of% (composition_reduction l D E j (h ≫ k) K),
    reassoc_of% (composition_reduction l D E j h Kk)]
  have ha := (integralComparisonSystemComposition l E j h).hom.naturality
    ((reductionCounit l D E k).app K.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ha
  rw [← ha, reassoc_of% (composition_reduction l D E (j ≫ h) k K),
    reassoc_of% (reduction_transport l D E (Category.assoc j h k) K)]
  have hs := congr_app ((integralQuotientMixedCoherence.{u, u} l).derived_associative
    E j h k) (((D.coefficient E).system V).reduction.obj K.obj)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, eqToHom_app]
    using congrArg ((reductionCounit l D E ((j ≫ h) ≫ k)).app K.obj ≫ ·) hs

private theorem composition_unitSource {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonComposition l E D (𝟙 X) f K).hom ≫
        (integralComparisonUnit l E D X ((constructibleIntegralPullback l E f).obj K)).hom =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralDerivedPullback l E g).obj K.obj) (Category.id_comp f)) := by
  let Kf : sfIntegralConstructibleCategory l E X :=
    ⟨(integralDerivedPullback l E f).obj K.obj,
      ((constructibleIntegralPullback l E f).obj K).property⟩
  change (integralComparisonComposition l E D (𝟙 X) f K).hom ≫
    (integralComparisonUnit l E D X Kf).hom = _
  have := (D.coefficient E).complete X Kf
  have := (D.coefficient E).effective f K
  apply unitMapInjective ((D.coefficient E).system X).adjunction
  apply (cancel_mono ((reductionCounit l D E f).app K.obj)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [unit_reduction l D E X Kf]
  simp only [Category.assoc]
  have hn := (integralComparisonSystemUnit l E X).hom.naturality
    ((reductionCounit l D E f).app K.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
  rw [← hn, reassoc_of% (composition_reduction l D E (𝟙 X) f K),
    reduction_transport l D E (Category.id_comp f) K]
  have hs := congr_app ((integralQuotientMixedCoherence.{u, u} l).derived_unital E f).1
    (((D.coefficient E).system Y).reduction.obj K.obj)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, Category.assoc]
    using congrArg ((reductionCounit l D E (𝟙 X ≫ f)).app K.obj ≫ ·) hs

private theorem composition_unitTarget {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonComposition l E D f (𝟙 Y) K).hom ≫
        (integralDerivedPullback l E f).map ((integralComparisonUnit l E D Y K).hom) =
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (integralDerivedPullback l E g).obj K.obj) (Category.comp_id f)) := by
  let Kf : sfIntegralConstructibleCategory l E X :=
    ⟨(integralDerivedPullback l E f).obj K.obj,
      ((constructibleIntegralPullback l E f).obj K).property⟩
  have := (D.coefficient E).complete X Kf
  have := (D.coefficient E).effective f K
  apply unitMapInjective ((D.coefficient E).system X).adjunction
  apply (cancel_mono ((reductionCounit l D E f).app K.obj)).1
  simp only [Functor.map_comp, Category.assoc]
  have hn := (reductionCounit l D E f).naturality (integralComparisonUnit l E D Y K).hom
  dsimp only [Functor.comp_map] at hn
  rw [hn, unit_reduction l D E Y K, Functor.map_comp]
  rw [reassoc_of% (composition_reduction l D E f (𝟙 Y) K),
    reduction_transport l D E (Category.comp_id f) K]
  have hs := congr_app ((integralQuotientMixedCoherence.{u, u} l).derived_unital E f).2
    (((D.coefficient E).system Y).reduction.obj K.obj)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, Category.assoc]
    using congrArg ((reductionCounit l D E (f ≫ 𝟙 Y)).app K.obj ≫ ·) hs

private theorem composition_naturality {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K J : sfIntegralConstructibleCategory l E V) (r : K ⟶ J) :
    (integralDerivedPullback l E (h ≫ k)).map r.hom ≫
        (integralComparisonComposition l E D h k J).hom =
      (integralComparisonComposition l E D h k K).hom ≫
        (integralDerivedPullback l E h).map ((integralDerivedPullback l E k).map r.hom) := by
  apply (cancel_mono (integralComparisonEta l E D h k J).hom).1
  rw [← etaTransformation_app, Category.assoc, composition_square]
  rw [← Category.assoc, ((D.coefficient E).pullback (h ≫ k)).realization.hom.naturality]
  simp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp]
  rw [(integralComparisonSystemComposition l E h k).hom.naturality]
  rw [Functor.map_comp, ← Category.assoc, ← composition_square]
  have hn := (etaTransformation l D E h k).naturality r.hom
  simp only [Functor.comp_map] at hn ⊢
  rw [Category.assoc, ← hn]
  simp only [Category.assoc]

/-- The counit-normalized pullback comparisons obey geometric composition laws.
Source: Stacks 0D6D and 0941, geometric part of common-stage transport.
Proof: embed each pullback letter into the word calculus. Its coordinate is the
primitive realization b. The composite coordinate is b_h followed by realization
of the whole-system h-counit. Naturality and the adjunction triangle identify
cutting a word with insertion of that counit. Paste the primitive compositor squares.
For three letters both paths have the same system arrow by quotient associativity;
cancel the invertible common coordinate. For an identity letter the coordinate
is the completion unit; the triangle identity and quotient unit laws give both
units. Naturality follows from naturality of b, the counit and the quotient
compositor. Ordinary system laws are precisely quotient composition coherence.
(blueprint: lem-trf-normalized-integral-geometric-coherence). -/
theorem normalizedIntegralGeometricCoherence
    (l : ℕ) [Fact l.Prime] (D : IntegralComparisonSystem.{u} l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IntegralComparisonCompositionLaws l E D := by
  refine {
    systemAssociative := ?_
    systemUnitSource := ?_
    systemUnitTarget := ?_
    naturality := ?_
    associative := ?_
    unitSource := ?_
    unitTarget := ?_ }
  · intro V W Z Y _ _ _ _ j h k N
    have e := congr_app ((integralQuotientMixedCoherence.{u, u} l).ordinary_associative
      E j h k) N
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, eqToHom_app] using e
  · intro X Y _ _ f N
    have e := congr_app ((integralQuotientMixedCoherence.{u, u} l).ordinary_unital E f).1 N
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] using e
  · intro X Y _ _ f N
    have e := congr_app ((integralQuotientMixedCoherence.{u, u} l).ordinary_unital E f).2 N
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app] using e
  · exact composition_naturality l D E
  · exact composition_associative l D E
  · exact composition_unitSource l D E
  · exact composition_unitTarget l D E

end WeilConjectures
