/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionRestrictedRoos
import all WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityLimit
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionModelPasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Total-limit composition for section-normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 0941. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem composition_factors
    {C B D : Type*} [Category C] [Category B] [Category D]
    [Abelian C] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : C ⥤ B) (G : B ⥤ D) (H : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G) (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso a ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

private theorem localize_composition_models
    {C B D : Type*} [Category C] [Category B] [Category D]
    [Abelian C] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : C ⥤ B) (G : B ⥤ D) (H : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G)
    (X : CochainComplex C ℤ) (Y : CochainComplex B ℤ) (Z W : CochainComplex D ℤ)
    (rF : (F.mapHomologicalComplex (.up ℤ)).obj X ⟶ Y)
    (rG : (G.mapHomologicalComplex (.up ℤ)).obj Y ⟶ Z)
    (rH : (H.mapHomologicalComplex (.up ℤ)).obj X ⟶ W) (ms : W ⟶ Z)
    (hr : (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app X ≫
      (G.mapHomologicalComplex (.up ℤ)).map rF ≫ rG = rH ≫ ms) :
    (Functor.mapDerivedCategoryNatIso a ≪≫
      (Functor.mapDerivedCategoryCompIso F G).symm).hom.app (DerivedCategory.Q.obj X) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map rF) ≫
      G.mapDerivedCategoryFactors.hom.app Y ≫ DerivedCategory.Q.map rG =
    H.mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map rH ≫
      DerivedCategory.Q.map ms := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := G.mapDerivedCategoryFactors.hom.naturality rF
  change G.mapDerivedCategory.map (DerivedCategory.Q.map rF) ≫
    G.mapDerivedCategoryFactors.hom.app Y =
      G.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map rF) at hn
  slice_lhs 3 4 => exact hn
  slice_lhs 1 3 => exact composition_factors F G H a X
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
  rw [hr]

/-- The total-limit equation, on arbitrary ambient coefficient systems.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 0941 (blueprint: lem-pod-reindexing-composition-limit-equation).

Proof: represent a coefficient system by a strict complex C. RestrictedGenerators
identifies the comparison between reindexing its restricted tower and restricting
its sequence pullback with the actual sectionwise adjunction-unit map. The unit
normalization of the strict sequence compositor makes the two iterated restricted
maps equal, including their transition morphisms. The ordinary compositor is fixed
on all original sections by hcomposition. Apply every product projection to the
product maps in the three Roos comparisons: both composite paths are restriction
along this same Over.mapComp arrow. RoosFst and RoosSnd then give equality on both
coordinates of the mapping cocone of 1-s, hence equality of the entire chain maps.
The intermediate source/target Roos models are identified using their computes
normalization on a simultaneous K-injective resolution. Naturality extends this
identification to C, so these model isomorphisms cancel in the pasted square.
Substitute the three LimitModel formulas and localize the strict square. The
localization factors are natural and their composition comparison is precisely
the one in A.compositionDerived and integralComparisonSystemComposition.
Every derived system is isomorphic to a localized complex; naturality transports
the resulting equality to it. No finite evaluation is treated as faithful.
For the zero complex or an empty scheme the same projection and coordinate
formulas apply. This statement assumes no tensor law and proves no reduction
or tensor composition equation. -/
theorem podReindexingCompositionLimit
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (hcomposition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f] (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x) :
    ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)],
      ∀ N : coefficientSequenceDerived l E V,
        (A.compositionDerived l E h f).hom.app ((coefficientSequenceLimit l E V).obj N) ≫
          (podOrdinaryReindex l E h).map ((A.completion f).limit.hom.app N) ≫
          (A.completion h).limit.hom.app ((integralComparisonDerivedSequencePullback l E f).obj N) =
        (A.completion (h ≫ f)).limit.hom.app N ≫
          (coefficientSequenceLimit l E Z).map
            ((integralComparisonSystemComposition l E h f).hom.app N) := by
  intro V W Z h f _ _ _ _ _ N
  let Df := A.completion f
  let Dh := A.completion h
  let Dc := A.completion (h ≫ f)
  let F := podOrdinaryReindex l E f
  let G := podOrdinaryReindex l E h
  let H := podOrdinaryReindex l E (h ≫ f)
  let S := integralComparisonDerivedSequencePullback l E f
  let T := integralComparisonDerivedSequencePullback l E h
  let U := integralComparisonDerivedSequencePullback l E (h ≫ f)
  let R₀ := coefficientSequenceLimit l E V
  let R₁ := coefficientSequenceLimit l E W
  let R₂ := coefficientSequenceLimit l E Z
  let k := A.compositionDerived l E h f
  let s := integralComparisonSystemComposition l E h f
  have he : whiskerLeft R₀ k.hom ≫ whiskerRight Df.limit.hom G ≫
      whiskerLeft S Dh.limit.hom = Dc.limit.hom ≫ whiskerRight s.hom R₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro C
    let Cf := ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C
    let Chf := ((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj Cf
    let Cc := ((integralComparisonSequencePullback l E (h ≫ f)).mapHomologicalComplex (.up ℤ)).obj C
    let σ := (NatTrans.mapHomologicalComplex
      (integralComparisonSequenceComposition l E h f).hom (.up ℤ)).app C
    let sf := (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C
    let th := (integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.hom.app Cf
    let cc := (integralComparisonSequencePullback l E (h ≫ f)).mapDerivedCategoryFactors.hom.app C
    let β₂ := limit_roos_iso l E Z Dh.targetRoos
    let rF := (Df.roos (podRestrictedTower l E C)).hom ≫
      integralOperationsRoosFunctor.map (Df.restricted C).hom
    let rG := (Dh.roos (podRestrictedTower l E Cf)).hom ≫
      integralOperationsRoosFunctor.map (Dh.restricted Cf).hom
    let rH := (Dc.roos (podRestrictedTower l E C)).hom ≫
      integralOperationsRoosFunctor.map (Dc.restricted C).hom
    let Tσ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).map σ)
    have hmf : PodCompletionReindex.LimitModel l E f Df := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := hcompletion f
      exact hm
    have hmg : PodCompletionReindex.LimitModel l E h Dh := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := hcompletion h
      exact hm
    have hmc : PodCompletionReindex.LimitModel l E (h ≫ f) Dc := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ :=
        hcompletion (h ≫ f)
      exact hm
    have hmfC := hmf C
    have hmgC := hmg Cf
    have hmcC := hmc C
    rw [roos_model_unique l E W Dh.sourceRoos Df.targetRoos] at hmgC
    rw [roos_model_unique l E V Dc.sourceRoos Df.sourceRoos,
      roos_model_unique l E Z Dc.targetRoos Dh.targetRoos] at hmcC
    have hstrict := podCompositionRestrictedRoos l E h f A (hcompletion f)
      (hcompletion h) (hcompletion (h ≫ f)) (hcomposition h f) C
    have hlocalized := localize_composition_models
      (isoReductionIntegralInverse l E f) (isoReductionIntegralInverse l E h)
      (isoReductionIntegralInverse l E (h ≫ f)) (A.composition h f)
      (integralOperationsRoos (podRestrictedTower l E C))
      (integralOperationsRoos (podRestrictedTower l E Cf))
      (integralOperationsRoos (podRestrictedTower l E Chf))
      (integralOperationsRoos (podRestrictedTower l E Cc)) rF rG rH
      (integralOperationsRoosFunctor.map Tσ) (by
        simpa only [rF, rG, rH, Functor.map_comp, Category.assoc] using hstrict)
    have hσ := composition_factors (integralComparisonSequencePullback l E f)
      (integralComparisonSequencePullback l E h)
      (integralComparisonSequencePullback l E (h ≫ f))
      (integralComparisonSequenceComposition l E h f) C
    have hβ := β₂.hom.naturality σ
    change R₂.map (DerivedCategory.Q.map σ) ≫
      (podLimitRoos l E Dh.targetRoos Chf).hom =
      (podLimitRoos l E Dh.targetRoos Cc).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map Tσ) at hβ
    change k.hom.app (R₀.obj (DerivedCategory.Q.obj C)) ≫
      G.map (Df.limit.hom.app (DerivedCategory.Q.obj C)) ≫
      Dh.limit.hom.app (S.obj (DerivedCategory.Q.obj C)) =
        Dc.limit.hom.app (DerivedCategory.Q.obj C) ≫ R₂.map (s.hom.app _)
    apply podCompositionModelPasting Df.limit.hom Dh.limit.hom Dc.limit.hom k.hom s.hom
      (DerivedCategory.Q.obj C) (DerivedCategory.Q.obj Cf)
      (DerivedCategory.Q.obj Chf) (DerivedCategory.Q.obj Cc)
      sf th cc (DerivedCategory.Q.map σ)
      _ _ _ _ (podLimitRoos l E Df.sourceRoos C) (podLimitRoos l E Df.targetRoos Cf)
      (podLimitRoos l E Dh.targetRoos Chf) (podLimitRoos l E Dh.targetRoos Cc)
      ((isoReductionIntegralInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map rF)
      ((isoReductionIntegralInverse l E h).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map rG)
      ((isoReductionIntegralInverse l E (h ≫ f)).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map rH)
      (DerivedCategory.Q.map (integralOperationsRoosFunctor.map Tσ))
    · exact hσ
    · exact hβ
    · simpa only [rF, Functor.map_comp, Category.assoc] using hmfC
    · simpa only [rG, Functor.map_comp, Category.assoc] using hmgC
    · simpa only [rH, Functor.map_comp, Category.assoc] using hmcC
    · simpa only [k, PodReindexFamily.compositionDerived, podOrdinaryReindex,
        Category.assoc] using hlocalized
  exact congr_app he N

end WeilConjectures
