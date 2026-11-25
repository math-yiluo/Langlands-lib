/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.TraceFormula.Compact.CompactSupportEvaluationOrdinaryMate
import WeilConjectures.TraceFormula.Compact.CompactSupportEvaluationDirectImageAcyclic
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived direct-image evaluation for compact support

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 07A4 and 0941.
(blueprint: lem-trf-compact-support-direct-image-derived-evaluation).

This is the derived component of the direct-image evaluation theorem.  The ordinary
comparison is supplied as an input, so this statement is strictly smaller than the
parent existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u a b c d v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

section FormalNormalization

variable {C : Type a} {A : Type b} {C' : Type c} {A' : Type d}
  [Category.{v} C] [Category.{v} A] [Category.{v} C'] [Category.{v} A']
  [Abelian C] [Abelian A] [Abelian C'] [Abelian A']
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} C'] [HasDerivedCategory.{w} A']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  {L : A ⥤ C} {G : C ⥤ A} {L' : A' ⥤ C'} {G' : C' ⥤ A'}
  {H : C ⥤ C'} {K : A ⥤ A'}
  [L.Additive] [G.Additive] [L'.Additive] [G'.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

private theorem cochain_unit_eq (J : CochainComplex C ℤ) :
    CategoryTheory.UnboundedExactTower.cochainUnit G J = G.rightDerivedFunctorUnitQ J := by
  unfold CategoryTheory.UnboundedExactTower.cochainUnit Functor.rightDerivedFunctorUnitQ
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  erw [(DerivedCategory.Qh (C := A)).map_id]
  repeat erw [Category.id_comp]

private theorem unit_model (adj : L ⊣ G) (adj' : L' ⊣ G')
    (s : K ⋙ L' ≅ L ⋙ H) (J : CochainComplex C ℤ) :
    K.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
      K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)).app
          (DerivedCategory.Q.obj J) ≫
      G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app J) ≫
      G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J) := by
  have ht := CategoryTheory.UnboundedExactTower.localized_mate_cochain_normalization
    adj adj' s J
  rw [cochain_unit_eq, cochain_unit_eq] at ht
  exact ht

private theorem normalized_of_unit
    (ordinary : G ⋙ K ≅ H ⋙ G')
    (right : G.rightDerivedFunctor ⋙ K.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (h : ∀ J : CochainComplex C ℤ,
      K.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) ≫
        right.hom.app (DerivedCategory.Q.obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app J) ≫
        G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J)) :
    CompactSupportDerivedSquareNormalization G G' H K ordinary.symm right.symm := by
  intro J hJ I hI r hr
  have : IsIso (G.rightDerivedFunctorUnitQ J) := by
    rw [G.rightDerivedFunctorUnitQ_eq J]
    infer_instance
  apply (cancel_epi (right.hom.app (DerivedCategory.Q.obj J))).mp
  apply (cancel_epi (K.mapDerivedCategoryFactors.inv.app
    ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
      K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J))).mp
  simp only [Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (h J)]
  rw [← G'.rightDerivedFunctorUnitQ_naturality_assoc r,
    G'.rightDerivedFunctorUnitQ_eq I]
  simp only [G.rightDerivedFunctorUnitQ_eq J, ← Functor.map_comp_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rfl

private theorem iso_of_unit
    (ordinary : G ⋙ K ≅ H ⋙ G')
    (right : G.rightDerivedFunctor ⋙ K.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (h : ∀ J : CochainComplex C ℤ,
      K.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) ≫
        right.app (DerivedCategory.Q.obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app J) ≫
        G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J))
    (acyclic : ∀ (J : CochainComplex C ℤ) [J.IsKInjective],
      IsIso (G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J))) :
    IsIso right := by
  have hQ (J : CochainComplex C ℤ) [J.IsKInjective] :
      IsIso (right.app (DerivedCategory.Q.obj J)) := by
    have : IsIso (G.rightDerivedFunctorUnitQ J) := by
      rw [G.rightDerivedFunctorUnitQ_eq J]
      infer_instance
    have := acyclic J
    let b := K.mapDerivedCategoryFactors.inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J)
    have : IsIso (b ≫ right.app (DerivedCategory.Q.obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J)) := by
      simp only [b, Category.assoc]
      rw [h J]
      infer_instance
    have := IsIso.of_isIso_comp_left b
      (right.app (DerivedCategory.Q.obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J))
    exact IsIso.of_isIso_comp_right (right.app (DerivedCategory.Q.obj J))
      (G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J))
  have (M : DerivedCategory C) : IsIso (right.app M) := by
    obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    let := hJ
    exact (NatTrans.isIso_app_iff_of_iso right e).mpr (hQ J)
  exact NatIso.isIso_of_isIso_app _

end FormalNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Derived evaluation, arbitrary-resolution normalization, and the two mate equations.

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 07A4 and 0941.
Take the inverse ordinary mate and use the sequence-module evaluation theorem to
prove it invertible. Localizing it gives `left`; its derived adjunction mate gives
`right`. The cochain mate normalization identifies this mate with the ordinary
comparison and the two canonical right-derived units. On K-injective systems,
finite direct-image acyclicity of evaluation makes both units invertible, hence
makes the mate invertible. Naturality of the right-derived unit then proves the
formula for an arbitrary finite-level K-injective resolution. Finally the unit-mate
and counit-mate identities give the two displayed equations. The finite-prefix
derived-extension argument is confined to the acyclicity lemma; evaluation itself
is not assumed to preserve K-injective complexes.
(blueprint: lem-trf-compact-support-direct-image-derived-evaluation).
-/
theorem compactSupportDirectImageDerivedEvaluation
    {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    [(integralComparisonSequenceDirectImage l E p).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E Z)]
    [∀ n : ℕ, (compactSupportLevelDirectImage l E p n).Additive]
    [∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)]
    [∀ n : ℕ, (compactSupportLevelPullback l E p n).Additive]
    [∀ n : ℕ, PreservesFiniteLimits (compactSupportLevelPullback l E p n)]
    [∀ n : ℕ, PreservesFiniteColimits (compactSupportLevelPullback l E p n)]
    (ordinary : ∀ n : ℕ,
        integralComparisonSequenceDirectImage l E p ⋙ coefficientSequenceEvaluation l E Y n ≅
          coefficientSequenceEvaluation l E Z n ⋙ compactSupportLevelDirectImage l E p n) :
    ∃ (left : ∀ n : ℕ,
        integralComparisonDerivedSequencePullback l E p ⋙
            coefficientSequenceDerivedEvaluation l E Z n ≅
          coefficientSequenceDerivedEvaluation l E Y n ⋙
            (compactSupportLevelPullback l E p n).mapDerivedCategory)
      (right : ∀ n : ℕ,
        (integralComparisonSequenceDirectImage l E p).rightDerivedFunctor ⋙
            coefficientSequenceDerivedEvaluation l E Y n ≅
          coefficientSequenceDerivedEvaluation l E Z n ⋙
            (compactSupportLevelDirectImage l E p n).rightDerivedFunctor),
      (∀ n : ℕ,
        letI := coefficientSequenceEvaluation_additiveInstance l E Z n
        letI := coefficientSequenceEvaluation_additiveInstance l E Y n
        letI := coefficientSequenceEvaluation_limits l E Z n
        letI := coefficientSequenceEvaluation_colimits l E Z n
        letI := coefficientSequenceEvaluation_limits l E Y n
        letI := coefficientSequenceEvaluation_colimits l E Y n
        CompactSupportDerivedSquareNormalization
            (integralComparisonSequenceDirectImage l E p) (compactSupportLevelDirectImage l E p n)
            (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
            (ordinary n).symm (right n).symm) ∧
      (∀ (n : ℕ) M,
          (coefficientSequenceDerivedEvaluation l E Y n).map ((compactSupportCanonicalPAdjunction l
            E p).unit.app M) ≫
            (right n).hom.app ((integralComparisonDerivedSequencePullback l E p).obj
              M) ≫
            ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor).map
              ((left n).hom.app M) =
              (compactSupportCanonicalPLevelAdjunction l E p n).unit.app
                ((coefficientSequenceDerivedEvaluation l E Y n).obj M)) ∧
      (∀ (n : ℕ) N,
          ((compactSupportLevelPullback l E p n).mapDerivedCategory).map
              ((right n).hom.app N) ≫
            (compactSupportCanonicalPLevelAdjunction l E p n).counit.app
              ((coefficientSequenceDerivedEvaluation l E Z n).obj N) =
              (left n).inv.app (((integralComparisonSequenceDirectImage l E
                p).rightDerivedFunctor).obj N) ≫
                (coefficientSequenceDerivedEvaluation l E Z n).map
                  ((compactSupportCanonicalPAdjunction l E p).counit.app N)) := by
  classical
  let : (integralComparisonSequenceDirectImage l E p).leftAdjoint.Additive :=
    integralComparisonSequencePullbackAdditive l E p
  let : PreservesFiniteLimits
      (integralComparisonSequenceDirectImage l E p).leftAdjoint :=
    integralComparisonSequencePullbackLimits l E p
  let : PreservesFiniteColimits
      (integralComparisonSequenceDirectImage l E p).leftAdjoint :=
    integralComparisonSequencePullbackColimits l E p
  let (n : ℕ) : (compactSupportLevelDirectImage l E p n).leftAdjoint.Additive :=
    inferInstanceAs (compactSupportLevelPullback l E p n).Additive
  let (n : ℕ) : PreservesFiniteLimits
      (compactSupportLevelDirectImage l E p n).leftAdjoint :=
    inferInstanceAs (PreservesFiniteLimits (compactSupportLevelPullback l E p n))
  let (n : ℕ) : PreservesFiniteColimits
      (compactSupportLevelDirectImage l E p n).leftAdjoint :=
    inferInstanceAs (PreservesFiniteColimits (compactSupportLevelPullback l E p n))
  let a := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E p)
  let b (n : ℕ) := Adjunction.ofIsRightAdjoint (compactSupportLevelDirectImage l E p n)
  let (n : ℕ) := compactSupportEvaluationOrdinaryMate_isIso l E p n (ordinary n)
  let s (n : ℕ) := asIso (((mateEquiv a (b n)).symm
    (TwoSquare.mk _ _ _ _ (ordinary n).hom)))
  let left (n : ℕ) := (Functor.mapDerivedCategorySquareIso (s n)).symm
  let beta (n : ℕ) := (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    (b n).mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategorySquareIso (s n)).hom)
  have hs (n : ℕ) : (mateEquiv a (b n) (s n).hom) =
      (ordinary n).hom := by
    exact ((mateEquiv a (b n)).apply_symm_apply
      (TwoSquare.mk _ _ _ _ (ordinary n).hom))
  have hu (n : ℕ) (J : CochainComplex (coefficientSequenceModules l E Z) ℤ) :
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.inv.app
          (((integralComparisonSequenceDirectImage l E p).mapHomologicalComplex
            (.up ℤ)).obj J) ≫
        (coefficientSequenceDerivedEvaluation l E Y n).map
          ((integralComparisonSequenceDirectImage l E p).rightDerivedFunctorUnitQ J) ≫
        (beta n).app (DerivedCategory.Q.obj J) ≫
        (compactSupportLevelDirectImage l E p n).rightDerivedFunctor.map
          ((coefficientSequenceEvaluation l E Z n).mapDerivedCategoryFactors.hom.app J) =
      DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app J) ≫
        (compactSupportLevelDirectImage l E p n).rightDerivedFunctorUnitQ
          (((coefficientSequenceEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj J) := by
    have h := unit_model a (b n) (s n) J
    rw [hs n] at h
    exact h
  have (n : ℕ) : IsIso (beta n) :=
    iso_of_unit (ordinary n) (beta n) (hu n)
      (fun J _ ↦ compactSupportEvaluationDirectImage_acyclic l E p n J)
  let right (n : ℕ) := asIso (beta n)
  refine ⟨left, right, ?_, ?_, ?_⟩
  · intro n
    exact normalized_of_unit (ordinary n) (right n) (hu n)
  · intro n M
    have h := unit_mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      (b n).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso (s n)).hom M
    change (coefficientSequenceEvaluation l E Y n).mapDerivedCategory.map
        (a.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
      (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        (b n).mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategorySquareIso (s n)).hom).app
          ((integralComparisonSequenceDirectImage l E p).leftAdjoint.mapDerivedCategory.obj M) ≫
      (compactSupportLevelDirectImage l E p n).rightDerivedFunctor.map
        ((Functor.mapDerivedCategorySquareIso (s n)).inv.app M) =
      (b n).mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategory.obj M)
    rw [reassoc_of% h, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro n N
    exact mateEquiv_counit a.mapDerivedCategoryRightDerivedAdjunction
      (b n).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso (s n)).hom N

end WeilConjectures
