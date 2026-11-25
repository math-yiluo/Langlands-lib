/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SixFunctors.System.SystemDirectImageFiniteComparisonTransitions
import WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact

/-! # Normalization of the direct image of a reduction system

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941 and 099N.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem transition_bijective_of_iso
    {C D : Type*} [Category C] [Category D] (R : D ⥤ C)
    {M M' : C} {N N' : D} (em : M ≅ M') (en : N ≅ N')
    (s : M ⟶ R.obj N) (t : M' ⟶ R.obj N')
    (h : s ≫ R.map en.hom = em.hom ≫ t) (P : D)
    (hs : Function.Bijective (fun a : N ⟶ P ↦ s ≫ R.map a)) :
    Function.Bijective (fun a : N' ⟶ P ↦ t ≫ R.map a) := by
  constructor
  · intro a b hab
    apply (cancel_epi en.hom).1
    apply hs.injective
    simp only [Functor.map_comp, ← Category.assoc, h]
    simpa only [Category.assoc] using congrArg (fun z ↦ em.hom ≫ z) hab
  · intro a
    obtain ⟨b, hb⟩ := hs.surjective (em.hom ≫ a)
    refine ⟨en.inv ≫ b, ?_⟩
    apply (cancel_epi em.hom).1
    rw [← Category.assoc, ← h]
    calc
      (s ≫ R.map en.hom) ≫ R.map (en.inv ≫ b) = s ≫ R.map b := by
        rw [Category.assoc, ← R.map_comp, Iso.hom_inv_id_assoc]
      _ = em.hom ≫ a := hb

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The whole-system direct image of a reduction system is normalized.
This asserts only the universal finite quotient transition property. It does not
choose a limit, a finite evaluation comparison, or a map of Roos triangles.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941 and 099N;
Bhatt--Scholze, Lemma 6.5.11(3).
(blueprint: lem-weil-system-direct-image-reduction-normalized).

Proof: put F = sfCompletedDerivedDirectImage(f). Choose one K-injective
resolution of S.reduction(K) on the sequence site. The sectionwise ordinary
direct-image evaluation square, followed by its derived comparison, identifies
the nth evaluation of its direct image with Rf_*(K tensor^L B_n). The specified
K-flat reduction model identifies the source quotient maps with those of K.
The two-term free completed-coefficient resolution of B_n makes the projection
formula F(K) tensor^L B_n -> Rf_*(K tensor^L B_n) an isomorphism, without any
bound on K or on the cohomological dimension of f. These comparisons commute
with the quotient maps B_m -> B_n: on the two-term resolutions, quotient is
given by identity in degree zero and multiplication by the intervening
uniformizer power in degree minus one. Naturality of the derived direct-image
unit, and the section normalization of the restriction comparison, identify
their transported quotient maps with the actual derived transitions of the
sequence-site direct image. Thus its finite objects and transitions are
isomorphic to the finite reduction system of F(K). Associativity of derived
scalar extension shows that each transition-adjoint of that reduction system
is an isomorphism: (F(K) tensor^L B_m) tensor^L_B_m B_n = F(K) tensor^L B_n.
Transport this across the comparison isomorphisms. By the scalar adjunction,
precomposition with each transition is a bijection on the Hom sets in the
definition of IsNormalizedCoefficientSequence. The argument includes n=0,
identity quotient maps, zero complexes and empty schemes. -/
theorem systemDirectImage_reduction_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    IsNormalizedCoefficientSequence l E Y
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K)) := by
  let levelAdditive (n : ℕ) : (compactSupportLevelDirectImage l E f n).Additive := by
    constructor
    intro M N a b
    ext V x
    rfl
  let levelKInjective (n : ℕ) :
      Abelian.HasKInjectiveResolutions (normalizedDVRModules l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X (integralCoefficientCommRingSheaf l E X n)
  let pullAdditive (n : ℕ) : (compactSupportLevelPullback l E f n).Additive :=
    (Adjunction.ofIsRightAdjoint (compactSupportLevelDirectImage l E f n)).left_adjoint_additive
  let pullLimits (n : ℕ) : PreservesFiniteLimits (compactSupportLevelPullback l E f n) :=
    (Scheme.coefficientProEtaleModulePullback_exact.{u, u} f _).1
  let pullColimits (n : ℕ) : PreservesFiniteColimits (compactSupportLevelPullback l E f n) :=
    (Scheme.coefficientProEtaleModulePullback_exact.{u, u} f _).2
  obtain ⟨_, d, o, ho, hd, _, _⟩ := compactSupportDirectImageEvaluation l E f
  obtain ⟨T, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  let b (n : ℕ) := systemDirectImageFiniteComparison l E f S T d K n
  have hb (n : ℕ) : IsIso (b n) := by
    have := completedDirectImageFiniteProjection_isIso l E f n K
    dsimp only [b, systemDirectImageFiniteComparison]
    infer_instance
  intro m n h P
  exact transition_bijective_of_iso (normalizedDVRRes l E Y h)
    (asIso (b m)) (asIso (b n)) _ _
    (systemDirectImageFiniteComparison_transitions l E f S T o d ho hd K h) P
    (T.reduction_normalized _ h P)

end WeilConjectures
