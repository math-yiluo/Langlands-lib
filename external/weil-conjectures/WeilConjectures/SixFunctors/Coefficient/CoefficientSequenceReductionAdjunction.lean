/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import WeilConjectures.SixFunctors.Coefficient.CoefficientSequenceProjectionTransition

/-! # Reduction adjunction before choosing tensor presentations

Source: Stacks 06YS, 06YY, 07A6 and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The sequence projection supplies the reduction adjunction and its finite models,
independently of every choice of tensor presentation.
Source: Stacks 06YS, 06YY, 07A6 and 0941.

Proof: apply SequenceProjection.pushforwardLimitProjections to the completed
coefficient ring, the quotient ring tower, and the completion projections. Transport
its ordinary strict systems through strictSystemSequenceEquivalence and derive that
exact equivalence. The restricted-tower functor is naturally identified with
coefficientSequenceRestriction: both have the same completed-linear sections and
quotient transitions. Uniqueness of right derived functors identifies the theorem's
right adjoint with coefficientSequenceLimit. This identification preserves each
projection, by the defining right-derived descent equation for
coefficientConstantTowerProjection and the exact evaluation factors.
Transport the adjunction through this identification. Uniqueness of the left
derived extension at each level identifies its evaluated left adjoint with
coefficientFiniteDerivedExtension, preserving its universal K-flat counit. The
normalized derived level adjunction is therefore coefficientFiniteAdjunction.
The counit projection clause of pushforwardLimitProjections now gives the displayed
Hom-equivalence equation. For a flat-term K-flat Q take the ordinary sequence
extension of Q, and localize its universal left-derived counit. Its finite components
are the scalar-extension counits and its transitions send b tensor x to rho(b)
tensor x; uniqueness of the ordinary scalar model gives precisely
CoefficientReductionModels. Finally the transition adjunct for reduction identifies
with the derived associativity isomorphism B_n tensor over B_m (B_m tensor over A Q)
= B_n tensor over A Q. It is invertible. The finite scalar adjunction converts this
into the universal Hom-bijection defining IsNormalizedCoefficientSequence. This also
covers equal levels, the zero complex, and the empty scheme.
(blueprint: lem-coef-sequence-reduction-adjunction)
-/
theorem coefficientSequenceReductionAdjunction_exists :
    ∃ (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
      (adj : L ⊣ coefficientSequenceLimit l E W)
      (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
        coefficientFiniteDerivedExtension l E W n),
      CoefficientReductionModels l E W L ρ ∧
      (∀ P, IsNormalizedCoefficientSequence l E W (L.obj P)) ∧
      ∀ (N : coefficientSequenceDerived l E W) (n : ℕ),
        (coefficientFiniteAdjunction l E W n).homEquiv _ _
          ((ρ n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
            (coefficientSequenceDerivedEvaluation l E W n).map (adj.counit.app N)) =
          (coefficientSequenceProjection l E W n).app N := by
  obtain ⟨M⟩ := OrdinaryQuotient.ordinaryModel_exists l E W
  obtain ⟨L, ⟨adj⟩⟩ := OrdinaryQuotient.leftAdjoint_exists l E W
  obtain ⟨ε, -, hiso, hhom⟩ := OrdinaryQuotient.reductionComparison_exists l E W M L adj
  let θ (n : ℕ) : coefficientFiniteDerivedExtension l E W n ⟶
      L ⋙ coefficientSequenceDerivedEvaluation l E W n :=
    { app := fun P ↦ ((coefficientFiniteAdjunction l E W n).homEquiv _ _).symm
        (adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P))
      naturality := by
        intro P P' f
        apply ((coefficientFiniteAdjunction l E W n).homEquiv _ _).injective
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        have hp := (coefficientSequenceProjection l E W n).naturality (L.map f)
        dsimp only [Functor.comp_map] at hp
        rw [Functor.comp_map, Category.assoc, ← hp]
        simp only [← Category.assoc]
        exact congrArg (· ≫ _) (adj.unit.naturality f) }
  have hθ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
      adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P) =
        (coefficientFiniteAdjunction l E W n).unit.app P ≫
          (coefficientFiniteDerivedRestriction l E W n).map ((θ n).app P) := by
    rw [← (coefficientFiniteAdjunction l E W n).homEquiv_unit P _ ((θ n).app P)]
    exact (Equiv.apply_symm_apply _ _).symm
  have hθiso (n : ℕ) : IsIso (θ n) := by
    have hflatIso (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) :
        IsIso ((θ n).app (DerivedCategory.Q.obj Q)) := by
      have := hiso Q hQ hflat
      have h := OrdinaryQuotient.finiteComparison_of_unitProjection l E W M
        (OrdinaryQuotient.termwiseLimitComparison l E W)
        (OrdinaryQuotient.termwiseLimitComparison_projection l E W)
        (OrdinaryQuotient.constantLimitUnit l E W)
        (OrdinaryQuotient.constantLimitUnit_normalization l E W) L adj θ hθ ε
        (OrdinaryQuotient.reductionComparison_unit l E W M _ L adj ε hhom) Q hQ n
      rw [← IsIso.eq_comp_inv] at h
      rw [h]
      infer_instance
    have happ (P : DerivedCategory (scalarReductionSource l E W)) : IsIso ((θ n).app P) := by
      obtain ⟨Q, q, ⟨hQ, hflat⟩, hq⟩ := OrdinaryQuotient.exists_flatTermKFlatResolution l E W
        (DerivedCategory.Q.objPreimage P)
      have : IsIso (DerivedCategory.Q.map q) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := q)).2 hq
      exact (NatTrans.isIso_app_iff_of_iso (θ n)
        (asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso P)).1
          (hflatIso Q hQ hflat)
    exact NatIso.isIso_of_isIso_app _
  let ρ (n : ℕ) : L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n := (asIso (θ n)).symm
  have hunitproj (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
      adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P) =
        (coefficientFiniteAdjunction l E W n).unit.app P ≫
          (coefficientFiniteDerivedRestriction l E W n).map ((ρ n).inv.app P) :=
    hθ P n
  refine ⟨L, adj, ρ, ?_, ?_, ?_⟩
  · intro Q hQ hflat
    have := hiso Q hQ hflat
    refine ⟨(M.quotient l E W).obj Q, asIso (ε.app Q),
      fun n ↦ (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app Q, ?_, ?_⟩
    · intro n
      exact OrdinaryQuotient.finiteComparison_of_unit l E W M L adj ρ hunitproj ε hhom Q hQ
        hflat n
    · intro m n h
      apply HomologicalComplex.hom_ext
      intro i
      exact M.transition (Q.X i) h
  · exact isNormalizedCoefficientSequence_of_unitProjection l E W L adj ρ hunitproj
  · intro N n
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit, ← hunitproj,
      Category.assoc]
    have hp := (coefficientSequenceProjection l E W n).naturality (adj.counit.app N)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hp
    rw [← hp, ← Category.assoc, adj.right_triangle_components, Category.id_comp]

end WeilConjectures
