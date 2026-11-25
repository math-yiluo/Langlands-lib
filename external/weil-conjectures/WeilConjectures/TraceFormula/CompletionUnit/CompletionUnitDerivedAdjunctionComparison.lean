/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitRestrictionAcyclicity
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Normalized derived tensor adjunction comparison

Source: Stacks 07A6, 09T5 and 0D6E, canonical-model construction steps 2--3.
(blueprint: lem-trf-completion-unit-derived-adjunction-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The actual composite unit for exact scalar restriction followed by total limit.
Source: Stacks 0D6E
(blueprint: lem-trf-completion-unit-derived-adjunction-comparison). -/
def systemLimitUnit (M : OrdinaryModel l E W)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W) :
    (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit l E W :=
  Functor.whiskerRight M.limitComparison.hom DerivedCategory.Q ≫
    Functor.whiskerLeft (tower l E W) η ≫
    Functor.whiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv
      (coefficientConstantTowerLimit l E W)

private instance systemKInjectives :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) := by
  let : IsGrothendieckAbelian.{max u (t+1)} (coefficientSequenceModules l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).1
  infer_instance

private theorem systemLimitUnit_isIso
    (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) (hI : I.IsKInjective) :
    IsIso ((systemLimitUnit l E W M η).app I) := by
  let : I.IsKInjective := hI
  let K := (tower l E W).obj I
  obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  let : J.IsKInjective := hJ
  let : QuasiIso j := hj
  have : QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j) :=
    restricted_limit_acyclic l E W I J j
  have : IsIso ((roosLimitFunctor ⋙ DerivedCategory.Q).map j) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight c DerivedCategory.Q) j).1
      (by
        change IsIso (DerivedCategory.Q.map
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j))
        infer_instance)
  have hJnorm := hηnorm J
  have : IsIso (η.app J ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom) := by
    rw [hJnorm]
    infer_instance
  have : IsIso (η.app J) := IsIso.of_isIso_comp_right _
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom
  have : IsIso (η.app K ≫ (coefficientConstantTowerLimit l E W).map
      (DerivedCategory.Q.map j)) := by
    change IsIso (η.app K ≫ (DerivedCategory.Q ⋙
      coefficientConstantTowerLimit l E W).map j)
    rw [← η.naturality j]
    infer_instance
  have : IsIso (η.app K) := IsIso.of_isIso_comp_right _
    ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map j))
  dsimp only [systemLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

private theorem tensor_inverts
    (S : CoefficientDerivedSystemCalculus l E W) (M : OrdinaryModel l E W)
    {Q Q' : CochainComplex (scalarReductionSource l E W) ℤ} (f : Q ⟶ Q')
    (hQ : Q.IsKFlatIndependentCoefficients) (hQ' : Q'.IsKFlatIndependentCoefficients)
    (hf : QuasiIso f) :
    IsIso (DerivedCategory.Q.map ((M.quotient l E W).map f)) := by
  apply (S.isIso_iff_evaluations _).2
  intro n
  have hpres :=
    (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.1
      f hQ hQ' hf
  let : QuasiIso (((scalarReductionExtension l E W n).mapHomologicalComplex
    (.up ℤ)).map f) := hpres
  let e := Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)) DerivedCategory.Q
  have he := NatIso.isIso_map_iff e f
  have : IsIso (((M.quotient l E W ⋙
      (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q).map f) := he.2
    (by
      change IsIso (DerivedCategory.Q.map
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map f))
      infer_instance)
  exact (NatIso.isIso_map_iff
    (Functor.isoWhiskerLeft (M.quotient l E W)
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors) f).2 this

private theorem flat_resolution (X : CochainComplex (scalarReductionSource l E W) ℤ) :
    ∃ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (q : Q ⟶ X),
      (Q.IsKFlatIndependentCoefficients ∧ ∀ p : ℤ, (Q.X p).IsFlatOnSite) ∧
        QuasiIso q := by
  obtain ⟨Q, q, hQ, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) X
  refine ⟨Q, q, ⟨hQ, fun p ↦ ?_⟩, hq⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (completedIntegralCommRingSheafUnrestricted l E W) (Q.X p)).symm (hflat p)

private theorem tensor_derived_exists
    (S : CoefficientDerivedSystemCalculus l E W) (M : OrdinaryModel l E W)
    (δ : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit l E W)
    (hδ : (coefficientSequenceLimit l E W).IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))) :
    ∃ (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
      (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
      (a : L ⊣ coefficientSequenceLimit l E W),
      L.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) ∧
      (∀ Q : CochainComplex (scalarReductionSource l E W) ℤ,
        Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
          IsIso (ε.app Q)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (f : (M.quotient l E W).obj Q ⟶ I),
        a.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫ δ.app I) := by
  classical
  let A := scalarReductionSource l E W
  let B := coefficientSequenceModules l E W
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := M.tensor.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ Q : CochainComplex A ℤ,
      (Q.IsKFlatIndependentCoefficients ∧ ∀ p : ℤ, (Q.X p).IsFlatOnSite) ∧ q.obj Q = X
  have hr : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Q, f, hQ, hf⟩ := flat_resolution l E W X
    exact ⟨q.obj Q, q.map f, ⟨Q, hQ, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hi : ∀ X Y (f : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso A (.up ℤ) f → IsIso (H.map f) := by
    rintro _ _ f ⟨Q, hQ, rfl⟩ ⟨Q', hQ', rfl⟩ hf
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have := tensor_inverts l E W S M f hQ.1 hQ'.1
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf)
    change IsIso (DerivedCategory.Q.map ((M.quotient l E W).map f))
    infer_instance
  obtain ⟨_, L, εh, hL, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (coefficientSequenceDerived l E W) H P hr hi
  let := hL
  obtain ⟨ε, hε, he⟩ := CategoryTheory.leftDerivedOnComplexes M.tensor
    (𝟭 (coefficientSequenceDerived l E W)) L εh
  obtain ⟨a, ha⟩ := derivedAdjunctionOfResolvingClass M.tensor (ordinaryLimit l E W)
    M.adjunction P hr hi L εh hL (coefficientSequenceLimit l E W) δ hδ
  refine ⟨L, ε, a, hε, ?_, ?_⟩
  · intro Q hQ hf
    rw [he]
    exact hcomp (q.obj Q) ⟨Q, ⟨hQ, hf⟩, rfl⟩
  · intro Q I f
    rw [he]
    exact ha Q I f

/-- Derive the ordinary tensor adjunction and compare it with a fixed coherent calculus.
The right comparison is the displayed composite, not a choice of a system unit.
This supplies only the derived-adjunction part of the canonical models: the ordinary
model, constant-tower derived unit and Roos comparison are separate inputs or results.

Source: Stacks sites-cohomology.tex, lemma-adjoint (07A6),
lemma-derived-pushforward-composition (0D6E), and derived.tex,
lemma-derived-adjoint-functors (09T5), with the coefficient adjunction-mate
normalization in steps 2--3 of lem-trf-completion-unit-canonical-models.
(blueprint: lem-trf-completion-unit-derived-adjunction-comparison).

Proof: Derive M.tensor on flat-term K-flat representatives and M.ordinaryLimit on
K-injective systems using the resolving-class derived adjunction theorem. Restriction
of coefficient rings is exact; the normalized pushforward/limit composition theorem
identifies the right-derived unit with systemLimitUnit M η, including its value on
every chain map and its invertibility on K-injective systems. This argument uses
limit-acyclicity supplied by the composition theorem, not preservation of
K-injectivity by scalar restriction. Both the resulting left functor and S.reduction
are left adjoints to the same coefficientSequenceLimit. The unique isomorphism
compatible with the two adjunctions transports the universal left-derived comparison
to ε. Its universal property and invertibility on flat-term K-flat objects transport
along this isomorphism. The resolving-class Hom equation then gives the last clause
for every Q, I and chain map a, without assuming either is a resolution.
To verify the finite comparison, take the finite scalar adjunction mates of the
evaluated counits. S.counit_projection identifies one mate with the actual total-limit
projection; the normalized sequence pushforward/limit theorem gives the same projection
for the other mate. Injectivity of the finite Hom bijection identifies the counits.
On a flat-term K-flat representative, the normalized finite scalar comparison turns
this counit equality into the displayed evaluation equation for ε. Thus the original
S and its coherence are retained, rather than replacing S by a different calculus.
All universal properties are unbounded and apply also to zero objects and degree zero. -/
theorem derivedAdjunctionComparison_exists
    [∀ x : W, Invertible (l : W.residueField x)]
    (S : CoefficientDerivedSystemCalculus l E W)
    (_coherence : CoefficientDerivedSystemCoherence l E W S)
    (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (_hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (_hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (_hη : (coefficientConstantTowerLimit l E W).IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ))) :
    (∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ),
      I.IsKInjective → IsIso ((systemLimitUnit l E W M η).app I)) ∧
    ∃ (ε : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q),
      S.reduction.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ),
        Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
          IsIso (ε.app Q)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : Q.IsKFlatIndependentCoefficients)
        (_hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E W n).map (ε.app Q) ≫
            (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
              ((M.quotient l E W).obj Q) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
          (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q) ≫
            (coefficientFiniteReductionModel l E W Q hQ n).hom) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (a : (M.quotient l E W).obj Q ⟶ I),
        S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
            (ε.app Q ≫ DerivedCategory.Q.map a) =
          DerivedCategory.Q.map
              ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a) ≫
            (systemLimitUnit l E W M η).app I) := by
  have hsys := systemLimitUnit_isIso l E W M c η _hηnorm
  have hδ : (coefficientSequenceLimit l E W).IsRightDerivedFunctor
      (systemLimitUnit l E W M η)
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ)) := by
    apply (CategoryTheory.derives (ordinaryLimit l E W)).isRightDerivedFunctor_of_isIso
      (systemLimitUnit l E W M η)
    intro I
    exact hsys I.obj I.property
  obtain ⟨L, ε, a, hε, hcomp, hhom⟩ :=
    tensor_derived_exists l E W S M (systemLimitUnit l E W M η) hδ
  let e := S.adjunction.leftAdjointUniq a
  let ε' : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q e.hom ≫ ε
  have hε' : S.reduction.IsLeftDerivedFunctor ε'
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    (Functor.isLeftDerivedFunctor_iff_of_iso
      (LF := S.reduction) (LF' := L) (α := ε') ε
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) e rfl).2 hε
  have hhom' : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (ε'.app Q ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M η).app I := by
    intro Q I f
    rw [← hhom Q I f]
    change S.adjunction.homEquiv _ _
      ((e.hom.app (DerivedCategory.Q.obj Q) ≫ ε.app Q) ≫ DerivedCategory.Q.map f) = _
    rw [Category.assoc, S.adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [show S.adjunction.unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientSequenceLimit l E W).map (e.hom.app (DerivedCategory.Q.obj Q)) =
        a.unit.app (DerivedCategory.Q.obj Q) from
          S.adjunction.unit_leftAdjointUniq_hom_app a _]
    exact (a.homEquiv_unit _ _ _).symm
  refine ⟨hsys, ε', hε', ?_, ?_, hhom'⟩
  · intro Q hQ hf
    have := hcomp Q hQ hf
    dsimp only [ε', NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · apply finiteComparison_of_unit l E W S M c _hc η _hηnorm ε'
    intro Q
    have h := hhom' Q ((M.quotient l E W).obj Q) (𝟙 _)
    have hid : ε'.app Q ≫ DerivedCategory.Q.map
        (𝟙 ((M.quotient l E W).obj Q)) = ε'.app Q := by
      rw [(DerivedCategory.Q (C := coefficientSequenceModules l E W)).map_id]
      exact Category.comp_id _
    have hh := (congrArg (S.adjunction.homEquiv (DerivedCategory.Q.obj Q)
      (DerivedCategory.Q.obj ((M.quotient l E W).obj Q))) hid).symm.trans h
    simpa only [Adjunction.homEquiv_id,
      systemLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hh

end WeilConjectures.CompletionUnit
