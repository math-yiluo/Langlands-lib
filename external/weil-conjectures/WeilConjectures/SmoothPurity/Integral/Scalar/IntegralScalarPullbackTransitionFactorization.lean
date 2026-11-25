/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerIdentification
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedCoefficientQuotientComparison
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedFinitePullbackComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelReduction
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.RamifiedPullback.FinitePullbackTransitionGenerators

/-! # Cofinal diagonal of the finite scalar pullback map

Source: Stacks Tags 07A4 and 0941, and the cofinal uniformizer-filtration
argument of lem-pur-integral-scalar-pullback-roos-quasi-iso.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted

attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem ramified_scalar_eq (W : AlgebraicGeometry.Scheme.{u}) :
    RamifiedPullback.scalar.{u, u} (integralCompletedScalarMap l E L ι W) =
      integralOrdinaryScalar l E L ι W := by
  let φ := integralCompletedScalarMap l E L ι W
  have h₁ : RamifiedPullback.scalar.{u, u} φ = CategoryTheory.CochainPullback.extensionFunctor φ :=
    CategoryTheory.Functor.ext (RamifiedPullback.scalarWitness.{u, u} φ).choose_spec.choose
      (fun _ _ a ↦ (RamifiedPullback.scalarWitness.{u, u} φ).choose_spec.choose_spec.choose a)
  have h₂ : integralOrdinaryScalar l E L ι W =
      CategoryTheory.CochainPullback.extensionFunctor φ :=
    CategoryTheory.Functor.ext (scalar_obj l E L ι W) (fun _ _ a ↦ scalar_map l E L ι W a)
  exact h₁.trans h₂.symm

private theorem scalar_comparison_transport {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n m : ℕ)
    (FX : integralTowerModules l E X ⥤ integralTowerModules l L X)
    (FY : integralTowerModules l E Y ⥤ integralTowerModules l L Y)
    [FX.PreservesZeroMorphisms] [FY.PreservesZeroMorphisms]
    (hFX : FX = integralOrdinaryScalar l E L ι X)
    (hFY : FY = integralOrdinaryScalar l E L ι Y)
    (hX : ∀ M, FX.obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E L ι X) M)
    (hY : ∀ M, FY.obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E L ι Y) M)
    (d : (FX.mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackLevel l E f n).obj P) ≅
      (integralOperationsPullbackLevel l L f m).obj
        ((FY.mapHomologicalComplex (.up ℤ)).obj P))
    (hd : ∀ (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
      (d.hom.f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
        (tensorSection (integralCompletedScalarMap l E L ι X) FX hX _ _ 1
          (integralOperationsPullbackGenerator l E f n _ V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
      integralOperationsPullbackGenerator l L f m _ V
        (unrestrictedIntegralTensorSection l L Y m (FY.obj (P.X i)) (op V) 1
          (tensorSection (integralCompletedScalarMap l E L ι Y) FY hY
            (P.X i) (op V) 1 x))) :
    ∃ d' : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackLevel l E f n).obj P) ≅
      (integralOperationsPullbackLevel l L f m).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P),
      ∀ (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (d'.hom.f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f n _ V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f m _ V
          (unrestrictedIntegralTensorSection l L Y m
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)) := by
  subst FX
  subst FY
  have hx : hX = scalar_obj l E L ι X := Subsingleton.elim _ _
  have hy : hY = scalar_obj l E L ι Y := Subsingleton.elim _ _
  rw [hx, hy] at hd
  refine ⟨d, ?_⟩
  intro i V x
  simpa only [tensorSection_eq] using hd i V x

private theorem ramified_level {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    ∃ (m : ℕ) (h : n ≤ m)
      (d : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsPullbackLevel l E f n).obj P) ≅
        (integralOperationsPullbackLevel l L f m).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)),
      ∀ (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (d.hom.f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f n _ V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f m _ V
          (unrestrictedIntegralTensorSection l L Y m
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)) := by
  classical
  obtain ⟨e, he, hideal, _⟩ := RamifiedPullback.ramification_exists l E L ι
  have hexp (k : ℕ) : RamifiedPullback.index e k + 1 = e * (k + 1) := by
    have hp : 0 < e * (k + 1) := Nat.mul_pos he (by omega)
    dsimp [RamifiedPullback.index]
    omega
  have hmono : Monotone (RamifiedPullback.index e) := by
    intro a b hab
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right hab 1)) 1
  have hsame (k : ℕ) : k ≤ RamifiedPullback.index e k := by
    have hh := Nat.mul_le_mul_right (k + 1) he
    simp only [one_mul] at hh
    have hx := hexp k
    omega
  let j := fun k ↦ RamifiedPullback.ramifiedQuotient l E L ι e k hideal (hexp k)
  have hj (k : ℕ) (a : Padic.coefficientExtensionIntegers l E) :
      j k (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (k + 1)) a) =
        Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal l L (RamifiedPullback.index e k + 1))
            (integralScalarIntegerInclusion l E L ι a) := rfl
  obtain ⟨source⟩ := RamifiedPullback.coefficients_exists l E L ι e he hideal hexp j hj Y
  obtain ⟨target⟩ := RamifiedPullback.coefficients_exists l E L ι e he hideal hexp j hj X
  have hS : source.completedMap = integralCompletedScalarMap l E L ι Y :=
    (integralCompletedScalarMap_existsUnique l E L ι Y).unique source.projection
      (by
        unfold integralCompletedScalarMap
        exact (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec)
  have hT : target.completedMap = integralCompletedScalarMap l E L ι X :=
    (integralCompletedScalarMap_existsUnique l E L ι X).unique target.projection
      (by
        unfold integralCompletedScalarMap
        exact (integralCompletedScalarMap_existsUnique l E L ι X).exists.choose_spec)
  have hcomp :=
    RamifiedPullback.finitePullbackComparison_exists l E L ι f e hmono j hj source target
  rw [hS, hT] at hcomp
  obtain ⟨d, hd, _⟩ := hcomp
  refine ⟨RamifiedPullback.index e n, hsame n, ?_⟩
  apply scalar_comparison_transport l E L ι f P n (RamifiedPullback.index e n)
    (RamifiedPullback.scalar.{u, u} (integralCompletedScalarMap l E L ι X))
    (RamifiedPullback.scalar.{u, u} (integralCompletedScalarMap l E L ι Y))
    (ramified_scalar_eq l E L ι X) (ramified_scalar_eq l E L ι Y)
    (RamifiedPullback.scalarWitness.{u, u} _).choose_spec.choose
    (RamifiedPullback.scalarWitness.{u, u} _).choose_spec.choose ((d n).app P)
  intro i V x
  have h := hd n P i V 1 1 1 x
  simp only [map_one, mul_one, RamifiedPullback.pullTensor, one_smul, id_eq,
    RamifiedPullback.tensor] at h
  unfold tensorSection
  convert h using 1 <;> rfl

private theorem pullback_transition_generator
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l F Y) ℤ) {n m : ℕ} (h : n ≤ m)
    (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)) :
    ((((integralOperationsPullbackTowerFunctor l F f).obj P).map (homOfLE h).op).f i).val.app
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
      (integralOperationsPullbackGenerator l F f m _ V
        (unrestrictedIntegralTensorSection l F Y m (P.X i) (op V) 1 x)) =
      integralOperationsPullbackGenerator l F f n _ V
        (unrestrictedIntegralTensorSection l F Y n (P.X i) (op V) 1 x) := by
  have ht := RamifiedPullback.pullTensor_transition l F f n m h P i V 1 1 x
  simp only [RamifiedPullback.transition, RamifiedPullback.pullTensor, map_one,
    one_smul, id_eq] at ht
  convert ht using 1 <;> rfl

private theorem scalar_level_hom_ext {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (Q : CochainComplex (integralTowerModules l L Y) ℤ) (n : ℕ)
    (a b : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackLevel l E f n).obj P) ⟶
      (integralOperationsPullbackLevel l L f n).obj Q)
    (hab : ∀ (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
      (a.f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f n _ V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
      (b.f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f n _ V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x)))) : a = b := by
  let c := sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let q := c.map (integralScalarQuotientSheafMap l E L ι X n)
  have hq : integralOperationsProjection l E X n ≫ q =
      c.map (integralCompletedScalarMap l E L ι X) ≫
        integralOperationsProjection l L X n := by
    have hp : integralCompletedScalarMap l E L ι X ≫
        completedIntegralCommRingProjectionUnrestricted l L X n =
          integralScalarRho l E L ι X n := by
      unfold integralCompletedScalarMap
      exact (integralCompletedScalarMap_existsUnique l E L ι X).exists.choose_spec n
    have hc := congrArg c.map hp.symm
    simpa only [Functor.map_comp, integralScalarRho, integralOperationsProjection, q] using hc
  apply HomologicalComplex.hom_ext
  intro i
  exact scalar_pullback_hom_ext l E L ι f n n q hq (P.X i)
    (((integralOperationsLevelPullback l L f n).mapHomologicalComplex (.up ℤ)).obj
      ((unrestrictedIntegralFiniteComplex l L Y n).obj Q) |>.X i)
    (a.f i) (b.f i) (hab i)

/-- The finite scalar pullback square has a diagonal at sufficiently late levels.
Source: Stacks, sites-cohomology.tex, Tag 07A4; completed constant sheaf reduction,
and the uniformizer-filtration argument in the parent node.
(blueprint: lem-pur-integral-scalar-pullback-transition-factorization).

Proof: let e be the positive ramification index, so the image of the E-uniformizer
is a unit times the e-th power of the L-uniformizer. The completed coefficient
quotient at E-level n, extended to L, is the quotient at L-exponent e(n+1).
Balanced tensor associativity and the pullback adjunction identify the source
level C_n with the target level D_(e(n+1)-1). Use the quotient map from D_m to
that level, for m = e(n+1)-1, followed by the inverse identification, to obtain b.
The generator equation for alpha makes b followed by alpha_n the target
transition. Applied at level m, the same equation and the compatibility of the
quotient identifications with transitions make alpha_m followed by b the source
transition. All these maps commute with the differential: their coefficient
maps are independent of the cochain degree, and their section formulas commute
with P's differential. Each equality holds on the nested tensor and pullback
generators, which locally generate by sheafification and the pullback adjunction.
The identities therefore hold as maps of complexes. This uses ordinary tensors
only and needs no flatness or completeness assumption on P. For e=1 one may take
m=n and the inverse finite-level comparison. Zero complexes and the empty site
have their unique maps and obey the same formulas. No cone or homotopy is asserted.
-/
theorem integralScalarPullbackTransitionFactorization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (α : ((integralOperationsPullbackTowerFunctor l E f).obj P) ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOperationsPullbackTowerFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P))
    (hα :
      ∀ (n : ℕ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app (op n)).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel.{u, u} l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator.{u, u} l E f n
              (((unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator.{u, u} l L f n
          (((unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection.{u, u} l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x))) :
    let C := ((integralOperationsPullbackTowerFunctor l E f).obj P) ⋙
      (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
    let D := (integralOperationsPullbackTowerFunctor l L f).obj
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (b : D.obj (op m) ⟶ C.obj (op n)),
      α.app (op m) ≫ b = C.map (homOfLE h).op ∧
        b ≫ α.app (op n) = D.map (homOfLE h).op := by
  dsimp only
  intro n
  obtain ⟨m, h, d, hd⟩ := ramified_level l E L ι f P n
  refine ⟨m, h, d.inv, ?_, ?_⟩
  · apply (cancel_mono d.hom).mp
    erw [Category.assoc, d.inv_hom_id, Category.comp_id]
    apply scalar_level_hom_ext l E L ι f P
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) m
    intro i V x
    change ((α.app (op m)).f i).val.app _
        (integralOrdinaryTensorSection l E L ι X _ _ 1
          (integralOperationsPullbackGenerator l E f m _ V
            (unrestrictedIntegralTensorSection l E Y m (P.X i) (op V) 1 x))) =
      (d.hom.f i).val.app _
        (((integralOrdinaryScalar l E L ι X).map
          ((((integralOperationsPullbackTowerFunctor l E f).obj P).map
            (homOfLE h).op).f i)).val.app _
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f m _ V
              (unrestrictedIntegralTensorSection l E Y m (P.X i) (op V) 1 x))))
    erw [hα, scalar_map_tensor, pullback_transition_generator, hd]
    dsimp only [unrestrictedIntegralFiniteComplex, Functor.mapHomologicalComplex_obj_X]
  · apply (cancel_epi d.hom).mp
    rw [← Category.assoc, d.hom_inv_id, Category.id_comp]
    apply scalar_level_hom_ext l E L ι f P
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) n
    intro i V x
    change ((α.app (op n)).f i).val.app _
        (integralOrdinaryTensorSection l E L ι X _ _ 1
          (integralOperationsPullbackGenerator l E f n _ V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
      ((((integralOperationsPullbackTowerFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)).map
          (homOfLE h).op).f i).val.app _
        ((d.hom.f i).val.app _
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f n _ V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))))
    erw [hα, hd, pullback_transition_generator]
    dsimp only [unrestrictedIntegralFiniteComplex, Functor.mapHomologicalComplex_obj_X]

end WeilConjectures
