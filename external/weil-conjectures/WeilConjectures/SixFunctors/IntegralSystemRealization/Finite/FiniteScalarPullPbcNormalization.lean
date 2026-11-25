/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteScalarPullOrdinary
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarOrdinaryReductionIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarPullComplexPresentation
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullCoefficientComplexNormalization

/-! # Pbc scalar square on ordinary complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  WeilConjectures.PurCompactSupport.scalarPull
  WeilConjectures.PurCompactSupport.scalarPullComplex
  WeilConjectures.scalarReductionExtension AlgebraicGeometry.Scheme.pbcComplexCounit
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.scalarReductionTargetDerived WeilConjectures.scalarReductionSourceDerived
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem scalar_normalization_reverse
    {C : Type*} [Category C] {A B D E F G : C}
    (q : A ≅ B) (s : F ≅ G) (a : A ⟶ D) (b : D ⟶ G)
    (c : B ⟶ E) (d : E ⟶ F)
    (h : q.inv ≫ a ≫ b = c ≫ d ≫ s.hom) :
    q.hom ≫ c ≫ d = a ≫ b ≫ s.inv := by
  apply (cancel_epi q.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id, Category.comp_id]

private theorem scalar_pasting
    {C : Type*} [Category C] {A B D E F G H I J K : C}
    (q : A ⟶ B) (c : B ⟶ D) (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ G)
    (a : A ⟶ H) (b : H ⟶ I) (s : I ⟶ E)
    (t : I ⟶ J) (v : J ⟶ K) (w : K ⟶ G)
    (h : q ≫ c ≫ d = a ≫ b ≫ s) (h' : s ≫ e ≫ f = t ≫ v ≫ w) :
    q ≫ c ≫ d ≫ e ≫ f = a ≫ b ≫ t ≫ v ≫ w := by
  rw [reassoc_of% h, h']

/-- The pbc scalar comparison is compatible with the ordinary finite presentations.
Source: Stacks Tags 07A6, 06YY and 0D6E
(blueprint: lem-sf-finite-scalar-pull-pbc-normalization).
Proof: reverse scalarPull_complex_normalization by cancelling its source and target
isomorphisms. Compose that equation with the geometric pullback of the ordinary
scalar presentation and the ordinary geometric presentation. The image under Q of
finiteScalarPullComplexPresentation identifies these final three complex maps.
The argument applies to every cochain complex, without K-flatness. -/
theorem finiteScalarPullPbcNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := scalarReductionExtensionAdditive.{u, u} l E X n
    let := scalarReductionExtensionAdditive.{u, u} l E Y n
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
    let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
    let F := integralOrdinaryPull l E f
    let T := proEtaleRingModulePullback f (S.ring Y) (S.ring X) (S.pull f)
    let TD := PurCompactSupport.pull S f
    let CY := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P
    let BY := ((pbcExtend (a.map Y)).mapHomologicalComplex (.up ℤ)).obj P
    let αYc := (NatTrans.mapHomologicalComplex
      (finiteScalarOrdinaryReductionIso l E Y n).hom (.up ℤ)).app P
    let αXc := (NatTrans.mapHomologicalComplex
      (finiteScalarOrdinaryReductionIso l E X n).hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
    (PurCompactSupport.scalarPull a f).hom.app (DerivedCategory.Q.obj P) ≫
      TD.map (pbcComplexCounit (a.map Y) P) ≫ T.mapDerivedCategoryFactors.hom.app BY ≫
      DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map αYc) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (PurCompactSupport.finitePullbackIso l E n f)
          (.up ℤ)).hom.app CY) =
    (pbcDerivedExtend (a.map X)).map (F.mapDerivedCategoryFactors.hom.app P) ≫
      pbcComplexCounit (a.map X) ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map αXc ≫
      DerivedCategory.Q.map (ordinaryFiniteScalarPullComplex l E f n P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
          (.up ℤ)).hom.app CY) := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := scalarReductionExtensionAdditive.{u, u} l E X n
  let := scalarReductionExtensionAdditive.{u, u} l E Y n
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
  let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  let F := integralOrdinaryPull l E f
  let T := proEtaleRingModulePullback f (S.ring Y) (S.ring X) (S.pull f)
  let TD := PurCompactSupport.pull S f
  let CY := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P
  let BY := ((pbcExtend (a.map Y)).mapHomologicalComplex (.up ℤ)).obj P
  let αYc := (NatTrans.mapHomologicalComplex
    (finiteScalarOrdinaryReductionIso l E Y n).hom (.up ℤ)).app P
  let αXc := (NatTrans.mapHomologicalComplex
    (finiteScalarOrdinaryReductionIso l E X n).hom (.up ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let lamc := (NatIso.mapHomologicalComplex
    (PurCompactSupport.finitePullbackIso l E n f) (.up ℤ)).hom.app CY
  let q := (PurCompactSupport.scalarPull a f).app (DerivedCategory.Q.obj P)
  let qc := (PurCompactSupport.scalarPullComplex a f).inv.app P
  let cx := pbcComplexCounit (a.map X) ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let cy := pbcComplexCounit (a.map Y) P
  let fx := F.mapDerivedCategoryFactors.hom.app P
  let fy := T.mapDerivedCategoryFactors.hom.app BY
  let ν := ordinaryFiniteScalarPullComplex l E f n P
  let τ := (NatIso.mapHomologicalComplex
    (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app CY
  have hs := PurCompactSupport.scalarPull_complex_normalization a f P
  have hscalar : q.hom ≫ TD.map cy ≫ fy =
      (pbcDerivedExtend (a.map X)).map fx ≫ cx ≫ DerivedCategory.Q.map qc := by
    exact scalar_normalization_reverse q
      (DerivedCategory.Q.mapIso ((PurCompactSupport.scalarPullComplex a f).app P))
      ((pbcDerivedExtend (a.map X)).map fx) cx (TD.map cy) fy hs
  have ho : qc ≫ (T.mapHomologicalComplex (.up ℤ)).map αYc ≫ lamc = αXc ≫ ν ≫ τ :=
    finiteScalarPullComplexPresentation l E f n P
  have ho' := congrArg (fun k ↦ DerivedCategory.Q.map k) ho
  simp only [DerivedCategory.Q.map_comp] at ho'
  change q.hom ≫ TD.map cy ≫ fy ≫
      DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map αYc) ≫
      DerivedCategory.Q.map lamc =
    (pbcDerivedExtend (a.map X)).map fx ≫ cx ≫ DerivedCategory.Q.map αXc ≫
      DerivedCategory.Q.map ν ≫ DerivedCategory.Q.map τ
  exact scalar_pasting _ _ _ _ _ _ _ _ _ _ _ hscalar ho'

end WeilConjectures.IntegralSystemRealization
