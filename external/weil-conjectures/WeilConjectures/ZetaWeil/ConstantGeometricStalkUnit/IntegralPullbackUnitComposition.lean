/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.ConstantGeometricStalkUnit.IntegralConstantUnitReduction
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.FinitePullbackUnitComposition
import all WeilConjectures.ZetaWeil.FiniteRegularCoefficientComparisons
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteFiniteReductionDetection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Composition of normalized integral coefficient units

Source: the constant comparison preceding Step 1 of purity and trace equivariance;
Stacks 099N(5) and 0D6D, with the normalized strict coefficient units.
(blueprint: lem-pur-integral-pullback-unit-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantGeometricStalkUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def reductionNat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ) :=
  let F := constructibleIntegralPullback l E f
  let RX := integralSystemReduction l E X
  let RY := integralSystemReduction l E Y
  let ex := finiteSystemDerivedEvaluation (integralSystemRings l E)
    (integralSystemTransition l E) X n
  let ey := finiteSystemDerivedEvaluation (integralSystemRings l E)
    (integralSystemTransition l E) Y n
  let U := finiteSystemDerivedPullback (integralSystemRings l E)
    (integralSystemTransition l E) f
  let H := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  isoWhiskerLeft F (integralSystemReductionEvaluation l E X n).symm ≪≫
    (Functor.associator F RX ex).symm ≪≫
    isoWhiskerRight ((integralPullbackSystemComparison l E).choose f) ex ≪≫
    Functor.associator RY U ex ≪≫
    isoWhiskerLeft RY (finiteSystemDerivedPullbackEvaluation
      (integralSystemRings l E) (integralSystemTransition l E) f n) ≪≫
    (Functor.associator RY ey H).symm ≪≫
    isoWhiskerRight (integralSystemReductionEvaluation l E Y n) H

private theorem reductionNat_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :
    (reductionNat l E f n).app K = integralPullbackReductionIso l E f K P e n := by
  apply Iso.ext
  apply (cancel_epi ((integralSystemReductionEvaluation l E X n).hom.app
    ((constructibleIntegralPullback l E f).obj K))).1
  have h := (integralPullbackSystemComparison l E).choose_spec.1 f K P e n
  simpa only [reductionNat, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.hom_inv_id_app_assoc, integralPullbackReductionIso] using h

private theorem reduction_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K L : sfIntegralConstructibleCategory l E Y} (a : K ⟶ L)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (d : DerivedCategory.Q.obj Q.obj ≅ L.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).map
        ((constructibleIntegralPullback l E f).map a).hom ≫
      (integralPullbackReductionIso l E f L Q d n).hom =
    (integralPullbackReductionIso l E f K P e n).hom ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((scalarReductionDerivedExtension l E Y n).map a.hom) := by
  rw [← reductionNat_app l E f K P e n, ← reductionNat_app l E f L Q d n]
  exact (reductionNat l E f n).hom.naturality a

private theorem finiteRingUnit_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (integralFiniteCanonicalPullbackComposition l E f g n).hom.app
        (finiteConstantCoefficientObject l E Z n) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
          (finiteRingUnit l E g n).hom ≫ (finiteRingUnit l E f n).hom =
        (finiteRingUnit l E (f ≫ g) n).hom := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have h := finiteUnit_composition l E f g n
  apply (cancel_epi ((openSquareDerivedPullbackModel
    (Padic.coefficientExtensionRing l E (n + 1)) (f ≫ g)).inv.app
      (finiteConstantCoefficientObject l E Z n))).1
  simp only [finiteRingUnit, Iso.trans_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  have hn := (openSquareDerivedPullbackModel
    (Padic.coefficientExtensionRing l E (n + 1)) f).hom.naturality
      (finiteUnit l E g n).hom
  rw [reassoc_of% hn]
  simpa only [finiteCanonicalPullbackComposition, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc] using h

private theorem constant_reduction_ext
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) {P : DerivedCategory (scalarReductionSource l E X)}
    (e : P ≅ integralConstantCoefficientObject l E X)
    (a b : P ⟶ integralConstantCoefficientObject l E X)
    (h : ∀ n, (scalarReductionDerivedExtension l E X n).map a =
      (scalarReductionDerivedExtension l E X n).map b) : a = b := by
  apply derivedComplete_finiteReduction_ext l E X
    (integralConstantCoefficient_constructible l E X D hl).2.1.1 ?_ a b h
  intro n
  let R := scalarReductionRestriction l E X n
  let := scalarReductionRestrictionLimits l E X n
  let := scalarReductionRestrictionColimits l E X n
  let er : (sfDerivedReductionRestricted l E X n).obj
      (integralConstantCoefficientObject l E X) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (R.obj (SheafOfModules.unit (integralCoefficientSheaf l E X n))) :=
    (scalarReductionDerivedRestriction l E X n).mapIso
      (integralConstantReduction l E D hl X n) ≪≫
        (R.mapDerivedCategorySingleFunctor 0).app _
  let t := @DerivedCategory.TStructure.t (scalarReductionSource l E X) _ _ _
  let h0 : (integralConstantCoefficientObject l E X).IsLE 0 := by
    unfold integralConstantCoefficientObject
    infer_instance
  have hp : t.IsLE P 0 := t.isLE_of_iso e.symm 0
  let := hp
  have hp' := t.isLE_shift P 0 1 (-1) (by decide)
  have hq : t.IsGE ((sfDerivedReductionRestricted l E X n).obj
      (integralConstantCoefficientObject l E X)) 0 := by
    exact t.isGE_of_iso er.symm 0
  let : Subsingleton (P⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E X n).obj
      (integralConstantCoefficientObject l E X)) :=
    ⟨fun a b ↦ (t.zero_of_isLE_of_isGE a (-1) 0 (by decide) hp' hq).trans
      (t.zero_of_isLE_of_isGE b (-1) 0 (by decide) hp' hq).symm⟩
  infer_instance

/-- The normalized integral unit respects one composition of scheme morphisms.

Source: the constant comparison preceding Step 1 of purity and trace equivariance;
Stacks 099N(5), 0D6D; the constant-ring composition equation.
(blueprint: lem-pur-integral-pullback-unit-composition).

Proof: use the canonical regular K-flat representative on Y and Z. Reducing each
integral unit gives finite multiplication by integralUnit_reduction. The
projection-normalized integral compositor has the published finite compositor as its
reduction. Naturality of its single-arrow reduction comparison moves the unit for g
through the pullback for f. Paste these equations, then use finiteUnit_composition,
transported through the unit-preserving finite coordinate isomorphisms.

To detect the resulting integral equality, its source is isomorphic to the completed
regular sheaf in degree zero via the already constructed unit for f followed by g.
The target is derived complete. Its restricted finite reductions are also sheaves in
degree zero: use the canonical regular reduction isomorphism and exact scalar
restriction. Every Hom from the source shifted by one to these reductions is zero by
the standard t-structure. The proved finite-shifted-Hom detection theorem therefore
applies. No joint faithfulness assertion for arbitrary derived systems is used.
Identity maps, empty schemes and the first positive quotient require no exception. -/
theorem integralUnit_composition
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] :
    let KX := constantWeilIntegralObject l E D hl X
    let KY := constantWeilIntegralObject l E D hl Y
    let KZ := constantWeilIntegralObject l E D hl Z
    let uf : (constructibleIntegralPullback l E f).obj KY ≅ KX :=
      ObjectProperty.isoMk _ (integralUnit l E f)
    let ug : (constructibleIntegralPullback l E g).obj KZ ≅ KY :=
      ObjectProperty.isoMk _ (integralUnit l E g)
    let ufg : (constructibleIntegralPullback l E (f ≫ g)).obj KZ ≅ KX :=
      ObjectProperty.isoMk _ (integralUnit l E (f ≫ g))
    (pullbackTensorIntegralComposition l E g f).hom.app KZ ≫
      (constructibleIntegralPullback l E f).map ug.hom ≫ uf.hom = ufg.hom := by
  dsimp only
  let KX := constantWeilIntegralObject l E D hl X
  let KY := constantWeilIntegralObject l E D hl Y
  let KZ := constantWeilIntegralObject l E D hl Z
  let uf : (constructibleIntegralPullback l E f).obj KY ≅ KX :=
    ObjectProperty.isoMk _ (integralUnit l E f)
  let ug : (constructibleIntegralPullback l E g).obj KZ ≅ KY :=
    ObjectProperty.isoMk _ (integralUnit l E g)
  let ufg : (constructibleIntegralPullback l E (f ≫ g)).obj KZ ≅ KX :=
    ObjectProperty.isoMk _ (integralUnit l E (f ≫ g))
  change (pullbackTensorIntegralComposition l E g f).hom.app KZ ≫
    (constructibleIntegralPullback l E f).map ug.hom ≫ uf.hom = ufg.hom
  apply (sfIntegralConstructible l E X).ι.map_injective
  apply constant_reduction_ext l E D hl X (integralUnit l E (f ≫ g))
  intro n
  let PZ := constantWeilIntegralGood l E Z
  let PY := constantWeilIntegralGood l E Y
  have hf := integralUnit_reduction l E D hl f n
  have hg := integralUnit_reduction l E D hl g n
  have hfg := integralUnit_reduction l E D hl (f ≫ g) n
  have hn := reduction_naturality l E f ug.hom PY (integralUnit l E g).symm
    PY (Iso.refl _) n
  have hc := (integralPullbackComposition l E).choose_spec.1 f g KZ PZ
    (Iso.refl _) PY (integralUnit l E g).symm n
  change (scalarReductionDerivedExtension l E X n).map
      ((pullbackTensorIntegralComposition l E g f).hom.app KZ).hom ≫ _ = _ at hc
  apply (cancel_mono (integralConstantReduction l E D hl X n).hom).1
  simp only [Functor.map_comp, Category.assoc]
  change (scalarReductionDerivedExtension l E X n).map
      ((pullbackTensorIntegralComposition l E g f).hom.app KZ).hom ≫
    (scalarReductionDerivedExtension l E X n).map
      ((constructibleIntegralPullback l E f).map ug.hom).hom ≫
    (scalarReductionDerivedExtension l E X n).map (integralUnit l E f).hom ≫
    (integralConstantReduction l E D hl X n).hom =
    (scalarReductionDerivedExtension l E X n).map (integralUnit l E (f ≫ g)).hom ≫
      (integralConstantReduction l E D hl X n).hom
  rw [hf, hfg]
  rw [reassoc_of% hn]
  have hug : ug.hom.hom = (integralUnit l E g).hom := rfl
  rw [hug]
  have hg' := congrArg (proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f).map hg
  simp only [Functor.map_comp] at hg'
  rw [reassoc_of% hg']
  rw [reassoc_of% hc]
  have ha := (integralFiniteCanonicalPullbackComposition l E f g n).hom.naturality
    (integralConstantReduction l E D hl Z n).hom
  change (proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) (f ≫ g)).map
        (integralConstantReduction l E D hl Z n).hom ≫
      (integralFiniteCanonicalPullbackComposition l E f g n).hom.app
        (finiteConstantCoefficientObject l E Z n) =
    (integralFiniteCanonicalPullbackComposition l E f g n).hom.app
        ((scalarReductionDerivedExtension l E Z n).obj KZ.obj) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((proEtaleConstantRingDerivedPullback
            (Padic.coefficientExtensionRing l E (n + 1)) g).map
              (integralConstantReduction l E D hl Z n).hom) at ha
  rw [← reassoc_of% ha]
  rw [finiteRingUnit_composition l E f g n]

end WeilConjectures.ConstantGeometricStalkUnit
