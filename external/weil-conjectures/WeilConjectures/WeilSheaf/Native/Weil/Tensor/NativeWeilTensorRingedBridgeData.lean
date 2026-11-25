/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData

/-! # Data for the underived native forgetful bridge

The bridge records the underived square and retains coherence for the specified
ordinary Hom comparison. Its existence proof uses the canonical section model.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An additive ringed presentation of forgetting the actual Frobenius structure.
The square, Hom comparison and coefficient unit are comparisons of underived modules.
The last field is the flat-term resolution condition required by ringed tensor descent.

Source: native tensor geometry, steps 1 and 2; Stacks 00W0, 00YV, 06YS, 06YU.
(blueprint: def-sf-native-weil-tensor-ringed-bridge). -/
structure NativeWeilTensorRingedBridge
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] where
  /-- The action site. -/
  C : Type (u + 1)
  [categoryC : SmallCategory C]
  J : GrothendieckTopology C
  R : Sheaf J CommRingCat.{u + 1}
  /-- The ordinary small pro-etale site. -/
  A : Type (u + 1)
  [categoryA : SmallCategory A]
  K : GrothendieckTopology A
  Q : Sheaf K CommRingCat.{u + 1}
  /-- Equivalences of actual module categories, before localization. -/
  native : ProEtaleWeilSheaf k₀ l X ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R
  ordinary : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≌
    RingedTensorModules.{u + 1, u + 1, u + 1} K Q
  [native_additive : native.functor.Additive]
  [ordinary_additive : ordinary.functor.Additive]
  /-- Restriction from the action site. -/
  forget : RingedTensorModules.{u + 1, u + 1, u + 1} J R ⥤
    RingedTensorModules.{u + 1, u + 1, u + 1} K Q
  [forget_additive : forget.Additive]
  [forget_limits : PreservesFiniteLimits forget]
  [forget_colimits : PreservesFiniteColimits forget]
  [forget_products : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) forget]
  [forget_coproducts : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) forget]
  [forget_injectives : forget.PreservesKInjectiveComplexes]
  /-- The functor in this square is exactly native underived forgetting. -/
  square : native.functor ⋙ forget ≅
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙ ordinary.functor
  /-- Restriction has the normalized sheaf tensor, unit, Hom and evaluation maps. -/
  underived : RingedForgetTensorTransposition.Underived J R K Q forget
  /-- The native equivalence preserves the underived internal Hom. -/
  nativeHom : Functor.uncurry.obj (ihomBifunctor k₀ l X) ⋙ native.functor ≅
    (native.functor.op.prod native.functor) ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))
  /-- The ordinary equivalence preserves the underived internal Hom. -/
  ordinaryHom : Functor.uncurry.obj
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⋙
        ordinary.functor ≅
    (ordinary.functor.op.prod ordinary.functor) ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := Q))
  /-- The specified ordinary Hom comparison comes from the coherent actual tensor.
  A bare natural Hom isomorphism does not supply this normalization. -/
  ordinary_coherence : OrdinaryRingedTensorCoherence l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber K Q ordinary ordinaryHom
  /-- These are the same Hom comparison across the square, including evaluation. -/
  hom_square (P I : ProEtaleWeilSheaf k₀ l X) :
    forget.map (nativeHom.hom.app (op P, I)) ≫
        underived.hom.hom.app (op (native.functor.obj P), native.functor.obj I) ≫
        SheafOfModules.homObjMap (R := Q) (square.inv.app P) (square.hom.app I) ≫
        ordinaryHom.inv.app (op P.carrier, I.carrier) =
      square.hom.app (((ihomBifunctor k₀ l X).obj (op P)).obj I)
  /-- The native coefficient module is the genuine ringed tensor unit. -/
  nativeUnit : native.functor.obj (adicConstant k₀ l X) ≅
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  /-- Restriction takes flat-term K-flat complexes to flat-term K-flat complexes. -/
  preserves_flat_models (P : CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hterms : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := Q)
      ((forget.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := Q) (forget.obj (P.X p))

attribute [instance] NativeWeilTensorRingedBridge.categoryC
  NativeWeilTensorRingedBridge.categoryA NativeWeilTensorRingedBridge.native_additive
  NativeWeilTensorRingedBridge.ordinary_additive NativeWeilTensorRingedBridge.forget_additive
  NativeWeilTensorRingedBridge.forget_limits NativeWeilTensorRingedBridge.forget_colimits
  NativeWeilTensorRingedBridge.forget_products NativeWeilTensorRingedBridge.forget_coproducts
  NativeWeilTensorRingedBridge.forget_injectives

-- Keep this projection with the record: compiling the bridge must check that its
-- retained coherence supplies actual ordinary symmetry, before any consumer uses it.
-- The concrete sheaf tensor instances require additional elaboration fuel.
private theorem bridge_ordinary_tensor_symmetry
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (b : NativeWeilTensorRingedBridge k₀ l X)
    (d : OrdinaryRingedTensorUnderivedData l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber b.K b.Q b.ordinary b.ordinaryHom)
    (P Q : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    ∃ s : ((ordinaryTensorBifunctor l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj Q).obj P ⟶
        ((ordinaryTensorBifunctor l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj P).obj Q,
      (letI := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
       letI := SheafOfModules.monoidalCategory b.Q
       letI := SheafOfModules.symmetricCategory b.Q
       b.ordinary.functor.map s ≫ (d.underived P Q).hom =
         (d.underived Q P).hom ≫
           (β_ (b.ordinary.functor.obj P) (b.ordinary.functor.obj Q)).hom) ∧
      Mod.tensorπ P Q ≫ s.hom = (β_ P.X Q.X).hom ≫ Mod.tensorπ Q P := by
  exact b.ordinary_coherence.1 d P Q

end AlgebraicGeometry.ProEtaleWeilSheaf
