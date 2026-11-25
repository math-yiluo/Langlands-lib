/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition

/-! # Signed braiding under normalized reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 2 and 4;
Stacks 07A4, 08J9, 099B and 099M (blueprint: lem-pod-reindexing-ordinary-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local instance 1000001] cachedCompose
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] coefficientTotalTensor
  coefficientTensorGenerator
  SheafOfModules.monoidalCategory

namespace PodReindexingCoherence

private theorem ordinary_braiding_base {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (P L : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L) :
    let F := podReindexingDerivedFunctor l E g s
    let Q := podReindexingQ l E Y s
    F.map ((pullbackTensorBraiding (ProEt.topology Y)
      (podReindexingRing l E Y s) SY TY).app (Q.obj P, Q.obj L)).hom ≫
        c.tensor.hom.app (Q.obj L, Q.obj P) =
      c.tensor.hom.app (Q.obj P, Q.obj L) ≫
        ((pullbackTensorBraiding (ProEt.topology X)
          (podReindexingRing l E X s) SX TX).app (F.obj (Q.obj P), F.obj (Q.obj L))).hom := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let F := podReindexingDerivedFunctor l E g s
  let R := podReindexingComplexFunctor l E g s
  let QY := podReindexingQ l E Y s
  let QX := podReindexingQ l E X s
  have bnX {P Q P' Q' : podReindexingDerived l E X s} (f : P ⟶ P') (h : Q ⟶ Q') :
      SX.tensor.map (Prod.mkHom f h) ≫ ((pullbackTensorBraiding (ProEt.topology X)
        (podReindexingRing l E X s) SX TX).app (P', Q')).hom =
        ((pullbackTensorBraiding (ProEt.topology X)
          (podReindexingRing l E X s) SX TX).app (P, Q)).hom ≫
            SX.tensor.map (Prod.mkHom h f) := by
    exact (pullbackTensorBraiding (ProEt.topology X)
      (podReindexingRing l E X s) SX TX).hom.naturality (Prod.mkHom f h)
  obtain ⟨hRP, hRL, hρ⟩ := c.tensor_model P L hP hL
  obtain ⟨_, _, hρ'⟩ := c.tensor_model L P hL hP
  let t := pullbackTensorSignedTotal (ProEt.topology Y) (podReindexingRing l E Y s) P L
  let tX := pullbackTensorSignedTotal (ProEt.topology X) (podReindexingRing l E X s)
    (R.obj P) (R.obj L)
  have ht : ∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k)
      (U : Y.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
      (t.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y) (podReindexingRing l E Y s)
          P L p q k h U x y) =
      (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
        (podReindexingRing l E Y s) L P q p k h' U y x := by
    intro p q k h h' U x y
    exact (pullbackTensorSignedTotal_existsUnique (ProEt.topology Y)
      (podReindexingRing l E Y s) P L).exists.choose_spec p q k h U x y
  have htX : ∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k)
      (U : X.ProEtᵒᵖ) (x : ((R.obj P).X p).val.obj U) (y : ((R.obj L).X q).val.obj U),
      (tX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) (podReindexingRing l E X s)
          (R.obj P) (R.obj L) p q k h U x y) =
      (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) (R.obj L) (R.obj P) q p k h' U y x := by
    intro p q k h h' U x y
    exact (pullbackTensorSignedTotal_existsUnique (ProEt.topology X)
      (podReindexingRing l E X s) (R.obj P) (R.obj L)).exists.choose_spec p q k h U x y
  have hchain := symmetry_chain l E g s SX SY TX TY c P L t tX ht htX
  apply symmetry_models F SY.tensor SX.tensor c.tensor
    (fun P Q ↦ (pullbackTensorBraiding (ProEt.topology Y)
      (podReindexingRing l E Y s) SY TY).app (P, Q))
    (fun P Q ↦ (pullbackTensorBraiding (ProEt.topology X)
      (podReindexingRing l E X s) SX TX).app (P, Q)) bnX
    (TY.iso _ _ SY P L hP hL) (TY.iso _ _ SY L P hL hP)
    (TX.iso _ _ SX (R.obj P) (R.obj L) hRP hRL)
    (TX.iso _ _ SX (R.obj L) (R.obj P) hRL hRP)
    ((podReindexingDerivedFactors l E g s).app P)
    ((podReindexingDerivedFactors l E g s).app L)
    (((podReindexingDerivedFactors l E g s).app _) ≪≫ QX.mapIso (c.tensorChain P L))
    (((podReindexingDerivedFactors l E g s).app _) ≪≫ QX.mapIso (c.tensorChain L P))
    (QY.mapIso t) (QX.mapIso tX)
  · dsimp only [CoefficientTensorModels.iso, Iso.app_hom, Iso.trans_hom,
      Functor.mapIso_hom, F, QX, QY, R, Functor.comp_obj, Functor.prod_obj,
      coefficientKFlatInclusion, ObjectProperty.ι_obj, total] at hρ ⊢
    exact hρ.trans (Category.assoc _ _ _).symm
  · dsimp only [CoefficientTensorModels.iso, Iso.app_hom, Iso.trans_hom,
      Functor.mapIso_hom, F, QX, QY, R, Functor.comp_obj, Functor.prod_obj,
      coefficientKFlatInclusion, ObjectProperty.ι_obj, total] at hρ' ⊢
    exact hρ'.trans (Category.assoc _ _ _).symm
  · exact ((pullbackTensorBraiding_existsUnique (ProEt.topology Y)
      (podReindexingRing l E Y s) SY TY).exists.choose_spec P L hP hL).symm
  · exact ((pullbackTensorBraiding_existsUnique (ProEt.topology X)
      (podReindexingRing l E X s) SX TX).exists.choose_spec
        (R.obj P) (R.obj L) hRP hRL).symm
  · have hn := (podReindexingDerivedFactors l E g s).hom.naturality t.hom
    change F.map (QY.map t.hom) ≫
        ((podReindexingDerivedFactors l E g s).hom.app _ ≫
          QX.map (c.tensorChain L P).hom) =
      ((podReindexingDerivedFactors l E g s).hom.app _ ≫
        QX.map (c.tensorChain P L).hom) ≫ QX.map tX.hom
    change F.map (QY.map t.hom) ≫
        (podReindexingDerivedFactors l E g s).hom.app _ =
      (podReindexingDerivedFactors l E g s).hom.app _ ≫ QX.map (R.map t.hom) at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    exact congrArg ((podReindexingDerivedFactors l E g s).hom.app _ ≫ ·)
      ((QX.map_comp _ _).symm.trans
        ((congrArg QX.map hchain).trans (QX.map_comp _ _)))

/-- The specified signed braiding commutes with the normalized tensor comparison.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08J9
(blueprint: lem-pod-reindexing-ordinary-braiding).

Proof: compute both paths on simultaneous K-flat representatives. The chain tensor
comparison sends x tensor y to Fx tensor Fy and both braidings exchange the factors
with the same sign. Tensor model compatibility descends this chain equality. Choose
K-flat resolutions of both arbitrary inputs, then use naturality and cancel their
localization isomorphisms. No boundedness or constructibility is needed. -/
theorem podReindexingOrdinaryBraiding {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (M N : podReindexingDerived l E Y s) :
    let F := podReindexingDerivedFunctor l E g s
    let βY := pullbackTensorBraiding (ProEt.topology Y) (podReindexingRing l E Y s) SY TY
    let βX := pullbackTensorBraiding (ProEt.topology X) (podReindexingRing l E X s) SX TX
    F.map (βY.app (M, N)).hom ≫ c.tensor.hom.app (N, M) =
      c.tensor.hom.app (M, N) ≫ (βX.app (F.obj M, F.obj N)).hom := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let F := podReindexingDerivedFunctor l E g s
  let QY := podReindexingQ l E Y s
  let βY := pullbackTensorBraiding (ProEt.topology Y) (podReindexingRing l E Y s) SY TY
  let βX := pullbackTensorBraiding (ProEt.topology X) (podReindexingRing l E X s) SX TX
  have bnX {P Q P' Q' : podReindexingDerived l E X s} (f : P ⟶ P') (h : Q ⟶ Q') :
      SX.tensor.map (Prod.mkHom f h) ≫ (βX.app (P', Q')).hom =
        (βX.app (P, Q)).hom ≫ SX.tensor.map (Prod.mkHom h f) :=
    βX.hom.naturality (Prod.mkHom f h)
  have bnY {P Q P' Q' : podReindexingDerived l E Y s} (f : P ⟶ P') (h : Q ⟶ Q') :
      SY.tensor.map (Prod.mkHom f h) ≫ (βY.app (P', Q')).hom =
        (βY.app (P, Q)).hom ≫ SY.tensor.map (Prod.mkHom h f) :=
    βY.hom.naturality (Prod.mkHom f h)
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (QY.objPreimage M)
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (QY.objPreimage N)
  have : IsIso (QY.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have : IsIso (QY.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  let eM : QY.obj P ≅ M := asIso (QY.map p) ≪≫ QY.objObjPreimageIso M
  let eN : QY.obj L ≅ N := asIso (QY.map q) ≪≫ QY.objObjPreimageIso N
  exact symmetry_iso F SY.tensor SX.tensor c.tensor
    (fun P Q ↦ βY.app (P, Q)) (fun P Q ↦ βX.app (P, Q)) bnY bnX eM eN
    (ordinary_braiding_base l E g s SX SY TX TY c P L hP hL)

end PodReindexingCoherence

end WeilConjectures
