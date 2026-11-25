/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Associativity on simultaneous resolving representatives

Source: Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r wb d vd s wa b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  CategoryTheory.MonoidalCategory.leftAssocTensor
  CategoryTheory.MonoidalCategory.rightAssocTensor

-- Check the categorical pasting once with abstract functors, before specializing to sheaves.
private theorem coefficient_tensor_associativity_paste
    {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    {V : Type c} [Category.{v} V] {W : Type d} [Category.{vd} W]
    (q : V ⥤ B) (q' : W ⥤ A) (K : V ⥤ W) (F : B ⥤ A)
    (ε : q ⋙ F ⟶ K ⋙ q') (T : V × V ⥤ V) (T' : W × W ⥤ W)
    (chain : T ⋙ K ≅ K.prod K ⋙ T')
    (μ : MonoidalCategory.tensor B ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor A)
    (P Q N : V) [IsIso (ε.app P)] [IsIso (ε.app Q)] [IsIso (ε.app N)]
    (aB : T.obj (T.obj (P, Q), N) ≅ T.obj (P, T.obj (Q, N)))
    (aA : T'.obj (T'.obj (K.obj P, K.obj Q), K.obj N) ≅
      T'.obj (K.obj P, T'.obj (K.obj Q, K.obj N)))
    (bPQ : q.obj (T.obj (P, Q)) ≅ q.obj P ⊗ q.obj Q)
    (bQN : q.obj (T.obj (Q, N)) ≅ q.obj Q ⊗ q.obj N)
    (bL : q.obj (T.obj (T.obj (P, Q), N)) ≅ q.obj (T.obj (P, Q)) ⊗ q.obj N)
    (bR : q.obj (T.obj (P, T.obj (Q, N))) ≅ q.obj P ⊗ q.obj (T.obj (Q, N)))
    (aPQ : q'.obj (T'.obj (K.obj P, K.obj Q)) ≅ q'.obj (K.obj P) ⊗ q'.obj (K.obj Q))
    (aQN : q'.obj (T'.obj (K.obj Q, K.obj N)) ≅ q'.obj (K.obj Q) ⊗ q'.obj (K.obj N))
    (aL : q'.obj (T'.obj (T'.obj (K.obj P, K.obj Q), K.obj N)) ≅
      q'.obj (T'.obj (K.obj P, K.obj Q)) ⊗ q'.obj (K.obj N))
    (aR : q'.obj (T'.obj (K.obj P, T'.obj (K.obj Q, K.obj N))) ≅
      q'.obj (K.obj P) ⊗ q'.obj (T'.obj (K.obj Q, K.obj N)))
    (aL₀ : q'.obj (T'.obj (K.obj (T.obj (P, Q)), K.obj N)) ≅
      q'.obj (K.obj (T.obj (P, Q))) ⊗ q'.obj (K.obj N))
    (aR₀ : q'.obj (T'.obj (K.obj P, K.obj (T.obj (Q, N)))) ≅
      q'.obj (K.obj P) ⊗ q'.obj (K.obj (T.obj (Q, N))))
    (heB : bL.hom ≫ (bPQ.hom ⊗ₘ 𝟙 (q.obj N)) ≫
        (α_ (q.obj P) (q.obj Q) (q.obj N)).hom =
      q.map aB.hom ≫ bR.hom ≫ (𝟙 (q.obj P) ⊗ₘ bQN.hom))
    (heA : aL.hom ≫ (aPQ.hom ⊗ₘ 𝟙 (q'.obj (K.obj N))) ≫
        (α_ (q'.obj (K.obj P)) (q'.obj (K.obj Q)) (q'.obj (K.obj N))).hom =
      q'.map aA.hom ≫ aR.hom ≫ (𝟙 (q'.obj (K.obj P)) ⊗ₘ aQN.hom))
    (hmPQ : F.map bPQ.hom ≫ μ.hom.app (q.obj P, q.obj Q) ≫
        (ε.app P ⊗ₘ ε.app Q) = ε.app (T.obj (P, Q)) ≫
      q'.map (chain.hom.app (P, Q)) ≫ aPQ.hom)
    (hmQN : F.map bQN.hom ≫ μ.hom.app (q.obj Q, q.obj N) ≫
        (ε.app Q ⊗ₘ ε.app N) = ε.app (T.obj (Q, N)) ≫
      q'.map (chain.hom.app (Q, N)) ≫ aQN.hom)
    (hmL : F.map bL.hom ≫ μ.hom.app (q.obj (T.obj (P, Q)), q.obj N) ≫
        (ε.app (T.obj (P, Q)) ⊗ₘ ε.app N) = ε.app (T.obj (T.obj (P, Q), N)) ≫
      q'.map (chain.hom.app (T.obj (P, Q), N)) ≫ aL₀.hom)
    (hmR : F.map bR.hom ≫ μ.hom.app (q.obj P, q.obj (T.obj (Q, N))) ≫
        (ε.app P ⊗ₘ ε.app (T.obj (Q, N))) = ε.app (T.obj (P, T.obj (Q, N))) ≫
      q'.map (chain.hom.app (P, T.obj (Q, N))) ≫ aR₀.hom)
    (hnL : q'.map (T'.map (X := (K.obj (T.obj (P, Q)), K.obj N))
        (Y := (T'.obj (K.obj P, K.obj Q), K.obj N))
        (chain.hom.app (P, Q), 𝟙 (K.obj N))) ≫ aL.hom =
      aL₀.hom ≫ (q'.map (chain.hom.app (P, Q)) ⊗ₘ q'.map (𝟙 (K.obj N))))
    (hnR : q'.map (T'.map (X := (K.obj P, K.obj (T.obj (Q, N))))
        (Y := (K.obj P, T'.obj (K.obj Q, K.obj N)))
        (𝟙 (K.obj P), chain.hom.app (Q, N))) ≫ aR.hom =
      aR₀.hom ≫ (q'.map (𝟙 (K.obj P)) ⊗ₘ q'.map (chain.hom.app (Q, N))))
    (hc : K.map aB.hom ≫ chain.hom.app (P, T.obj (Q, N)) ≫
        T'.map (X := (K.obj P, K.obj (T.obj (Q, N))))
          (Y := (K.obj P, T'.obj (K.obj Q, K.obj N)))
          (𝟙 (K.obj P), chain.hom.app (Q, N)) =
      chain.hom.app (T.obj (P, Q), N) ≫
        T'.map (X := (K.obj (T.obj (P, Q)), K.obj N))
          (Y := (T'.obj (K.obj P, K.obj Q), K.obj N))
          (chain.hom.app (P, Q), 𝟙 (K.obj N)) ≫ aA.hom) :
    F.map (α_ (q.obj P) (q.obj Q) (q.obj N)).hom ≫
        μ.hom.app (q.obj P, q.obj Q ⊗ q.obj N) ≫
        (𝟙 (F.obj (q.obj P)) ⊗ₘ μ.hom.app (q.obj Q, q.obj N)) =
      μ.hom.app (q.obj P ⊗ q.obj Q, q.obj N) ≫
        (μ.hom.app (q.obj P, q.obj Q) ⊗ₘ 𝟙 (F.obj (q.obj N))) ≫
        (α_ (F.obj (q.obj P)) (F.obj (q.obj Q)) (F.obj (q.obj N))).hom := by
  erw [id_tensorHom, tensorHom_id]
  let PQ := T.obj (P, Q)
  let QN := T.obj (Q, N)
  let lB := bL ≪≫ whiskerRightIso bPQ (q.obj N)
  let rB := bR ≪≫ whiskerLeftIso (q.obj P) bQN
  let lA := aL ≪≫ whiskerRightIso aPQ (q'.obj (K.obj N))
  let rA := aR ≪≫ whiskerLeftIso (q'.obj (K.obj P)) aQN
  let e := ε
  let tPQ := q'.map (chain.hom.app (P, Q))
  let tQN := q'.map (chain.hom.app (Q, N))
  let tL := q'.map (chain.hom.app (PQ, N))
  let tR := q'.map (chain.hom.app (P, QN))
  let eL := e.app (T.obj (PQ, N)) ≫ tL ≫
    q'.map (T'.map (X := (K.obj PQ, K.obj N))
      (Y := (T'.obj (K.obj P, K.obj Q), K.obj N))
      (chain.hom.app (P, Q), 𝟙 (K.obj N)))
  let eR := e.app (T.obj (P, QN)) ≫ tR ≫
    q'.map (T'.map (X := (K.obj P, K.obj QN))
      (Y := (K.obj P, T'.obj (K.obj Q, K.obj N)))
      (𝟙 (K.obj P), chain.hom.app (Q, N)))
  have hB : lB.hom ≫ (α_ (q.obj P) (q.obj Q)
        (q.obj N)).hom = q.map aB.hom ≫ rB.hom := by
    simpa only [lB, rB, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      tensorHom_id, id_tensorHom, Category.assoc] using heB
  have hA : lA.hom ≫ (α_ (q'.obj (K.obj P))
        (q'.obj (K.obj Q)) (q'.obj (K.obj N))).hom =
      q'.map aA.hom ≫ rA.hom := by
    simpa only [lA, rA, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      tensorHom_id, id_tensorHom, Category.assoc] using heA
  erw [q'.map_id, tensorHom_id] at hnL
  erw [q'.map_id, id_tensorHom] at hnR
  have hL₀ := left_square F μ bPQ.hom bL.hom
    (e.app P) (e.app Q) (e.app N) (e.app PQ)
    (e.app (T.obj (PQ, N))) (tPQ ≫ aPQ.hom) (tL ≫ aL₀.hom) hmPQ hmL
  have hR₀ := right_square F μ bQN.hom bR.hom
    (e.app P) (e.app Q) (e.app N) (e.app QN)
    (e.app (T.obj (P, QN))) (tQN ≫ aQN.hom) (tR ≫ aR₀.hom) hmQN hmR
  have hL : F.map lB.hom ≫
      μ.hom.app (q.obj P ⊗ q.obj Q, q.obj N) ≫
      (μ.hom.app (q.obj P, q.obj Q) ▷ F.obj (q.obj N)) ≫
      (((e.app P) ⊗ₘ (e.app Q)) ⊗ₘ (e.app N)) = eL ≫ lA.hom := by
    calc
      _ = e.app (T.obj (PQ, N)) ≫ (tL ≫ aL₀.hom) ≫
          ((tPQ ≫ aPQ.hom) ▷ q'.obj (K.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
  have hR : F.map rB.hom ≫
      μ.hom.app (q.obj P, q.obj Q ⊗ q.obj N) ≫
      (F.obj (q.obj P) ◁ μ.hom.app (q.obj Q, q.obj N)) ≫
      ((e.app P) ⊗ₘ ((e.app Q) ⊗ₘ (e.app N))) = eR ≫ rA.hom := by
    calc
      _ = e.app (T.obj (P, QN)) ≫ (tR ≫ aR₀.hom) ≫
          (q'.obj (K.obj P) ◁ (tQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  have hC : F.map (q.map aB.hom) ≫ eR =
      eL ≫ q'.map aA.hom := by
    have hf := e.naturality aB.hom
    change F.map (q.map aB.hom) ≫
        e.app (T.obj (P, QN)) = e.app (T.obj (PQ, N)) ≫
          q'.map (K.map aB.hom) at hf
    dsimp only [eL, eR]
    rw [reassoc_of% hf]
    simpa only [q'.map_comp, Category.assoc] using
      congrArg (fun f ↦ e.app (T.obj (PQ, N)) ≫ q'.map f) hc
  exact associativity_transport F μ lB rB (q.map aB.hom)
    lA.hom rA.hom (q'.map aA.hom) (asIso (e.app P))
    (asIso (e.app Q)) (asIso (e.app N))
    eL eR hB hA hL hR hC

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]

variable (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory _ _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)
  (K : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
    CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ)
  (F : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
    DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
  (ε : DerivedCategory.Q ⋙ F ⟶ K ⋙ DerivedCategory.Q)
  (hε : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) → IsIso (ε.app P))
  (hU : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
  (chain : coefficientTotalTensor.{r, c, v} J R ⋙ K ≅
    K.prod K ⋙ coefficientTotalTensor.{s, d, vd} J' R')
  (hκ : CoefficientComplexTensorAssociativity J R J' R' K chain)
  (μ : SB.tensor ⋙ F ≅ F.prod F ⋙ SA.tensor)
  (hμ : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hUP : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
    (hUQ : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj Q))
    (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (_fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p)),
    F.map (TB.iso J R SB P Q hP hQ).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SA.tensor.map
          (X := (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj (K.obj P), DerivedCategory.Q.obj (K.obj Q)))
          (Prod.mkHom (ε.app P) (ε.app Q)) =
      ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
        (TA.iso J' R' SA (K.obj P) (K.obj Q) hUP hUQ).hom)

omit [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)] in
private theorem coefficient_total_eq :
    coefficientTotalTensor.{r, c, v} J R = SheafOfModules.KFlatTotalTensorModel.total R := by
  rfl

include cB cA hε hU hκ hμ

attribute [local irreducible] coefficientTotalTensor SheafOfModules.monoidalCategory

-- Paste the four model squares without unfolding localization constructions.
/-- Paste four binary representative squares and the ordinary associativity equation.
Source: Stacks 07A4 and 0FPT.
(blueprint: lem-coef-tensor-associativity-representatives). -/
theorem coefficientTensorAssociativityOnRepresentatives
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (hQ : Q.IsKFlatIndependentCoefficients)
    (fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p))
    (hN : N.IsKFlatIndependentCoefficients)
    (fN : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (N.X p)) :
    F.map (SB.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P,
          SB.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
        SA.tensor.map (Prod.mkHom (𝟙 (F.obj (DerivedCategory.Q.obj P)))
          (μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N))) =
      μ.hom.app (SB.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
        DerivedCategory.Q.obj N) ≫
        SA.tensor.map (Prod.mkHom
          (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
          (𝟙 (F.obj (DerivedCategory.Q.obj N)))) ≫
        (SA.monoidal.associator (F.obj (DerivedCategory.Q.obj P))
          (F.obj (DerivedCategory.Q.obj Q)) (F.obj (DerivedCategory.Q.obj N))).hom := by
  let := SB.monoidal
  let := SA.monoidal
  let V := K
  let := hε P hP fP
  let := hε Q hQ fQ
  let := hε N hN fN
  let B := coefficientTotalTensor.{r, c, v} J R
  let A := coefficientTotalTensor.{s, d, vd} J' R'
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQ := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ
  have hQN := coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN
  have fPQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (PQ.X i) := by
    dsimp only [PQ, B]
    rw [coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R P Q hP hQ fP fQ).2.1
  have fQN : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (QN.X i) := by
    dsimp only [QN, B]
    rw [coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R Q N hQ hN fQ fN).2.1
  have hUP := hU P hP fP
  have hUQ := hU Q hQ fQ
  have hUN := hU N hN fN
  have hUPQ := hU PQ hPQ fPQ
  have hUQN := hU QN hQN fQN
  have hAPQ := coefficientTotalTensor_isKFlat.{s, d, vd} J' R' (V.obj P) (V.obj Q) hUP hUQ
  have hAQN := coefficientTotalTensor_isKFlat.{s, d, vd} J' R' (V.obj Q) (V.obj N) hUQ hUN
  obtain ⟨aB, haB, heB⟩ := cB.associator_model P Q N hP hQ hN
  obtain ⟨aA, haA, heA⟩ := cA.associator_model (V.obj P) (V.obj Q) (V.obj N) hUP hUQ hUN
  have hc : V.map aB.hom ≫ chain.hom.app (P, QN) ≫
        A.map (X := (V.obj P, V.obj QN))
          (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
          (𝟙 (V.obj P), chain.hom.app (Q, N)) =
      chain.hom.app (PQ, N) ≫
        A.map (X := (V.obj PQ, V.obj N))
          (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
          (chain.hom.app (P, Q), 𝟙 (V.obj N)) ≫ aA.hom := by
    exact hκ P Q N aB aA haB haA
  conv at heB =>
    lhs
    arg 1
    rw [cB.tensorIso_both PQ N hPQ hN]
  conv at heB =>
    rhs
    arg 2
    arg 1
    rw [cB.tensorIso_both P QN hP hQN]
  conv at heA =>
    lhs
    arg 1
    rw [cA.tensorIso_both (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN]
  conv at heA =>
    rhs
    arg 2
    arg 1
    rw [cA.tensorIso_both (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN]
  let bPQ := TB.iso J R SB P Q hP hQ
  let bQN := TB.iso J R SB Q N hQ hN
  let bL := TB.iso J R SB PQ N hPQ hN
  let bR := TB.iso J R SB P QN hP hQN
  let aPQ := TA.iso J' R' SA (V.obj P) (V.obj Q) hUP hUQ
  let aQN := TA.iso J' R' SA (V.obj Q) (V.obj N) hUQ hUN
  let aL := TA.iso J' R' SA (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN
  let aR := TA.iso J' R' SA (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN
  let aL₀ := TA.iso J' R' SA (V.obj PQ) (V.obj N) hUPQ hUN
  let aR₀ := TA.iso J' R' SA (V.obj P) (V.obj QN) hUP hUQN
  have hmPQ := hμ P Q hP hQ hUP hUQ fP fQ
  have hmQN := hμ Q N hQ hN hUQ hUN fQ fN
  have hmL := hμ PQ N hPQ hN hUPQ hUN fPQ fN
  have hmR := hμ P QN hP hQN hUP hUQN fP fQN
  have hnL := cA.tensorIso_naturality (V.obj PQ) (V.obj N)
    (A.obj (V.obj P, V.obj Q)) (V.obj N) (Or.inl hUPQ) (Or.inl hAPQ)
    (chain.hom.app (P, Q)) (𝟙 (V.obj N))
  conv at hnL =>
    lhs
    arg 2
    rw [cA.tensorIso_both (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN]
  conv at hnL =>
    rhs
    arg 1
    rw [cA.tensorIso_both (V.obj PQ) (V.obj N) hUPQ hUN]
  have hnR := cA.tensorIso_naturality (V.obj P) (V.obj QN)
    (V.obj P) (A.obj (V.obj Q, V.obj N)) (Or.inl hUP) (Or.inl hUP)
    (𝟙 (V.obj P)) (chain.hom.app (Q, N))
  conv at hnR =>
    lhs
    arg 2
    rw [cA.tensorIso_both (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN]
  conv at hnR =>
    rhs
    arg 1
    rw [cA.tensorIso_both (V.obj P) (V.obj QN) hUP hUQN]
  exact coefficient_tensor_associativity_paste
    DerivedCategory.Q DerivedCategory.Q K F ε B A chain μ P Q N aB aA
    bPQ bQN bL bR aPQ aQN aL aR aL₀ aR₀ heB heA hmPQ hmQN hmL hmR hnL hnR hc

end WeilConjectures
