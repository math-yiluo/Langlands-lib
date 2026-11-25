/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorAssociatorRepresentatives
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryModelComparison

/-! # Pasted binary squares for the explicit native derived tensor models

Source: Stacks 06YN, 06YU, 0FPT. Transport the explicit chain models through localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  nativeWeilRingedTensorModel NativeTensorKFlat nativeRingedAssociatorComplex
  nativeRingedTripleLeft nativeRingedTripleRight
  nativeWeilRingedTensorComplexModel

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)
  [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
  (SB : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
  (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)

attribute [local irreducible] nativeWeilRingedMonoidal nativeRingedTensorComparison

-- The concrete model maps remain folded during tensor-square elaboration.
/-- The left iterated native model commutes with the ringed comparison.
Source: Stacks 0FPT
(blueprint: lem-sf-native-weil-ringed-associator-model-left-square).

Proof: paste the two binary model squares, move the inner chain comparison
by tensorIso_naturality, and combine the maps by tensor functoriality. -/
theorem nativeRingedAssociatorModel_left_square
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (_hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q)
    (hN : NativeTensorKFlat k₀ l X T N) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SB.monoidal
    letI := nativeWeilRingedMonoidal b SB
    let E := nativeWeilRingedDerivedEquivalence b
    let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
    let τ := b.native.functor.mapDerivedCategoryFactors
    let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
    let qB := DerivedCategory.Q
      (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
    let B := coefficientTotalTensor b.J b.R
    let μ := nativeRingedTensorComparison b SB
    let pq := nativeTensorComplex T P Q
    let ci (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (hQ : NativeTensorKFlat k₀ l X T Q) :=
      cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
    let bPQ := (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).symm
    let bL := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N pq hN).symm
    let lB := bL ≪≫ whiskerRightIso bPQ (q.obj N)
    let l := nativeRingedTripleLeft b T adj A P Q N
    let ciL := cB.tensorIso (B.obj (Ec.obj P, Ec.obj Q)) (Ec.obj N)
      (Or.inr (A.flat N hN))
    let lA := ciL ≪≫ whiskerRightIso (ci P Q hQ) (qB.obj (Ec.obj N))
    let eL := τ.hom.app (nativeTensorComplex T pq N) ≫ qB.map l.hom
    (E.functor.map lB.hom ≫ μ.hom.app (q.obj P ⊗ q.obj Q, q.obj N) ≫
      (μ.hom.app (q.obj P, q.obj Q) ▷ E.functor.obj (q.obj N)) ≫
      ((τ.hom.app P ⊗ₘ τ.hom.app Q) ⊗ₘ τ.hom.app N) = eL ≫ lA.hom) := by
  classical
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI := SB.monoidal
  letI := nativeWeilRingedMonoidal b SB
  let E := nativeWeilRingedDerivedEquivalence b
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let τ := b.native.functor.mapDerivedCategoryFactors
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qB := DerivedCategory.Q
    (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
  let B := coefficientTotalTensor b.J b.R
  let μ := nativeRingedTensorComparison b SB
  let pq := nativeTensorComplex T P Q
  let ci (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hQ : NativeTensorKFlat k₀ l X T Q) :=
    cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
  have binary (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hQ : NativeTensorKFlat k₀ l X T Q) :=
    nativeRingedTensorModel_binary b T adj A SB TB βB cB P Q hQ
  let bPQ := (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).symm
  let bL := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N pq hN).symm
  let lB := bL ≪≫ whiskerRightIso bPQ (q.obj N)
  let l := nativeRingedTripleLeft b T adj A P Q N
  let ciL := cB.tensorIso (B.obj (Ec.obj P, Ec.obj Q)) (Ec.obj N)
    (Or.inr (A.flat N hN))
  let lA := ciL ≪≫ whiskerRightIso (ci P Q hQ) (qB.obj (Ec.obj N))
  let eL := τ.hom.app (nativeTensorComplex T pq N) ≫ qB.map l.hom
  have hL₀ := RingedForgetTensorTransposition.left_square E.functor μ bPQ.hom bL.hom
    (τ.hom.app P) (τ.hom.app Q) (τ.hom.app N) (τ.hom.app pq)
    (τ.hom.app (nativeTensorComplex T pq N))
    (qB.map (A.chain Q P).hom ≫ (ci P Q hQ).hom)
    (qB.map (A.chain N pq).hom ≫ (ci pq N hN).hom)
    (binary P Q hQ) (binary pq N hN)
  have hnL := cB.tensorIso_naturality (Ec.obj pq) (Ec.obj N)
    (B.obj (Ec.obj P, Ec.obj Q)) (Ec.obj N)
    (Or.inr (A.flat N hN)) (Or.inr (A.flat N hN)) (A.chain Q P).hom (𝟙 _)
  change qB.map (B.map ((A.chain Q P).hom, 𝟙 (Ec.obj N))) ≫ ciL.hom =
    (ci pq N hN).hom ≫ (qB.map (A.chain Q P).hom ⊗ₘ qB.map (𝟙 (Ec.obj N))) at hnL
  simp only [qB.map_id] at hnL
  rw [tensorHom_id (qB.map (A.chain Q P).hom) (qB.obj (Ec.obj N))] at hnL
  have hL : E.functor.map lB.hom ≫ μ.hom.app (q.obj P ⊗ q.obj Q, q.obj N) ≫
    (μ.hom.app (q.obj P, q.obj Q) ▷ E.functor.obj (q.obj N)) ≫
    ((τ.hom.app P ⊗ₘ τ.hom.app Q) ⊗ₘ τ.hom.app N) = eL ≫ lA.hom := by
    calc
      _ = τ.hom.app (nativeTensorComplex T pq N) ≫
          (qB.map (A.chain N pq).hom ≫ (ci pq N hN).hom) ≫
          ((qB.map (A.chain Q P).hom ≫ (ci P Q hQ).hom) ▷ qB.obj (Ec.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        rw [← reassoc_of% hnL]
        simp only [eL, l, nativeRingedTripleLeft, lA, Iso.trans_hom,
          Functor.mapIso_hom, Functor.map_comp, whiskerRightIso_hom, Category.assoc]
        rfl
  exact hL

end AlgebraicGeometry.ProEtaleWeilSheaf
