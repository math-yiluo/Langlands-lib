/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModelLeftSquare
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModelRightSquare
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

/-- Both iterated native binary model squares commute with the ringed comparisons.
Source: Stacks 0FPT
(blueprint: lem-sf-native-weil-ringed-associator-model-squares).

Proof: combine the separately proved left and right binary model pastings. -/
theorem nativeRingedAssociatorModel_squares
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q)
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
    let qn := nativeTensorComplex T Q N
    let hqn := nativeTensorComplex_kflat b T adj A Q N hQ hN
    let ci (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (hQ : NativeTensorKFlat k₀ l X T Q) :=
      cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
    let bPQ := (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).symm
    let bQN := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N Q hN).symm
    let bL := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N pq hN).symm
    let bR := (nativeWeilRingedTensorModel b T adj A SB TB βB cB qn P hqn).symm
    let lB := bL ≪≫ whiskerRightIso bPQ (q.obj N)
    let rB := bR ≪≫ whiskerLeftIso (q.obj P) bQN
    let l := nativeRingedTripleLeft b T adj A P Q N
    let r := nativeRingedTripleRight b T adj A P Q N
    let ciL := cB.tensorIso (B.obj (Ec.obj P, Ec.obj Q)) (Ec.obj N)
      (Or.inr (A.flat N hN))
    let ciR := cB.tensorIso (Ec.obj P) (B.obj (Ec.obj Q, Ec.obj N))
      (Or.inl (A.flat P hP))
    let lA := ciL ≪≫ whiskerRightIso (ci P Q hQ) (qB.obj (Ec.obj N))
    let rA := ciR ≪≫ whiskerLeftIso (qB.obj (Ec.obj P)) (ci Q N hN)
    let eL := τ.hom.app (nativeTensorComplex T pq N) ≫ qB.map l.hom
    let eR := τ.hom.app (nativeTensorComplex T P qn) ≫ qB.map r.hom
    (E.functor.map lB.hom ≫ μ.hom.app (q.obj P ⊗ q.obj Q, q.obj N) ≫
      (μ.hom.app (q.obj P, q.obj Q) ▷ E.functor.obj (q.obj N)) ≫
      ((τ.hom.app P ⊗ₘ τ.hom.app Q) ⊗ₘ τ.hom.app N) = eL ≫ lA.hom) ∧
    (E.functor.map rB.hom ≫ μ.hom.app (q.obj P, q.obj Q ⊗ q.obj N) ≫
      (E.functor.obj (q.obj P) ◁ μ.hom.app (q.obj Q, q.obj N)) ≫
      (τ.hom.app P ⊗ₘ (τ.hom.app Q ⊗ₘ τ.hom.app N)) = eR ≫ rA.hom) := by
  exact ⟨nativeRingedAssociatorModel_left_square b T adj A SB TB βB cB P Q N hP hQ hN,
    nativeRingedAssociatorModel_right_square b T adj A SB TB βB cB P Q N hP hQ hN⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
