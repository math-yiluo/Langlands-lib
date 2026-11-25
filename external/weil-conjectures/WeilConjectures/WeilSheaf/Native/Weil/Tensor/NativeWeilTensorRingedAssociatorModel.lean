/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedDerivedAssociatorModelNative
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryModelComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModelSquares
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorLocalizationSquare

/-! # The explicit native chain associator as a derived associator model

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

-- The four explicit tensor models require extra elaboration steps, without unfolding
-- the localization or monoidal structures protected by the local irreducibility API.
-- Elaborate the four model squares while keeping localization definitions folded.
/-- The explicit native binary models identify the transported derived associator
with the localization of the explicit chain associator.
Source: Stacks 06YU, 0FPT
(blueprint: lem-sf-native-weil-ringed-associator-model).

Proof: map the equation through the fully faithful derived equivalence. Its
counit is the tensor comparison for the transported monoidal structure. Expand
the four native binary models, cancel the counit and exact-functor factors, and
use naturality of the ringed binary comparisons to move the two inner chain
comparisons. The resulting equation is cB.associator_model. Its local pure-triple
formula identifies its chain isomorphism with the canonical complex associator
by coefficientAssociator_eq_native. The preimage equation in the definition of
nativeRingedAssociatorComplex supplies the remaining chain square. -/
theorem nativeRingedAssociatorComplex_model
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q)
    (hN : NativeTensorKFlat k₀ l X T N) :
    letI := nativeWeilRingedMonoidal b SB
    let pq := nativeTensorComplex T P Q
    let qn := nativeTensorComplex T Q N
    let pqModel := nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ
    let qnModel := nativeWeilRingedTensorModel b T adj A SB TB βB cB N Q hN
    let leftModel := nativeWeilRingedTensorModel b T adj A SB TB βB cB N pq hN
    let rightModel := nativeWeilRingedTensorModel b T adj A SB TB βB cB qn P
      (nativeTensorComplex_kflat b T adj A Q N hQ hN)
    (leftModel.symm ≪≫ whiskerRightIso pqModel.symm (DerivedCategory.Q.obj N)).hom ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map (nativeRingedAssociatorComplex b T adj A P Q N).hom ≫
        (rightModel.symm ≪≫ whiskerLeftIso (DerivedCategory.Q.obj P) qnModel.symm).hom := by
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
  let qn := nativeTensorComplex T Q N
  have hqn := nativeTensorComplex_kflat b T adj A Q N hQ hN
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
  let a := nativeRingedAssociatorComplex b T adj A P Q N
  let ciL := cB.tensorIso (B.obj (Ec.obj P, Ec.obj Q)) (Ec.obj N)
    (Or.inr (A.flat N hN))
  let ciR := cB.tensorIso (Ec.obj P) (B.obj (Ec.obj Q, Ec.obj N))
    (Or.inl (A.flat P hP))
  let lA := ciL ≪≫ whiskerRightIso (ci P Q hQ) (qB.obj (Ec.obj N))
  let rA := ciR ≪≫ whiskerLeftIso (qB.obj (Ec.obj P)) (ci Q N hN)
  let eL := τ.hom.app (nativeTensorComplex T pq N) ≫ qB.map l.hom
  let eR := τ.hom.app (nativeTensorComplex T P qn) ≫ qB.map r.hom
  have hA : lA.hom ≫ (α_ (qB.obj (Ec.obj P)) (qB.obj (Ec.obj Q))
      (qB.obj (Ec.obj N))).hom =
    qB.map (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom ≫
      rA.hom := by
    exact RingedForgetTensorTransposition.coefficientAssociator_model_native b.J b.R
      SB TB βB cB (Ec.obj P) (Ec.obj Q) (Ec.obj N)
      (A.flat P hP) (A.flat Q hQ) (A.flat N hN)
  obtain ⟨hL, hR⟩ := nativeRingedAssociatorModel_squares b T adj A SB TB βB cB
    P Q N hP hQ hN
  have hC : E.functor.map (q.map a.hom) ≫ eR =
    eL ≫ qB.map (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom := by
    exact nativeRingedAssociatorComplex_localization_square b T adj A P Q N
  exact associator_of_model_comparison E.functor μ
    (X := q.obj P) (Y := q.obj Q) (Z := q.obj N)
    (X' := qB.obj (Ec.obj P)) (Y' := qB.obj (Ec.obj Q)) (Z' := qB.obj (Ec.obj N))
    lB rB (q.map a.hom)
    lA.hom rA.hom
    (qB.map (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom)
    (τ.app P) (τ.app Q) (τ.app N) eL eR hA hL hR hC
    (nativeRingedTensorComparison_associativity b SB (q.obj P) (q.obj Q) (q.obj N))

end AlgebraicGeometry.ProEtaleWeilSheaf
