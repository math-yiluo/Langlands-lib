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
/-- The right iterated native model commutes with the ringed comparison.
Source: Stacks 0FPT
(blueprint: lem-sf-native-weil-ringed-associator-model-right-square).

Proof: paste the two binary model squares, move the inner chain comparison
by tensorIso_naturality, and combine the maps by tensor functoriality. -/
theorem nativeRingedAssociatorModel_right_square
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
    let qn := nativeTensorComplex T Q N
    let hqn := nativeTensorComplex_kflat b T adj A Q N hQ hN
    let ci (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (hQ : NativeTensorKFlat k₀ l X T Q) :=
      cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
    let bQN := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N Q hN).symm
    let bR := (nativeWeilRingedTensorModel b T adj A SB TB βB cB qn P hqn).symm
    let rB := bR ≪≫ whiskerLeftIso (q.obj P) bQN
    let r := nativeRingedTripleRight b T adj A P Q N
    let ciR := cB.tensorIso (Ec.obj P) (B.obj (Ec.obj Q, Ec.obj N))
      (Or.inl (A.flat P hP))
    let rA := ciR ≪≫ whiskerLeftIso (qB.obj (Ec.obj P)) (ci Q N hN)
    let eR := τ.hom.app (nativeTensorComplex T P qn) ≫ qB.map r.hom
    (E.functor.map rB.hom ≫ μ.hom.app (q.obj P, q.obj Q ⊗ q.obj N) ≫
      (E.functor.obj (q.obj P) ◁ μ.hom.app (q.obj Q, q.obj N)) ≫
      (τ.hom.app P ⊗ₘ (τ.hom.app Q ⊗ₘ τ.hom.app N)) = eR ≫ rA.hom) := by
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
  let qn := nativeTensorComplex T Q N
  have hqn := nativeTensorComplex_kflat b T adj A Q N hQ hN
  let ci (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hQ : NativeTensorKFlat k₀ l X T Q) :=
    cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
  have binary (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hQ : NativeTensorKFlat k₀ l X T Q) :=
    nativeRingedTensorModel_binary b T adj A SB TB βB cB P Q hQ
  let bQN := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N Q hN).symm
  let bR := (nativeWeilRingedTensorModel b T adj A SB TB βB cB qn P hqn).symm
  let rB := bR ≪≫ whiskerLeftIso (q.obj P) bQN
  let r := nativeRingedTripleRight b T adj A P Q N
  let ciR := cB.tensorIso (Ec.obj P) (B.obj (Ec.obj Q, Ec.obj N))
    (Or.inl (A.flat P hP))
  let rA := ciR ≪≫ whiskerLeftIso (qB.obj (Ec.obj P)) (ci Q N hN)
  let eR := τ.hom.app (nativeTensorComplex T P qn) ≫ qB.map r.hom
  have hR₀ := RingedForgetTensorTransposition.right_square E.functor μ bQN.hom bR.hom
    (τ.hom.app P) (τ.hom.app Q) (τ.hom.app N) (τ.hom.app qn)
    (τ.hom.app (nativeTensorComplex T P qn))
    (qB.map (A.chain N Q).hom ≫ (ci Q N hN).hom)
    (qB.map (A.chain qn P).hom ≫ (ci P qn hqn).hom)
    (binary Q N hN) (binary P qn hqn)
  have hnR := cB.tensorIso_naturality (Ec.obj P) (Ec.obj qn)
    (Ec.obj P) (B.obj (Ec.obj Q, Ec.obj N))
    (Or.inr (A.flat qn hqn)) (Or.inl (A.flat P hP)) (𝟙 _) (A.chain N Q).hom
  change qB.map (B.map (𝟙 (Ec.obj P), (A.chain N Q).hom)) ≫ ciR.hom =
    (ci P qn hqn).hom ≫ (qB.map (𝟙 (Ec.obj P)) ⊗ₘ qB.map (A.chain N Q).hom) at hnR
  simp only [qB.map_id] at hnR
  rw [id_tensorHom (qB.obj (Ec.obj P)) (qB.map (A.chain N Q).hom)] at hnR
  have hR : E.functor.map rB.hom ≫ μ.hom.app (q.obj P, q.obj Q ⊗ q.obj N) ≫
    (E.functor.obj (q.obj P) ◁ μ.hom.app (q.obj Q, q.obj N)) ≫
    (τ.hom.app P ⊗ₘ (τ.hom.app Q ⊗ₘ τ.hom.app N)) = eR ≫ rA.hom := by
    calc
      _ = τ.hom.app (nativeTensorComplex T P qn) ≫
          (qB.map (A.chain qn P).hom ≫ (ci P qn hqn).hom) ≫
          (qB.obj (Ec.obj P) ◁ (qB.map (A.chain N Q).hom ≫ (ci Q N hN).hom)) := hR₀
      _ = _ := by
        simp only [whiskerLeft_comp, Category.assoc]
        rw [← reassoc_of% hnR]
        simp only [eR, r, nativeRingedTripleRight, rA, Iso.trans_hom,
          Functor.mapIso_hom, Functor.map_comp, whiskerLeftIso_hom, Category.assoc]
        rfl
  exact hR

end AlgebraicGeometry.ProEtaleWeilSheaf
