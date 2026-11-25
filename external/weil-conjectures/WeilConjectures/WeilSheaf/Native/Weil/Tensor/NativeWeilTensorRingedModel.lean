/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedStructure

/-! # The explicit native one-K-flat model

Source: Stacks 06YU, 0FPT. The model is a composite of supplied isomorphisms,
not a witness selected from an existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] Functor.mapDerivedCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)
  (SB : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
  (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)

/-- Pull the ringed one-K-flat model back by the fully faithful derived equivalence.
The counit and exact-functor factorizations are included explicitly.
Source: Stacks 06YU, 0FPT
(blueprint: def-sf-native-weil-tensor-ringed-model). -/
def nativeWeilRingedTensorModel
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) :
    (nativeWeilRingedMonoidal b SB).tensorObj
        (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q T) :=
  let E := nativeWeilRingedDerivedEquivalence b
  E.functor.preimageIso
    (E.counitIso.app (SB.tensor.obj
        (E.functor.obj (DerivedCategory.Q.obj Q), E.functor.obj (DerivedCategory.Q.obj P))) ≪≫
      SB.tensor.mapIso ((b.native.functor.mapDerivedCategoryFactors.app Q).prod
        (b.native.functor.mapDerivedCategoryFactors.app P)) ≪≫
      nativeWeilRingedTensorComplexModel b T adj A SB TB βB cB P Q hP ≪≫
      (b.native.functor.mapDerivedCategoryFactors.app
        (CochainComplex.mapBifunctor P Q T)).symm)

end AlgebraicGeometry.ProEtaleWeilSheaf
