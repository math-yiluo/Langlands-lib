/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-!
# Reduction modulo `ℓⁿ` commutes with the derived tensor product

The derived extension of scalars along the reduction `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` commutes with the
derived tensor products, as extension of scalars is strong monoidal
(`Mod.extendScalarsMonoidal`): this is `Functor.leftDerivedTensorComparison`. On bounded
constructible complexes this gives
`(K ⊗ᴸ M) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ≅ (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⊗ᴸ (M ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`
(`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReductionTensorIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Reduction modulo `ℓⁿ` commutes with the tensor product** of bounded constructible
`𝒪_E`-complexes, as objects of `D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})`. -/
noncomputable def boundedConstructibleIntegersModPowReductionTensorIso
    (K M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructible _).ι.obj
        ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj (K ⊗ M)) ≅
      (boundedConstructible _).ι.obj
          ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj K) ⊗
        (boundedConstructible _).ι.obj
          ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M) :=
  letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E n)
  (boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).app (K ⊗ M) ≪≫
    ((asIso (Mod.extendScalars
      (integersModPowReduction Y.left ℓ E n)).leftDerivedTensorComparison).app K.obj).app M.obj ≪≫
    ((boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).app K ⊗ᵢ
      (boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).app M).symm

end AlgebraicGeometry.ProEtale.CondensedRing
