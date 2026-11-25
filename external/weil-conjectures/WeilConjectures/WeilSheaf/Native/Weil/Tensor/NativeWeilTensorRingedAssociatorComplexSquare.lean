/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison

/-! # Defining squares for the explicit native chain associator

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

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)

set_option linter.style.haveILetI false in
-- The ringed cochain monoidal structure needs a deep search for its graded tensor instances.
/-- The explicit preimage associator satisfies its defining ringed model square.
Source: Stacks 0FPQ (blueprint: lem-sf-native-weil-ringed-associator-complex-square).

Proof: map the full-faithful preimage and cancel the right model inverse. -/
theorem nativeRingedAssociatorComplex_square
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
    Ec.map (nativeRingedAssociatorComplex b T adj A P Q N).hom ≫
        (nativeRingedTripleRight b T adj A P Q N).hom =
      (nativeRingedTripleLeft b T adj A P Q N).hom ≫
        (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  dsimp only [nativeRingedAssociatorComplex]
  exact preimageAssociator_square (b.native.functor.mapHomologicalComplex (.up ℤ))
    (X := (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
    (Y := (b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
    (Z := (b.native.functor.mapHomologicalComplex (.up ℤ)).obj N)
    (nativeRingedTripleLeft b T adj A P Q N) (nativeRingedTripleRight b T adj A P Q N)

end AlgebraicGeometry.ProEtaleWeilSheaf
