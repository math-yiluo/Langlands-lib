/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedStructure
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorComplexSquare
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

attribute [local irreducible] nativeRingedAssociatorComplex
  nativeRingedTripleLeft nativeRingedTripleRight

variable [HasDerivedCategory.{u + 2}
  (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]

-- The ringed cochain monoidal structure needs a deep search for its graded tensor instances.
/-- The defining chain square commutes with derived localization.
Source: Stacks 0FPQ, 0FPT
(blueprint: lem-sf-native-weil-ringed-associator-localization-square).

Proof: apply naturality of the equivalence's localization factor to the chain
square, then use functoriality to combine its two model maps. -/
theorem nativeRingedAssociatorComplex_localization_square
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    let E := nativeWeilRingedDerivedEquivalence b
    let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
    let τ := b.native.functor.mapDerivedCategoryFactors
    let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
    let qB := DerivedCategory.Q
      (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
    let pq := nativeTensorComplex T P Q
    let qn := nativeTensorComplex T Q N
    let l := nativeRingedTripleLeft b T adj A P Q N
    let r := nativeRingedTripleRight b T adj A P Q N
    let a := nativeRingedAssociatorComplex b T adj A P Q N
    E.functor.map (q.map a.hom) ≫
        (τ.hom.app (nativeTensorComplex T P qn) ≫ qB.map r.hom) =
      (τ.hom.app (nativeTensorComplex T pq N) ≫ qB.map l.hom) ≫
        qB.map (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  let E := nativeWeilRingedDerivedEquivalence b
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let τ := b.native.functor.mapDerivedCategoryFactors
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qB := DerivedCategory.Q
    (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
  exact localizationModel_square q qB E.functor Ec τ
    (nativeRingedAssociatorComplex b T adj A P Q N).hom
    (nativeRingedTripleLeft b T adj A P Q N).hom
    (nativeRingedTripleRight b T adj A P Q N).hom
    (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom
    (nativeRingedAssociatorComplex_square b T adj A P Q N)

end AlgebraicGeometry.ProEtaleWeilSheaf
