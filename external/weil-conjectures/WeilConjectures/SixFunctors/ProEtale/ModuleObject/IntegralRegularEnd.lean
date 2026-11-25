/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Multiplication by a constant on the integral coefficient ring

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and `X` a scheme. An
element `x ∈ 𝒪_E` is a constant global section of `𝒪_{E,X}`, and multiplication by it is an
endomorphism of the regular `𝒪_{E,X}`-module
(`ProEtale.padicIntegersRegularEndOfAlgebra`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use it.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The constant global section `ϖ` of `𝒪_{E,X}`, as an endomorphism of the regular
`𝒪_{E,X}`-module: the multiplication by `ϖ`. -/
noncomputable def padicIntegersRegularEndOfAlgebra (ϖ : PadicAlgCl.integers ℓ E) :
    𝟙_ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⟶
      𝟙_ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  Mod.regularLift (Mod.regular _) (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
    (upperStarFromPoint X).map
      (Profinite.continuousMapConstRingHom.{u} (PadicAlgCl.integers ℓ E) ϖ).hom)

end AlgebraicGeometry.ProEtale
