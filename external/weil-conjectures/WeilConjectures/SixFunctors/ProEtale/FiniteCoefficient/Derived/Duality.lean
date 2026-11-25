/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!

# The dualizing complex and the two duals

The six operations on the small pro-étale site are already available: `Lg^*` and `Rg_*`
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`), `Rf_!` and `Rf^!`
(`…Derived.LowerShriek`, `…Derived.UpperShriek`), `- ⊗ᴸ -` and `RHom(-, -)`
(`…Derived.Tensor`, `…Derived.Hom`), together with `RΓ(X, -)` and `RΓ_c(X/Y, -)`. This file
adds the three objects the duality theory builds out of them: the dualizing complex
`ω_{X,Λ} = Ra_X^! Λ`, the Verdier dual `𝔻_X K = RHom(K, ω_{X,Λ})` and the naive dual
`K^∨ = RHom(K, Λ_X)`, plus the ordinary cohomology functors `H^i(X, -)` completing the
compactly supported ones.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedDual`: the naive dual `K ↦ K^∨ = RHom(K, Λ_X)`.
- `AlgebraicGeometry.ProEtale.cohomology`: `H^i(X, -)`, with scoped notation `H(X)[A](i)`.
- `AlgebraicGeometry.ProEtale.dualizingComplex`: `ω_{X,Λ} = Ra_X^! Λ`.
- `AlgebraicGeometry.ProEtale.verdierDual`: `𝔻_X K = RHom(K, ω_{X,Λ})`.

## Implementation notes

The exceptional inverse image `Ra^!` is the constructible one of blueprint
`theorem-f-shriek-ell-adic-coefficients--4` (vi), `ν_X^* ∘ a^× ∘ Rν_{Y,*}` (see
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek`), which needs no
hypothesis on `a` beyond a compactification: the ambient right adjoint of the pro-étale `Ra_!` does
not exist in general.

The constant sheaf `Λ_X` is the monoidal unit `𝟙_ D(X_proét)` of the derived tensor product,
and the coefficient object `Λ` at the point is the monoidal unit `𝟙_ A` of the coefficient
category.

*Perfectness* of `K ∈ D(X_proét)` over `Λ_X` is, in this formalisation, dualizability of `K`
for the derived tensor product, `CategoryTheory.IsDualizable` of
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`. That this is equivalent to
being locally quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules is a
theorem (Stacks, Tag 0FPV),
`AlgebraicGeometry.ProEtale.DerivedCategory.isDualizable_iff_isLocallyPerfect`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

namespace ProEtale

variable (X : Scheme.{u})

/-- Blueprint `definition-verdier-dual-evaluation`: The six operations, the dualizing complex, the
duals.

The naive dual `K ↦ K^∨ = RHom_{Λ_X}(K, Λ_X)` on `D(X_proét)`, the internal hom into the
constant sheaf `Λ_X = 𝟙_ D(X_proét)`. -/
noncomputable def derivedDual :
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (RHom(X)[A]).flip.obj (𝟙_ _)

/-- Blueprint `definition-verdier-dual-evaluation`: The six operations, the dualizing complex, the
duals.

The ordinary cohomology `H^i(X, K) = H^i(RΓ(X, K))`, the companion of the compactly
supported `AlgebraicGeometry.ProEtale.compactlySupportedCohomology`. -/
noncomputable def cohomology (i : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ A :=
  rightDerivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A i

@[inherit_doc cohomology]
scoped notation "H(" X ")[" A "](" i ")" => cohomology A X i

variable {X} {Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]
  [CompactSpace Y]

/-- Blueprint `definition-verdier-dual-evaluation`: The six operations, the dualizing complex, the
duals.

The dualizing complex `ω_{X,Λ} = Ra_X^! Λ` of a scheme `X` with structure morphism
`a_X : X ⟶ Y`, the exceptional inverse image of the constant sheaf `Λ_Y = 𝟙_ D(Y_proét)`. -/
noncomputable def dualizingComplex : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u
    + 1} Λ)) :=
  (R(a)^![Λ]).obj (𝟙_ _)

/-- Blueprint `definition-verdier-dual-evaluation`: The six operations, the dualizing complex, the
duals.

The Verdier dual `𝔻_X K = RHom_{Λ_X}(K, ω_{X,Λ})` on `D(X_proét)`. -/
noncomputable def verdierDual :
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))ᵒᵖ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  (RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj (dualizingComplex Λ a)

end ProEtale

end AlgebraicGeometry
