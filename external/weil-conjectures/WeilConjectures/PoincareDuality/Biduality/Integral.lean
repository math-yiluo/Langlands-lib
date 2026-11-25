/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier

/-!
# The double-dual morphism with integral coefficients `𝒪_E`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X` a separated
`k`-scheme of finite type. This file defines, for bounded constructible `𝒪_E`-complexes, the
objects of the Verdier formalism of `WeilConjectures.PoincareDuality.Verdier`:

- `ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructibleBraiding`: the Koszul braiding
  of `Dᵇc(X)⟦𝒪̲_E⟧`, the restriction of `DerivedCategory.braidedCategory'`; as for `ℚ̲̄_ℓ` it is
  meant to be used as a local instance;
- `ProEtale.CondensedRing.PadicIntegersRingObj.dualizingComplex`: `ω_X = Ra_X^! 𝒪_E`;
- `ProEtale.CondensedRing.PadicIntegersRingObj.verdierBiduality`: the double-dual morphism
  `δ_K : K ⟶ 𝔻_X 𝔻_X K`, `𝔻_X = RHom(-, ω_X)`.

These are the integral stage `Λ = 𝒪_E` of blueprint `theorem-verdier-biduality`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

attribute [local instance] DerivedCategory.braidedCategory' in
/-- The Koszul braiding of the derived tensor product on `Dᵇc(X)⟦𝒪̲_E⟧`: the restriction
(`ObjectProperty.fullBraidedSubcategory`) of the braiding `DerivedCategory.braidedCategory'` of
`D(Mod_{𝒪_{E,X}})`. As `ProEtale.CondensedRing.boundedConstructibleBraiding`, it is not an
instance. -/
@[instance_reducible]
noncomputable def boundedConstructibleBraiding :
    BraidedCategory (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  ObjectProperty.fullBraidedSubcategory _

attribute [local instance] boundedConstructibleBraiding

/-- The **dualizing complex** `ω_X = Ra_X^! 𝒪_E` (`𝒪_E`-coefficient), for the structure morphism
`a_X : X ⟶ Spec k`, the morphism `Over.mkIdTerminal.from X` to the terminal object. -/
noncomputable def dualizingComplex : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (boundedConstructibleUpperShriek ℓ E (Over.mkIdTerminal.from X)).obj (𝟙_ _)

variable {X}

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)` (`𝒪_E`-coefficient). -/
noncomputable def verdierDual (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (ihom K).obj (dualizingComplex ℓ E X)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K` (`𝒪_E`-coefficient): the transpose of the
evaluation pairing `𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    K ⟶ verdierDual ℓ E (verdierDual ℓ E K) :=
  Verdier.bidualityMap (dualizingComplex ℓ E X) K

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
