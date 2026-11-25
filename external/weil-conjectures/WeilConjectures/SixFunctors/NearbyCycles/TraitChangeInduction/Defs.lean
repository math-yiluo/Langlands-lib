/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar

/-!

# The statement of Deligne's induction for the change of strictly henselian trait

Let `T` be a finite discrete ring. `NearbyCyclesModel.TraitChangeInvariance T m` is the statement
of SGA 4½, [Th. finitude], Prop. 3.7, with coefficients `T`, for models whose total space locally
embeds into `𝔸ᵐ` over the base (`AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace`): for
an unramified local injection `ι : R₁ ⟶ R₂` of strictly henselian discrete valuation rings, with
compatible algebraic geometric generic points `Spec Ω₂ ⟶ Spec Ω₁` and residual characteristic
exponent invertible in `T`, a model `N` separated of finite type over `S₁ = Spec R₁` and its base
change `M` to `S₂ = Spec R₂`, both special fibres over the same separably closed field `κ`, the
pullback exchange `Lf'^* Ψ_N K ⟶ Ψ_M (Lφ^* K)` of the models of the geometric generic fibres
(`NearbyCyclesModel.Hom.toGeneric`) is invertible at every complex `K` bounded below of étale
origin.

It is proved by induction on `m` in
`WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Basic`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Invariance of nearby cycles under change of strictly henselian trait in chart dimension
`m`** (SGA 4½, [Th. finitude], Prop. 3.7, coefficients a finite ring `T`). For every unramified
injective local homomorphism `ι : R₁ ⟶ R₂` of strictly henselian discrete valuation rings, a
prime `p` divisible by every natural number vanishing in the residue field of `R₁` and invertible
in `T`, geometric generic points `aᵢ : Rᵢ ⟶ Ωᵢ` (algebraically closed, algebraic over `Rᵢ`)
compatible with `c : Ω₁ ⟶ Ω₂`, a closed point `b₂ : R₂ ⟶ κ` with kernel the maximal ideal (`κ`
separably closed), a model `N` over `Spec R₁` along `q₁` separated of finite type and locally
embedding into `𝔸ᵐ_{R₁}`, with cartesian geometric generic fibre along `g₁` and special fibre
along `p₁` over `b₂ ∘ ι`, a model `M` over `Spec R₂` with cartesian fibres along `g₂`, `p₂`, and a
morphism of models `φ : M ⟶ N` with cartesian square of total spaces over `Spec ι` and compatible
maps of fibres, the pullback exchange of `φ.toGeneric` is invertible at every complex on the
geometric generic fibre of `N` which is bounded below of étale origin.

This is a structure rather than a definition so that the instance proofs in its statement are not
abstracted into auxiliary lemmas, which would make its instances hard to unify with statements
elaborated elsewhere. -/
structure TraitChangeInvariance (m : ℕ) : Prop where
  isIso : ∀ ⦃R₁ R₂ : Type u⦄ [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
    [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
    [IsStrictlyHenselianLocalRing R₂] (ι : R₁ →+* R₂) [IsLocalHom ι], Function.Injective ι →
    maximalIdeal R₂ = (maximalIdeal R₁).map ι →
    ∀ (p : ℕ) [Fact p.Prime], (∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n) → IsUnit (p : T) →
    ∀ ⦃Ω₁ Ω₂ : Type u⦄ [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
      (a₁ : R₁ →+* Ω₁) (a₂ : R₂ →+* Ω₂) (c : Ω₁ →+* Ω₂), Function.Injective a₁ →
      Function.Injective a₂ → (letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁) →
      (letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) → c.comp a₁ = a₂.comp ι →
    ∀ ⦃κ : Type u⦄ [Field κ] [IsSepClosed κ] (b₂ : R₂ →+* κ), RingHom.ker b₂ = maximalIdeal R₂ →
    ∀ ⦃X X' Y Y' : Scheme.{u}⦄ ⦃M : NearbyCyclesModel X X'⦄ ⦃N : NearbyCyclesModel Y Y'⦄
      ⦃f : X ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)),
      LocallyOfFiniteType q₁ → QuasiCompact q₁ → IsSeparated q₁ →
      q₁.LocallyEmbedsInAffineSpace m →
    ∀ (g₁ : N.generic ⟶ Spec (.of Ω₁)), IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁)) →
    ∀ (p₁ : Y' ⟶ Spec (.of κ)),
      IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))) →
    ∀ (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂)),
      IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂)) →
    ∀ (p₂ : X' ⟶ Spec (.of κ)), IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)) →
      IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)) →
      φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c) → f' ≫ p₁ = p₂ →
    ∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) N.generic))),
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
        ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K) →
      IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
