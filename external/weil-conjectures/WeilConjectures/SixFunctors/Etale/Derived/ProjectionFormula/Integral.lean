/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# The projection formula at the integral stage `𝒪_E`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E` and maximal ideal
`𝔪_E = (ϖ)`. This file proves the projection formula at the integral stage of the `ℓ`-adic
formalism (blueprint `lemma-projection-formula-integral-coefficients`, with its detailed node
`thm-sf-pf-adic`): for `f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, 𝒪_E)` and
`L ∈ D(Y_ét, 𝒪_E)`, the projection map

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

is an isomorphism in the integral stage `D_comp(Y_ét, 𝒪_E)`, i.e. after derived completion
`DerivedCategoryDerivedCompleteIntegral.completion`, and its reductions modulo every `𝔪_Eⁿ` are
isomorphisms.

## The statement

The operations of the integral stage are defined levelwise on the finite reductions (blueprint
`theorem-f-shriek-ell-adic-coefficients--4`, adic stages; `def-exchange-projection`: the coefficient
categories `𝒪_E`, `E`, `ℚ̄_ℓ` "are obtained by derived completion"): the integral `Rf_! K ⊗ᴸ L` is
the derived limit `R lim_n (Rf_! K_n ⊗ᴸ L_n)` of its reductions, and `PF_{f, K, L}` over `𝒪_E` is
the morphism realized by the system `(PF_{f, K_n, L_n})_n` (`thm-sf-pf-adic`). Since reduction
commutes with the plain operations of `D(X_ét, 𝒪_E)`
(`proposition-six-operations-change-coefficients`), this derived limit is the derived completion
`(Rf_! K ⊗ᴸ L)^` of the plain operation, and the integral projection map is the derived completion
of the plain projection map. So the statement proved here,
`AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`, is the blueprint statement.

The plain projection map of `D(X_ét, 𝒪_E)` itself is only shown to be an isomorphism when its
source and target are derived complete
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map`). The blueprint
sketch notes that its own argument for the plain statement is incomplete (Step 3 needs the derived
completeness of both sides), and for the plain operations of `D(X_ét, 𝒪_E)` this fails in general:
`- ⊗ᴸ -` and `Lf^*` do not preserve derived completeness (for `X = Spec 𝔽_q` the derived limit `𝒪̂`
of the `(𝒪_E/𝔪_Eⁿ)_X` has `H¹(𝒪̂) ≠ 0`, so `𝒪̂ ⊗ᴸ 𝒪̂` has `H² ≠ 0` and is not derived complete), and
derived complete bounded constructible objects are very rare (the constant sheaf `𝒪_E` is not
derived complete on `Spec 𝔽_q`), so that a proof of the plain statement for them would need a
classification of these objects.

## Proof

* the reduction `ρ(PF_{f, K, L})` modulo `𝔪_Eⁿ` is an isomorphism (Steps 1 and 2 of the blueprint
  proof: it is the finite-level projection map `PF_{f, K_n, L_n}`);
* hence the cone of `PF_{f, K, L}` is an object on which `ϖ` acts invertibly, and the derived
  completion inverts such morphisms
  (`DerivedCategory.isIso_derivedCompletion_map`) — this replaces Step 3 of the
  blueprint proof.

## Main statements

- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap`:
  the reductions modulo `𝔪_Eⁿ` of the projection map are isomorphisms.
- `AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`: the
  projection formula at the integral stage.
- `AlgebraicGeometry.Etale.isIso_completion_map_projectionMap_of_derivedCompleteIntegral`
  (`thm-sf-pf-adic`): the same, together with the compatibility with all finite reductions.
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map`: the plain
  projection formula when both sides are derived complete.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. The ring structure is written
as the one underlying the commutative ring structure, as in the statements of the lemmas for
general commutative coefficient rings that are applied to it. -/
local notation "𝐌" =>
  @ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)) CommRing.toRing

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

/-- The reconstruction step of the projection formula, for an arbitrary coefficient ring `Λ'`
and a nonzerodivisor `ϖ`: if both sides of the projection map are derived `ϖ`-complete and its
reduction modulo `ϖ` is an isomorphism, then the projection formula holds. -/
theorem hasProjectionFormula_of_derivedComplete_of_isIso_reductionModIdeal {Λ' : Type (u + 1)}
    [CommRing Λ'] {ϖ : Λ'} (hϖ : ϖ ∈ nonZeroDivisors Λ') (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')))
    (hs : _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology (Ideal.span {ϖ})
      (((derivedTensor (ModuleCat.{u + 1} Λ') Y).obj
        ((R(f)_![ModuleCat.{u + 1} Λ']).obj K)).obj L))
    (ht : _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology (Ideal.span {ϖ})
      ((R(f)_![ModuleCat.{u + 1} Λ']).obj (((derivedTensor (ModuleCat.{u + 1} Λ') X).obj K).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj L))))
    (hρ : IsIso ((reductionModIdeal Λ' Y (Ideal.span {ϖ})).map (projectionMapApp Λ' f K L))) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ') f K L :=
  isIso_of_derivedComplete_of_isIso_reductionModIdeal hϖ _ hs ht hρ

/-- **The reconstruction step of the projection formula at the integral stage.** If both sides
`Rf_! K ⊗ᴸ L` and `Rf_!(K ⊗ᴸ Lf^* L)` of the projection map are derived complete for `𝔪_E`, and
the reduction of the projection map modulo `𝔪_E` is an isomorphism, then the projection formula
holds for `f` at `K` and `L`.

This is the passage to the limit of blueprint `lemma-projection-formula-integral-coefficients`
(Step 3) and `thm-sf-pf-adic`: the reduction modulo `𝔪_E = (ϖ)` is conservative on derived complete
objects (`AlgebraicGeometry.Etale.isIso_of_derivedComplete_of_isIso_reductionModIdeal`). -/
theorem hasProjectionFormula_of_isIso_reductionModIdeal_map (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hs : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((derivedTensor 𝐌 Y).obj ((R(f)_![𝐌]).obj K)).obj L))
    (ht : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![𝐌]).obj (((derivedTensor 𝐌 X).obj K).obj ((L((f)^*[𝐌])).obj L))))
    (hρ : IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E)).map
      (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L))) :
    HasProjectionFormula 𝐌 f K L := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  change _root_.DerivedCategory.derivedComplete _ (PadicAlgCl.maximalIdealShrink l E) _ at hs ht
  rw [hI] at hs ht hρ
  exact hasProjectionFormula_of_derivedComplete_of_isIso_reductionModIdeal hϖ f K L hs ht hρ

/-- The quotients `𝒪_E ⧸ 𝔪_Eⁿ` are finite. -/
lemma finite_quotient_maximalIdealShrink_pow (n : ℕ) :
    Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸ PadicAlgCl.maximalIdealShrink l E ^ n) :=
  .of_equiv _ (Ideal.quotientEquiv (IsLocalRing.maximalIdeal (PadicAlgCl.integers l E) ^ n) _
    (PadicAlgCl.shrinkRingEquiv l E)
    (by rw [PadicAlgCl.maximalIdealShrink, Ideal.map_pow]; rfl)).toEquiv

/-- Steps 1 and 2 of blueprint `lemma-projection-formula-integral-coefficients`: the reduction of
the projection map modulo `𝔪_E` is an isomorphism.

If `K` and `L` are bounded constructible, derived complete for `𝔪_E` and of finite Tor
amplitude, then `ρ(PF_{f, K, L})`, the image of the projection map under the reduction
`- ⊗ᴸ (𝒪_E/𝔪_E)_Y`, is an isomorphism. In the blueprint, `ρ(PF_{f, K, L})` is identified with the
finite-level projection map `PF_{f, K₁, L₁}` by the reduction square of
`sk-prop-sf-pf-reduction` (`proposition-six-operations-change-coefficients`), and the latter is an
isomorphism by the finite-level projection formula `sk-thm-sf-pf-finite`
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_finite`). The hypotheses
on `K` and `L` are not needed. -/
theorem isIso_reductionModIdeal_map_projectionMap_of_derivedCompleteIntegral (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (_hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (_hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (_hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (_hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (_hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (_hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E)).map
      (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  have : Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸ Ideal.span {ϖ} ^ 1) := by
    rw [← hI]
    exact finite_quotient_maximalIdealShrink_pow l E _
  have h := isIso_reductionModIdeal_map_projectionMap_of_finite hϖ 1 f K L
  rwa [pow_one, ← hI] at h

/-- Steps 1 and 2 of blueprint `lemma-projection-formula-integral-coefficients`, at every level `n`:
the reduction of the projection map modulo `𝔪_Eⁿ` is an isomorphism.

For all `K` and `L`, `ρ_n(PF_{f, K, L})`, the image of the projection map under the reduction
`- ⊗ᴸ (𝒪_E/𝔪_Eⁿ)_Y`, is an isomorphism: it is identified with the finite-level projection map
`PF_{f, K_n, L_n}` over `𝒪_E/𝔪_Eⁿ` by the reduction square of `sk-prop-sf-pf-reduction`
(`proposition-six-operations-change-coefficients`), an isomorphism by the finite-level projection
formula `sk-thm-sf-pf-finite`
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_finite`). -/
theorem isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)) (n : ℕ) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  have : Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸ Ideal.span {ϖ} ^ n) := by
    rw [← hI]
    exact finite_quotient_maximalIdealShrink_pow l E _
  have h := isIso_reductionModIdeal_map_projectionMap_of_finite hϖ n f K L
  rwa [← hI] at h

/-- **The derived completion inverts morphisms whose reduction is an isomorphism.** A morphism
`u` of `D(X_ét, 𝒪_E)` whose reduction modulo `𝔪_E` is an isomorphism becomes an isomorphism in
the integral stage `D_comp(X_ét, 𝒪_E)`: its cone `C` has `C ⊗ᴸ (𝒪_E/𝔪_E)_X = 0`, so `ϖ` acts
invertibly on `C` (`AlgebraicGeometry.Etale.isIso_smul_id_of_isZero_reductionModIdeal`), and the
derived completion inverts such morphisms. -/
theorem isIso_completion_map_of_isIso_reductionModIdeal
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌)} (u : M ⟶ N)
    (hu : IsIso ((reductionModIdeal _ X (PadicAlgCl.maximalIdealShrink l E)).map u)) :
    IsIso ((DerivedCategoryDerivedCompleteIntegral.completion X.smallEtaleTopology l E).map u) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  rw [hI] at hu
  have hC : IsZero ((reductionModIdeal _ X (Ideal.span {ϖ})).obj C) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal _ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  exact _root_.DerivedCategory.isIso_derivedCompletion_map _ hI hT
    (isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC)

/-- **The projection formula at the integral stage of the étale model** (the étale-site form of
the old blueprint `lemma-projection-formula-integral-coefficients`; the pro-étale statement of the
current blueprint is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaAdic`).

At the integral stage of the `ℓ`-adic formalism, where the coefficients are the ring of
integers `𝒪_E` of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the projection map

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

is an isomorphism in `D_comp(Y_ét, 𝒪_E)`: its image under the derived completion
`D(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_E)`, which is the projection map for the operations of the
integral stage (defined levelwise as derived limits of their finite reductions, see the module
docstring), is an isomorphism. This holds for all `K` and `L`, in particular for the
derived-complete objects of finite Tor amplitude of the blueprint.

The proof follows Steps 1 and 2 of the blueprint: the reduction of the projection map modulo
`𝔪_E` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap`).
Step 3 is replaced by the fact that the derived completion inverts such morphisms
(`AlgebraicGeometry.Etale.isIso_completion_map_of_isIso_reductionModIdeal`); the derived
completeness of the two sides of the plain projection map, which Step 3 needs and which the
blueprint sketch leaves open, is not used. -/
theorem isIso_completion_map_projectionMap (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)) :
    IsIso ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E).map
      (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)) := by
  refine isIso_completion_map_of_isIso_reductionModIdeal l E _ ?_
  have h := isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap l E f K L 1
  rwa [pow_one] at h

/-- Blueprint `thm-sf-pf-adic`: Derived-complete reconstruction over `𝒪_E`.

Let `K` and `L` be bounded constructible, derived complete for `𝔪_E` and of finite Tor amplitude.
The finite-level projection maps `PF_{f, K_n, L_n}`, which are the reductions modulo `𝔪_Eⁿ` of the
projection map `PF_{f, K, L}`, are isomorphisms, and they realize an isomorphism over `𝒪_E`: the
derived completion of `PF_{f, K, L}`, an isomorphism of `D_comp(Y_ét, 𝒪_E)` whose reductions are
the `PF_{f, K_n, L_n}` (the completion map `M ⟶ M^` of any `M` induces isomorphisms on all
reductions, its cone having `ϖ` acting invertibly).

The hypotheses on `K` and `L` are not needed: see
`AlgebraicGeometry.Etale.isIso_completion_map_projectionMap` and
`AlgebraicGeometry.Etale.isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap`. -/
theorem isIso_completion_map_projectionMap_of_derivedCompleteIntegral (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (_hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (_hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (_hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (_hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (_hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (_hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) :
    IsIso ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E).map
        (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)) ∧
      ∀ n : ℕ, IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
        (projectionMapApp (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)) :=
  ⟨isIso_completion_map_projectionMap l E f K L,
    isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap l E f K L⟩

end Etale

end AlgebraicGeometry
