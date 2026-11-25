/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Typing

/-!
# Preservation on the proved finite-Tor domains

This file states blueprint `proposition-six-operations-dctf` (`proposition-six-operations-dctf`) at
a finite coefficient ring `Λ` whose exponent is invertible on the base field `k`:
`AlgebraicGeometry.Etale.constructibleFiniteTor_stability` bundles clauses (i)–(vi) and the
finite-reduction part of clause (vii), with the Tor intervals of the blueprint. The integral
part of clause (vii) is `AlgebraicGeometry.Etale.boundedConstructibleIntegral_stability`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleFiniteTor_stability` (`proposition-six-operations-dctf`).
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`
  (`proposition-six-operations-dctf`, clause (v)): `Rf^! K ≅ 𝔻_X (Lf^* (𝔻_Y K))` on `Dctf(Y, Λ)`.
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_stability`
(`proposition-six-operations-dctf`,
  clause (vii), integral coefficients).

## Implementation notes

* The six operations are those of the ambient derived categories `D(-_ét, Λ)`; their restrictions
  to `Dctf` are `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.leftDerivedUpperStar`, …, and
  the typing rule relating the two is `AlgebraicGeometry.Etale.typingRule`
  (`proposition-six-operations-dctf`).
* The dimension-free internal-Hom interval `[c - b, d - a]` needs a site-perfect (dualizable)
  first variable; that it fails in general (the origin of `𝔸¹`) is
  `AlgebraicGeometry.Etale.not_forall_torAmplitudeIn_derivedHom`, which needs a normalized Tate
  twist and is therefore not part of the bundled statement.
* Of the finite-reduction comparisons of clause (vii), the ones for `Lf^*`, `⊗ᴸ` and `Rf_!` are
  stated; the comparisons for `Rf_*`, internal Hom, `𝔻_X` and `Rf^!` at a finite stage
  (blueprint `lemma-change-coefficients-direct-image--1`,
  `lemma-change-coefficients-internal-hom--1`, `theorem-verdier-biduality--2`,
  `lemma-change-coefficients-exceptional-inverse-image--1`) and the passage to the field stages `E`,
  `ℚ̄_ℓ` are not formalised: the field stages need coefficient categories the library does not have.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Blueprint `proposition-six-operations-dctf`, clause (v): the exceptional inverse image is
`Rf^! = 𝔻_X f^* 𝔻_Y` on `Dctf(Y, Λ)`.

For `k` algebraically closed, a finite `Λ` whose exponent is invertible on `k` and `f : X ⟶ Y`
over `k`, with `Y` separated of finite type over `k`, every `K ∈ Dctf(Y, Λ)` satisfies
`Rf^! K ≅ 𝔻_X (Lf^* (𝔻_Y K))`: apply the exchange `Rf^! 𝔻_Y ≅ 𝔻_X f^*`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual`) to `𝔻_Y K` and use
the biduality `K ≅ 𝔻_Y 𝔻_Y K` (`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`). -/
theorem nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar
    [IsSeparated aY] [HasCompactification aY] [HasCompactification aX] (f : X ⟶ Y)
    (hf : f ≫ aY = aX) [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    Nonempty ((R(f)^![Λ]).obj K ≅
      (verdierDual Λ aX).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
          ((verdierDual Λ aY).obj (op K))))) := by
  subst hf
  obtain ⟨b⟩ := nonempty_iso_verdierDual_verdierDual Λ aY hK
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_verdierDual Λ aY f
    ((verdierDual Λ aY).obj (op K))
  exact ⟨(R(f)^![Λ]).mapIso b ≪≫ e⟩

/-- Blueprint `proposition-six-operations-dctf`: Preservation on the proved finite-Tor domains.

Let `Λ` be a finite ring whose exponent is invertible on the algebraically closed field `k`, and
`f : X ⟶ Y` a morphism over `k` of separated finite-type `k`-schemes (it is then separated of
finite type; `f` is assumed to admit a compactification). At this finite coefficient stage:

1. (i) `Lf^*` carries `Dctf(Y, Λ)` into `Dctf(X, Λ)`, preserving the Tor interval `[a, b]`;
2. (ii) `⊗ᴸ` carries `Dctf × Dctf` into `Dctf`, with Tor intervals `[a, b] + [c, d] ↦
   [a + c, b + d]`; internal Hom carries `Dctf × Dctf` into `Dctf`, and if `dim X ≤ m` it sends
   bounded constructible inputs of Tor amplitude `[a, b]`, `[c, d]` to Tor amplitude
   `[c - b - 2m, d - a + 2m]`, sharpened to `[c - b, d - a]` when the first variable `K` is
   site-perfect (dualizable), in which case `RHom(K, M) ≅ K^∨ ⊗ᴸ M` with `K^∨ = RHom(K, Λ_X)`;
3. (iii) `Rf_*` carries `Dctf(X, Λ)` into `Dctf(Y, Λ)`, and if `dim X ≤ d` a bounded constructible
   input of Tor amplitude `[a, b]` goes to Tor amplitude `[a, b + 2d]`;
4. (iv) `Rf_!` carries `Dctf(X, Λ)` into `Dctf(Y, Λ)`;
5. (v) on `Dctf(Y, Λ)`, `Rf^! ≅ 𝔻_X f^* 𝔻_Y`, `Rf^!` carries `Dctf(Y, Λ)` into `Dctf(X, Λ)`, and
   if `dim X ≤ d_X`, `dim Y ≤ d_Y`, an input of Tor amplitude `[a, b]` goes to Tor amplitude
   `[a - 2 d_X, b + 2 d_Y]`;
6. (vi) `𝔻_X = RHom(-, Ra_X^! Λ)` preserves `Dctf(X, Λ)`, the double-dual map `K ⟶ 𝔻_X 𝔻_X K`
   is an isomorphism there, `𝔻_X` is exact (it carries a distinguished triangle
   `K → L → M → K[1]` to a distinguished triangle `𝔻M → 𝔻L → 𝔻K → 𝔻M[1]`), and `𝔻_X` restricts
   to an anti-equivalence `Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`
   (`AlgebraicGeometry.Etale.verdierDualEquivalence`);
7. (vii) finite coefficient quotients `K ↦ K ⊗ᴸ (Λ ⧸ J)_X` commute with `Lf^*`, with `⊗ᴸ` and with
   `Rf_!`.

The integral part of (vii) is `AlgebraicGeometry.Etale.boundedConstructibleIntegral_stability`. -/
theorem constructibleFiniteTor_stability [IsSeparated aX] [HasCompactification aX]
    [IsSeparated aY] [HasCompactification aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f] :
    -- (i)
    ((∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    -- (ii)
    ((∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
      (∀ (a b c d : ℤ)
        (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a + c) (b + d)
              (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)) ∧
      (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
            constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
              (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
      (∀ m : ℕ, topologicalKrullDim X ≤ (m : WithBot ℕ∞) → ∀ (a b c d : ℤ)
        (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        boundedConstructible (ModuleCat.{u + 1} Λ) X K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
            boundedConstructible (ModuleCat.{u + 1} Λ) X M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
                torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ))
                  (d - a + 2 * (m : ℤ)) (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
      (∀ (a b c d : ℤ)
        (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        boundedConstructible (ModuleCat.{u + 1} Λ) X K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K → IsDualizable K →
            boundedConstructible (ModuleCat.{u + 1} Λ) X M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
                torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                  (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
      ∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsDualizable K →
          Nonempty ((((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) ≅
            ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj
              ((coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).obj M)) ∧
    -- (iii)
    ((∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        boundedConstructible (ModuleCat.{u + 1} Λ) X K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
              ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    -- (iv)
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) ∧
    -- (v)
    ((∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        Nonempty ((R(f)^![Λ]).obj K ≅
          (verdierDual Λ aX).obj
            (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
              ((verdierDual Λ aY).obj (op K)))))) ∧
      (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((R(f)^![Λ]).obj K)) ∧
      ∀ dX dY : ℕ, topologicalKrullDim X ≤ (dX : WithBot ℕ∞) →
        topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) → ∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
              ((R(f)^![Λ]).obj K)) ∧
    -- (vi)
    ((∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((verdierDual Λ aX).obj (op K)) ∧
          Nonempty (K ≅ (verdierDual Λ aX).obj
            (op ((verdierDual Λ aX).obj (op K)))) ∧
          IsIso ((verdierDualDoubleDual Λ aX).app K)) ∧
      (∀ T ∈ distTriang (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} Λ))),
        ∃ w, Triangle.mk ((verdierDual Λ aX).map T.mor₂.op)
          ((verdierDual Λ aX).map T.mor₁.op) w ∈ distTriang _) ∧
      Nonempty ((verdierDualEquivalence Λ aX).functor ⋙
          DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
        (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X).op ⋙
          verdierDual Λ aX)) ∧
    -- (vii)
    ∀ J : Ideal Λ,
      Nonempty (reductionModIdeal Λ Y J ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
        L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ X J) ∧
      (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        Nonempty ((reductionModIdeal Λ X J).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) ≅
          ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj ((reductionModIdeal Λ X J).obj M))) ∧
      Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
        reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : IsSeparated f := by
    have : IsSeparated (f ≫ aY) := hf ▸ inferInstance
    exact IsSeparated.of_comp f aY
  have : QuasiCompact f := by
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    have : QuasiCompact (f ≫ aY) := hf ▸ inferInstance
    exact QuasiCompact.of_comp f aY
  obtain ⟨hi, hii, hiii, hiv, hdhom, hv, -⟩ :=
    constructibleFiniteTor_preservation Λ aX aY f hf
  obtain ⟨hti, htii, -, hthom, hthomd, -, htvi, hbid⟩ := torAmplitudeIn_preservation Λ aX aY f hf
  refine ⟨⟨hi, hti⟩, ⟨hii, htii, hdhom, hthom, hthomd,
      fun K M hK ↦ ⟨(nonempty_iso_coefficientDual_tensor hK M).some.symm⟩⟩,
    ⟨hiii, fun d hd a b K hK hKt ↦ ?_⟩,
    hiv, ⟨fun K hK ↦ nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY
      f hf hK, hv, fun dX dY hdX hdY a b K hK hKt ↦ ?_⟩,
    ⟨fun K hK ↦ ⟨(hbid K hK).1, (hbid K hK).2, isIso_verdierDualDoubleDual_app Λ aX hK⟩,
      fun T hT ↦ exists_distTriang_derivedHom_left _ T hT, ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩,
    fun J ↦
      ⟨nonempty_iso_reductionModIdeal_leftDerivedUpperStar Λ f J,
        fun K M ↦ ⟨α_ K M _⟩, nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite Λ
          f J⟩⟩
  · -- (iii): the direct image bound of `sk-thm-sf-direct-image-tor-amplitude`
    obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
    have : NeZero N := ⟨hN0.ne'⟩
    have : IsNoetherianRing Λ := inferInstance
    exact torAmplitudeIn_rightDerivedLowerStar _ aX aY f hf d hd a b N
      (nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K) hNY hK hKt
  · -- (v): `Rf^! K ≅ 𝔻_X f^* 𝔻_Y K` and the duality bounds on `Y` and on `X`
    have hKc : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K := ⟨hK, a, b, hKt⟩
    obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f
      hf hKc
    have hD := torAmplitudeIn_verdierDual Λ aY dY hdY a b hK hKt
    have hfD := constructibleFiniteTor_leftDerivedUpperStar _ f
      (constructibleFiniteTor_verdierDual Λ aY hKc)
    have h := htvi dX hdX _ _ _ hfD.1 (hti _ _ _ hD)
    rw [neg_neg, neg_sub', neg_neg, sub_neg_eq_add] at h
    exact (torAmplitudeIn _ X _ _).prop_of_iso e.symm h

end Finite

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

include hϖ hI in
/-- Blueprint `proposition-six-operations-dctf`, clause (vii), integral coefficients.

Let `Λ` be a Noetherian domain complete for `I = (ϖ)` with `Λ ⧸ I` finite of exponent invertible
on the algebraically closed field `k` (the stage `𝒪_E`), and `f : X ⟶ Y` a separated
finite-type morphism of separated finite-type `k`-schemes. Then:

* `Dᵇc(X, Λ)` is the category of derived complete objects whose reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` are
  bounded constructible of Tor amplitude in one common interval, i.e. `Dᵇc(X, 𝒪_E) =
  Dᵇctf(X, 𝒪_E)` (`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`);
* the internal Hom preserves `Dᵇc(X, Λ)` and has the canonical finite reductions
  `RHom_Λ(K, L) ⊗ᴸ A_n ≅ RHom_{A_n}(K_n, L_n)` (`proposition-six-operations-dctf--15`,
  `proposition-six-operations-change-coefficients--7`);
* the derived limit `G_f L` of the finite exceptional inverse images of the reductions of
  `L ∈ Dᵇc(Y, Λ)` lies in `Dᵇc(X, Λ)`, is `Rf^! L` compatibly with the maps to the
  `Rf^!(L ⊗ᴸ A_n)`, and has these as its reductions.

These are the integral entries `AlgebraicGeometry.Etale.preservationMatrix_integral` of the
preservation matrix. -/
theorem boundedConstructibleIntegral_stability {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I X K ↔
        DerivedCategory.derivedComplete X.smallEtaleTopology I K ∧ ∃ a b : ℤ, ∀ n : ℕ,
          boundedConstructible (ModuleCat.{u + 1} Λ) X
              ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
              ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) ∧
    (∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I X K →
        DerivedCategory.boundedConstructibleIntegral I X L →
          DerivedCategory.boundedConstructibleIntegral I X
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L)) ∧
    (∀ (n : ℕ) (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (Kn Ln : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn)
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Ln),
      IsDerivedBaseChange η → IsDerivedBaseChange η' →
        Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
          (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
            (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op Kn)).obj Ln))) ∧
    ∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          (∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
          ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
            (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
              ((reductionModIdeal Λ Y (I ^ n)).obj L)) := by
  obtain ⟨-, hhom, -, hhomc, hexc, -, -⟩ := preservationMatrix_integral I hϖ hI aX aY f hf
  exact ⟨(exists_normalizedTower_and_boundedConstructibleIntegral_iff (I := I) (X := X)).2,
    hhomc, hhom, hexc⟩

end Integral

end Etale

end AlgebraicGeometry
