/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.BoundedConstructibleUpperShriek

/-!
# The exceptional adjunction at the integral and rational stages

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on a field `k` (the integral stage `Λ = 𝒪_E`, `I = 𝔪_E`), and `M` a submonoid
of `Λ` (the nonzero elements, or the powers of `ϖ`), so that the rational stage is
`Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[M⁻¹]` (`CategoryTheory.Rationalization`, blueprint
`proposition-inverting-ell--2`). For a separated finite-type morphism `f : X ⟶ Y` of
separated finite-type `k`-schemes this file constructs the compact-support direct image and the
exceptional inverse image on `Dᵇc(-, 𝒪_E)` and `Dᵇc(-, E)`, with the adjunction `Rf_! ⊣ Rf^!`:

* at the integral stage, `Rf_!` preserves `Dᵇc(-, 𝒪_E)` (blueprint
  `lemma-change-coefficients-compact-support`,
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerShriek`) and so does
  `Rf^!` (`AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedUpperShriek`), so that
  the adjunction `Rf_! ⊣ Rf^!` of `D(X_ét, Λ)` restricts to the constructible categories
  (`AlgebraicGeometry.Etale.boundedConstructibleIntegralLowerShriekUpperShriekAdjunction`);
* at the rational stage, the functors and the adjunction are the rationalizations of the integral
  ones (`AlgebraicGeometry.Etale.boundedConstructibleRationalLowerShriekUpperShriekAdjunction`),
  so that the rational `Rf_E^!` is right adjoint to the rational `Rf_{!,E}` with the localized
  units and counits;
* the rational `Rf_E^!` is computed by coefficient passage from the integral formula
  `Rf^! L ≅ 𝔻_X f^*_comp 𝔻_Y L`
  (`AlgebraicGeometry.Etale.nonempty_iso_boundedConstructibleRationalUpperShriek`).

## Implementation notes

The rational internal hom and the rational dualizing object are those obtained by coefficient
passage, that is the images under the localization functor of the integral ones; they are not
introduced as separate functors here, and the formula for `Rf_E^!` is stated on objects coming
from the integral stage, which are all the objects of `Dᵇc(X, E)`. The compatibilities of the
identifications with evaluations, units and counits under finite scalar extension are not
recorded.

The exceptional inverse images at both stages are
`AlgebraicGeometry.Etale.boundedConstructibleIntegralUpperShriek` and
`AlgebraicGeometry.Etale.boundedConstructibleRationalUpperShriek`. As there, the lower shrieks on
`D(-_ét, Λ)` along `f` and the structure morphisms are assumed to be left adjoints, which is how
`Rf^!` on `D(-_ét, Λ)` is defined.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_rationalOperations
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] (M : Submonoid Λ) {I : Ideal Λ}

section Integral

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}}

/-- Blueprint `lemma-change-coefficients-compact-support`: Integral compact support.

Let `f : X ⟶ Y` be a separated finite-type morphism of separated finite-type `k`-schemes and
`K ∈ Dᵇc(X, Λ)`, at the integral stage `Λ = 𝒪_E`, `I = (ϖ)`. Then `Rf_! K ∈ Dᵇc(Y, Λ)`, the
canonical compact-support coefficient comparison `(Rf_! K) ⊗ᴸ A_n ≅ Rf_{!,n} K_n` is an
isomorphism (read after restriction of scalars to `Λ`, where `Rf_{!,n} K_n` is `Rf_!(K ⊗ᴸ A_n)`),
and if `dim X ≤ d` and the reductions of `K` have Tor amplitude in `[a, b]`, those of `Rf_! K`
have Tor amplitude in `[a, b + 2d]`.

The coefficient comparison is proved here
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow`); the
constructibility and the Tor bound belong to the coefficient chapter. -/
theorem boundedConstructibleIntegral_rightDerivedLowerShriek {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [QuasiCompact f] [HasCompactification f] {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
      (∀ n : ℕ, IsIso ((rightDerivedLowerShriekReductionModIdealMap Λ (I ^ n)
        (HasCompactification.compactification f)).app K)) ∧
      ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  refine ⟨sorry, fun n ↦ ?_, sorry⟩
  subst hI
  have := isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow
    (HasCompactification.compactification f) hϖ n
  infer_instance

variable [hϖI : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]

variable (I) in
/-- The compact-support direct image `Rf_! : Dᵇc(X, Λ) ⥤ Dᵇc(Y, Λ)` at the integral stage, the
restriction of `Rf_!`
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerShriek`,
blueprint `lemma-change-coefficients-compact-support`). -/
noncomputable abbrev boundedConstructibleIntegralRightDerivedLowerShriek (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [QuasiCompact f] [HasCompactification f] :
    (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleIntegral I Y).FullSubcategory :=
  ObjectProperty.liftFullSubcategory _ _ (R(f)_![ModuleCat.{u + 1} Λ]) fun _ hK ↦
    have ⟨_, hϖ, hI⟩ := hϖI.out
    (boundedConstructibleIntegral_rightDerivedLowerShriek hϖ hI aX aY f hf hK).1

/-- The integral exceptional adjunction: the adjunction `Rf_! ⊣ Rf^!` of `D(X_ét, Λ)` restricts to
the integral constructible categories. -/
noncomputable def boundedConstructibleIntegralLowerShriekUpperShriekAdjunction
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    boundedConstructibleIntegralRightDerivedLowerShriek I aX aY f hf ⊣
      boundedConstructibleIntegralUpperShriek I aX aY f hf :=
  (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

end Integral

section Rational

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ]
  [Finite (Λ ⧸ I)] [hϖI : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
  [HasCompactification aX] [HasCompactification aY]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
  [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

variable (I) in
/-- The compact-support direct image `Rf_{!,E} : Dᵇc(X, E) ⥤ Dᵇc(Y, E)` at the rational stage,
induced by the integral `Rf_!`
(`AlgebraicGeometry.Etale.boundedConstructibleIntegralRightDerivedLowerShriek`). -/
noncomputable abbrev boundedConstructibleRationalRightDerivedLowerShriek :=
  Rationalization.map M (boundedConstructibleIntegralRightDerivedLowerShriek I aX aY f hf)

/-- Identification with the rational internal Hom and exceptional inverse image, the adjunction.

On the rationalized constructible categories `Dᵇc(-, E) = Dᵇc(-, 𝒪_E)[M⁻¹]`, the exceptional
inverse image `Rf_E^!` obtained by coefficient passage from the integral `Rf^!` is right adjoint
to the compact-support direct image `Rf_{!,E}`, with the localized units and counits: this is the
localization (`CategoryTheory.Rationalization.mapAdjunction`) of the integral adjunction
`AlgebraicGeometry.Etale.boundedConstructibleIntegralLowerShriekUpperShriekAdjunction`. -/
noncomputable def boundedConstructibleRationalLowerShriekUpperShriekAdjunction :
    boundedConstructibleRationalRightDerivedLowerShriek M I aX aY f hf ⊣
      boundedConstructibleRationalUpperShriek (M := M) I aX aY f hf :=
  Rationalization.mapAdjunction M
    (boundedConstructibleIntegralLowerShriekUpperShriekAdjunction (I := I) aX aY f hf)

/-- Identification with the rational internal Hom and exceptional inverse image, the dual formula
`Rf_E^! M ≅ 𝔻_{X,E} f^* 𝔻_{Y,E} M`.

Let `ω_X`, `ω_Y` be the integral dualizing complexes, the homotopy limits of the towers
`n ↦ Ra^!(Λ ⧸ Iⁿ)`, with `ω_X ∈ Dᵇc(X, 𝒪_E)`, so that the integral Verdier dual is
`𝔻_X = RHom(-, ω_X)` and the rational one is its image `𝔻_{X,E}`. For `L ∈ Dᵇc(Y, 𝒪_E)` and a
completed pullback `N ∈ Dᵇc(X, 𝒪_E)` of `𝔻_Y L` (a morphism `Lf^* 𝔻_Y L ⟶ N` inducing
isomorphisms on all reductions), the rational exceptional inverse image of the image of `L` in
`Dᵇc(Y, E)` is the image of `𝔻_X N` in `Dᵇc(X, E)`. It is the image of the integral formula
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`) under the
localization functor; every object of `Dᵇc(Y, E)` is the image of some `L`. -/
theorem nonempty_iso_boundedConstructibleRationalUpperShriek
    (L : (DerivedCategory.boundedConstructibleIntegral I Y).FullSubcategory)
    (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωX : Pretriangulated.IsHomotopyLimit ωX)
    (hωXc : DerivedCategory.boundedConstructibleIntegral I X ωX.pt)
    (ωY : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωY : Pretriangulated.IsHomotopyLimit ωY)
    (N : (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory)
    (φ : (L((f)^*[ModuleCat.{u + 1} Λ])).obj
      (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L.obj)).obj ωY.pt) ⟶ N.obj)
    (hφ : ∀ n : ℕ, IsIso ((reductionModIdeal Λ X (I ^ n)).map φ)) :
    ∃ hD : DerivedCategory.boundedConstructibleIntegral I X
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op N.obj)).obj ωX.pt),
      Nonempty ((boundedConstructibleRationalUpperShriek (M := M) I aX aY f hf).obj
          ((Rationalization.Q M _).obj L) ≅
        (Rationalization.Q M _).obj ⟨_, hD⟩) := by
  obtain ⟨ϖ, hϖ, hI⟩ := hϖI.out
  have hD := (boundedConstructibleIntegral_derivedHom I hϖ hI aX N.property hωXc).1
  refine ⟨hD, ?_⟩
  have hc := L.property.1.map (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint
  obtain ⟨e⟩ := (boundedConstructibleIntegral_exceptionalAdjoint I hϖ hI aX aY f hf L.property
    hc).2.2.1 ωX hωX ωY hωY N.obj φ N.property.1 hφ
  exact ⟨(Rationalization.mapFac M _).app L ≪≫
    (Rationalization.Q M _).mapIso (ObjectProperty.isoMk _ e)⟩

end Rational

end Etale

end AlgebraicGeometry
