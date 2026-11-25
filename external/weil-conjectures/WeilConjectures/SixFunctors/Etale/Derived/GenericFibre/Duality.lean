/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification

/-!
# The double dual on a geometric generic fibre

Let `S` be integral and of finite type over a field `k` (in the application `S = 𝔸¹_k`), with
invertible dualizing complex `ω_S`, let `t : T ⟶ S` lie over the generic point of `S` (in the
application `T = Spec \overline{k(t)}`), and let `X` be of finite type over `S` with base change
`g : X_T ⟶ X`. This file proves blueprint `lemma-double-dual-geometric-generic-fibre--1`, Zariski
locally on `X`, that is for `X ⟶ S` factored as a closed immersion `i : X ⟶ P` followed by a smooth
`p : P ⟶ S` (e.g. `P = 𝔸^r_S` for `X` affine):

- `AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic`:
  `Lg^* ω_X ≅ ω_{X_T} ⊗ᴸ L` with `L` invertible, `ω_X` relative to `Spec k` and `ω_{X_T}`
  relative to `T`;
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic`:
  for `K ∈ Dctf(X, Λ)`, `Lg^* δ_K` is an isomorphism if and only if `δ_{Lg^* K}` is.

## Proof

As in the blueprint, `ω_X ≅ ω_{X/S} ⊗ᴸ (i ≫ p)^* ω_S` with `ω_S` invertible
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp_of_isInvertible`), and
`ω_{X/S} ≅ Ri^! ω_p`. Closed-support generic exchange
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_generic`) gives
`g^* Ri^! ω_p ≅ Ri'^! g_P^* ω_p`, smooth base change gives `g_P^* ω_p ≅ ω_{p'}`, and
`Ri'^! ω_{p'} ≅ ω_{X_T/T}`. This is the first assertion, with `L = g^* (i ≫ p)^* ω_S`.
The second follows from the formal statement
`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff`, the
internal-hom comparisons at `(K, ω_X)` and `(𝔻_X K, ω_X)` being isomorphisms by the generic
internal-hom exchange (`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_generic`),
since `ω_X` is bounded constructible and `𝔻_X K ∈ Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField`).

## Implementation notes

The second statement takes the braided axiom `AlgebraicGeometry.Etale.LeftDerivedUpperStarBraided`
for `g` as a hypothesis; it holds by `AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lemma-double-dual-geometric-generic-fibre--1`, first assertion (Zariski
locally): **the dualizing complex of a generic fibre.**

Let `S` be integral and of finite type over a field `k`, with invertible dualizing complex
`ω_S` (e.g. `S = 𝔸¹_k`), let `Λ` be a finite ring whose exponent is invertible on `S`, and let
`t : T ⟶ S` be a morphism from a noetherian scheme lying over the generic point of `S` (e.g.
`T = Spec \overline{k(S)}`). Let `X ⟶ S` factor as a closed immersion `i : X ⟶ P` followed by
a smooth morphism `p : P ⟶ S` of relative dimension `r` (e.g. `P = 𝔸^r_S`, which is always
possible Zariski locally on `X`), and let `X' = X_T ⟶ P' = P_T ⟶ T` be the base change, with
`g : X' ⟶ X`. Then, with `ω_X` relative to `a_X : X ⟶ Spec k` and `ω_{X'}` relative to
`f_T : X' ⟶ T`,

`Lg^* ω_X ≅ ω_{X'} ⊗ᴸ L`

for an invertible `L`, namely `L = Lg^* L(i ≫ p)^* ω_S` (for `S = 𝔸¹_k`, `ω_S ≅ Λ(1)[2]`).
For `S` smooth over `k`, the hypothesis `hS` is
`AlgebraicGeometry.Etale.isInvertible_dualizingComplex`. The hypothesis that `S` be
quasi-separated, automatic for `S` of finite type over `k`, is that of smooth base change for
`p`. -/
theorem exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] [QuasiSeparatedSpace S] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasCompactification aS] [HasInvertibleExponent Λ S]
    (hS : DerivedCategory.isInvertible Λ S (dualizingComplex Λ aS))
    {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S) (ht : ∀ x, t.base x = genericPoint S)
    {P P' : Scheme.{u}} (p : P ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r p]
    [LocallyOfFiniteType p] [QuasiCompact p] [HasCompactification p] {gP : P' ⟶ P}
    {p' : P' ⟶ T} [HasCompactification p'] (sqP : IsPullback gP p' p t)
    {X X' : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i] [HasCompactification i]
    {g : X' ⟶ X} {i' : X' ⟶ P'} [IsClosedImmersion i'] [HasCompactification i']
    (sqX : IsPullback g i' i gP) [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (aX : X ⟶ Spec (.of k)) (hX : i ≫ p ≫ aS = aX) [HasCompactification aX] [QuasiCompact aX]
    (fT : X' ⟶ T) (hT : i' ≫ p' = fT) [HasCompactification fT] [QuasiCompact fT] :
    ∃ L : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.isInvertible Λ X' L ∧
      Nonempty ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aX) ≅
        ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj (dualizingComplex _ fT)).obj L) := by
  subst hX hT
  have : HasInvertibleExponent Λ P := .of_hom p
  -- `ω_X ≅ ω_{X/S} ⊗ᴸ (i ≫ p)^* ω_S`
  obtain ⟨e₁⟩ := nonempty_iso_dualizingComplex_comp_of_isInvertible Λ (i ≫ p) aS
    (i ≫ p ≫ aS) (Category.assoc _ _ _) hS
  -- `ω_{X/S} ≅ Ri^! ω_p`
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ i p
  -- `ω_{X'/T} ≅ Ri'^! ω_{p'}`
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ i' p'
  have : QuasiCompact p' := MorphismProperty.of_isPullback sqP inferInstance
  -- `g_P^* ω_p ≅ ω_{p'}`, smooth base change
  obtain ⟨e₄⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar Λ p r sqP
  -- the closed-support generic exchange `g^* Ri^! ω_p ≅ Ri'^! g_P^* ω_p`
  let U := openComplementOfIsClosedImmersion i
  have sqU := IsPullback.of_hasPullback U.ι gP
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    simp [U, openComplementOfIsClosedImmersion]
  have hij' : Disjoint (Set.range i'.base) (Set.range (pullback.snd U.ι gP).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have h₁ : i.base (g.base x) = gP.base (i'.base x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sqX.w]
    have h₂ : U.ι.base ((pullback.fst U.ι gP).base y) =
        gP.base ((pullback.snd U.ι gP).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sqU.w]
    have hm : i.base (g.base x) ∈ Set.range i.base := ⟨_, rfl⟩
    rw [hij, h₁, ← hy, ← h₂] at hm
    exact hm ⟨_, rfl⟩
  have hU : boundedConstructible (ModuleCat.{u + 1} Λ) S (𝟙_ _) :=
    (boundedConstructible _ S).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0)
  have hM : boundedConstructible (ModuleCat.{u + 1} Λ) P (dualizingComplex _ p) :=
    boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ p r hU
  have hβ := isIso_rightDerivedUpperShriekBaseChangeMap_app_of_generic Λ aS t ht p sqP sqX sqU
    hij hij' hM
  let e₅ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ (i ≫ p)) ≅
      dualizingComplex _ (i' ≫ p') :=
    (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso e₂.symm ≪≫
      asIso ((rightDerivedUpperShriekBaseChangeMap Λ sqX).app (dualizingComplex _ p)) ≪≫
      (R(i')^![Λ]).mapIso
        (e₄.app (𝟙_ _) ≪≫ (R(p')^![Λ]).mapIso
          (leftDerivedUpperStarUnitIso _ t)) ≪≫ e₃
  refine ⟨(L((g)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((i ≫ p)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aS)),
    (hS.leftDerivedUpperStar (i ≫ p)).leftDerivedUpperStar g, ⟨?_⟩⟩
  exact (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso e₁ ≪≫ leftDerivedUpperStarTensorIso _ g _ _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X').mapIso e₅).app _

/-- Blueprint `lemma-double-dual-geometric-generic-fibre--1`, second assertion (Zariski
locally): **the double dual on a geometric generic fibre.**

In the setting of
`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic` (`S`
integral of finite type over `k` with `ω_S` invertible, `t : T ⟶ S` over the generic point, and
`X ⟶ S` factored as a closed immersion `i : X ⟶ P` followed by a smooth `p : P ⟶ S`, with base
change `g : X' ⟶ X`), let `X` be separated over `k`. For every `K ∈ Dctf(X, Λ)`, the pullback
`Lg^* δ_K` of the double-dual map relative to `a_X : X ⟶ Spec k` is an isomorphism if and only
if the double-dual map `δ_{Lg^* K}` relative to `f_T : X' ⟶ T` is. For `T = Spec` of an
algebraic closure of the function field of `S`, the latter is the double-dual map of the
geometric generic fibre over its base field.

The hypothesis `hbr`, that `Lg^*` is braided for the derived braidings, is
`AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`. -/
theorem isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic {k : Type u}
    [Field k] [PerfectField k] [HasInvertibleExponent Λ (Spec (.of k))]
    {S : Scheme.{u}} [IsIntegral S] [QuasiSeparatedSpace S] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasCompactification aS] [HasInvertibleExponent Λ S]
    (hS : DerivedCategory.isInvertible Λ S (dualizingComplex Λ aS))
    {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S) (ht : ∀ x, t.base x = genericPoint S)
    {P P' : Scheme.{u}} (p : P ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r p]
    [LocallyOfFiniteType p] [QuasiCompact p] [HasCompactification p] {gP : P' ⟶ P}
    {p' : P' ⟶ T} [HasCompactification p'] (sqP : IsPullback gP p' p t)
    {X X' : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i] [HasCompactification i]
    {g : X' ⟶ X} {i' : X' ⟶ P'} [IsClosedImmersion i'] [HasCompactification i']
    (sqX : IsPullback g i' i gP) [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (aX : X ⟶ Spec (.of k)) (hX : i ≫ p ≫ aS = aX) [HasCompactification aX] [QuasiCompact aX]
    [IsSeparated aX] [LocallyOfFiniteType aX]
    (fT : X' ⟶ T) (hT : i' ≫ p' = fT) [HasCompactification fT] [QuasiCompact fT]
    (hbr : LeftDerivedUpperStarBraided (ModuleCat.{u + 1} Λ) g)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual Λ aX).app K)) ↔
      IsIso ((verdierDualDoubleDual Λ fT).app
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic Λ aS hS t ht
    p r sqP i sqX aX hX fT hT
  have hXp : IsPullback g fT (i ≫ p) t := by
    subst hT
    exact sqX.paste_vert sqP
  have hUk : boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) (𝟙_ _) :=
    (boundedConstructible _ _).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0)
  have hω : boundedConstructible (ModuleCat.{u + 1} Λ) X (dualizingComplex _ aX) :=
    boundedConstructible_rightDerivedUpperShriek Λ (𝟙 (Spec (.of k))) aX hUk
  have h₁ := isIso_derivedHomUpperStarComparison_of_generic Λ aS t ht (i ≫ p) hXp hK hω
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  have hD := (constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField Λ aX d hd a b
    hKbc hKt).1
  have h₂ := isIso_derivedHomUpperStarComparison_of_generic Λ aS t ht (i ≫ p) hXp hD hω
  exact isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff Λ aX fT g
    hbr ((isInvertible_iff_exists_derivedTensor _).2 hL) e K h₁ h₂

end Etale

end AlgebraicGeometry
