/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary

/-!
# Detection by a proper direct image

Let `b : Y ⟶ S` be proper and let `a : G ⟶ Y` be an open immersion whose closed complement is
finite over `S`. A bounded below complex on `Y` is bounded constructible, and a morphism of
complexes on `Y` is an isomorphism, as soon as this holds over `G` and after `Rb_*`.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_and_isIso_of_upperStar_of_rightDerivedLowerStar`

## Implementation details

The source takes the closed complement of `G` reduced and coefficients in `𝔽_ℓ`; here any closed
subscheme structure on the complement and any finite coefficient ring `Λ` whose exponent is
invertible on `S` are allowed.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Let `S` be of finite type over a field `k`, let `Λ` be a finite ring whose exponent is
invertible on `S`, let `b : Y ⟶ S` be proper, and let `a : G ⟶ Y` be an open immersion with
closed complement `i : Z ⟶ Y` such that `i ≫ b` is finite. Then:

1. a bounded below complex `K` on `Y` such that `a^* K` and `Rb_* K` are bounded constructible
   is bounded constructible;
2. a morphism `c` such that `a^* c` and `Rb_* c` are isomorphisms is an isomorphism. -/
theorem boundedConstructible_and_isIso_of_upperStar_of_rightDerivedLowerStar [Finite Λ]
    {k : Type u} [Field k] {S Y G Z : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [HasInvertibleExponent Λ S] (b : Y ⟶ S)
    [IsProper b] (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hai : Set.range i = (Set.range a)ᶜ) [IsFinite (i ≫ b)] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∃ n : ℤ, K.IsGE n) →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) G
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K) →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
        ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K) →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) ∧
    ∀ {K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (c : K ⟶ L), IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.map c) →
      IsIso ((R((b)_*[ModuleCat.{u + 1} Λ])).map c) → IsIso c :=
  ⟨fun K hK ha hb ↦
    boundedConstructible_of_upperStar_of_rightDerivedLowerStar Λ aS b a i hai K hK ha hb,
   fun c ha hb ↦ isIso_of_isIso_upperStar_map_of_isIso_rightDerivedLowerStar_map Λ b a i hai c
    ha hb⟩


end Etale

end AlgebraicGeometry
