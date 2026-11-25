/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekTriangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EssentiallySmall
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizingLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# The exceptional inverse image on `Loc(Dctf)`, finite coefficients

Let `Λ` be a finite commutative ring and `k` a field which is finite or separably closed, so
that `cd_ℓ(k)` is finite (the standing base field of the blueprint). For a scheme `X` the
localizing closure `Loc(Dctf(X, Λ))` (blueprint `definition-localizing-subcategory`) is the smallest
triangulated subcategory of `D(X_proét, Λ)` containing `Dctf(X, Λ)` and closed under direct sums
(`AlgebraicGeometry.ProEtale.DerivedCategory.localizingConstructibleFiniteTor`). It is
pretriangulated and has direct sums, computed in `D(X_proét, Λ)`.

For a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f : X ⟶ Y`, the functor
`Rf_!(c) = Rp_* ∘ j_!` restricts to a triangulated functor
`Rf_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekLocalizing`), which preserves direct sums.
By Brown representability it has a right adjoint
`f^! : Loc(Dctf(Y, Λ)) ⥤ Loc(Dctf(X, Λ))`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizing`), which is triangulated, preserves
direct sums and is unique up to unique isomorphism (blueprint
`theorem-existence-exceptional-inverse-image`,
`AlgebraicGeometry.ProEtale.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`).

The finite coefficient rings `A` of the blueprint are those whose exponent is invertible on the
schemes (`AlgebraicGeometry.HasInvertibleExponent`); the schemes are of finite type and separated
over `k`. The compactness of the generators needs `k` to have finite cohomological dimension for
`Λ`-modules (`hk`): over `ℝ`, `Λ = 𝔽₂`, the coproduct of the shifts `Λ[n]` is also their product,
and `Hom(Λ, ∏ₙ Λ[n]) = ∏ₙ Hⁿ(ℝ, 𝔽₂)` is not a direct sum, so `Λ` is not compact.

## Inputs

- `ProEtale.DerivedCategory.compactlyGeneratesLocalizingClosure_constructibleFiniteTor`
  (blueprint `lemma-hypotheses-brown-representability`): `Loc(Dctf(X, Λ))` has split idempotents,
  and `Dctf(X, Λ)` is essentially small and compactly generates `Loc(Dctf(X, Λ))`. Essential
  smallness is `AlgebraicGeometry.ProEtale.DerivedCategory.exists_skeleton_constructibleFiniteTor`,
  compactness is
  `AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_of_constructibleFiniteTor`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.localizingConstructibleFiniteTor_lowerShriek`
  (blueprint `proposition-construction-independence-rf-shriek`): `Rf_!(c)` maps `Loc(Dctf(X, Λ))`
  into `Loc(Dctf(Y, Λ))` and `Dctf(X, Λ)` into `Dctf(Y, Λ)`, and preserves direct sums of objects of
  `Loc(Dctf(X, Λ))`; see
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizingLowerShriek`.

Everything else is the abstract theory of
`WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `definition-localizing-subcategory`: the localizing closure `Loc(Dctf(X, Λ))`, the
smallest triangulated subcategory of `D(X_proét, Λ)` closed under isomorphisms and direct sums which
contains `Dctf(X, Λ)`, for a finite coefficient ring `Λ`. -/
noncomputable abbrev DerivedCategory.localizingConstructibleFiniteTor (X : Scheme.{u}) :
    ObjectProperty
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure

/-- The category `Loc(Dctf(X, Λ))`, a full subcategory of `D(X_proét, Λ)`. It is
pretriangulated and has direct sums. -/
abbrev DerivedCategoryLocalizingFiniteTor (X : Scheme.{u}) : Type _ :=
  (DerivedCategory.localizingConstructibleFiniteTor Λ X).FullSubcategory

variable {k : Type u} [Field k]

/-- Blueprint `lemma-hypotheses-brown-representability`: Hypotheses of Brown representability, for a
finite coefficient ring `Λ` whose exponent is invertible on a separated finite-type `k`-scheme `X`.
The category `Loc(Dctf(X, Λ))` is locally small, triangulated and has direct sums (by
construction); it has split idempotents, and `Dctf(X, Λ)` is essentially small, with a small
skeleton forming a set of compact generators of `Loc(Dctf(X, Λ))`. The base field `k` has finite
cohomological dimension for `Λ`-modules (`hk`), as in the blueprint, where `k` is finite or
algebraically closed. -/
theorem DerivedCategory.compactlyGeneratesLocalizingClosure_constructibleFiniteTor
    (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] [HasInvertibleExponent Λ X] :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ)
        X).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (DerivedCategoryLocalizingFiniteTor Λ X) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  have : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K hK ↦ hK.shift n⟩⟩
  exact ⟨ObjectProperty.CompactlyGeneratesLocalizingClosure.of_isStableUnderShift
      (DerivedCategory.exists_skeleton_constructibleFiniteTor Λ X)
      (fun C hC ↦ DerivedCategory.isCompactObj_of_constructibleFiniteTor hk aX C hC),
    ObjectProperty.isIdempotentComplete_localizingClosure _⟩

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compact support along one
compactification on the localizing category, for a finite coefficient ring `Λ` whose exponent is
invertible on a quasi-compact quasi-separated scheme `Y` of finite type over a field `k`. For a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, the functor `Rp_* ∘ j_! = Rf_!(c)` (triangulated)
maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(Y, Λ))` and `Dctf(X, Λ)` into `Dctf(Y, Λ)`, and its
restriction to `Loc(Dctf(X, Λ))` preserves direct sums.

The finiteness hypothesis `aY` is needed: over an arbitrary quasi-compact quasi-separated `Y`
the direct image along a proper morphism need not preserve constructibility (for a closed point
`z` of `Spec ∏ₙ 𝔽_{pₙ}` which is not open, the closed immersion of `z` is proper, and the
extension by zero of `Λ` from `z` has non-constructible support). -/
theorem DerivedCategory.localizingConstructibleFiniteTor_lowerShriek
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] [HasInvertibleExponent Λ Y]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    {f : X ⟶ Y} (c : Compactification f) :
    (∀ K, DerivedCategory.localizingConstructibleFiniteTor Λ X K →
      DerivedCategory.localizingConstructibleFiniteTor Λ Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) ∧
    (∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) ∧
    ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.localizingConstructibleFiniteTor Λ X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) :=
  ⟨localizingClosure_rightDerivedLowerShriekOfCompactification_obj Λ aY c,
    fun _ hK ↦ constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c hK,
    preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification Λ aY c⟩

/-- `AlgebraicGeometry.ProEtale.DerivedCategory.localizingConstructibleFiniteTor_lowerShriek`
for a separated finite-type `k`-scheme `Y`, which is quasi-compact and quasi-separated. -/
theorem DerivedCategory.localizingConstructibleFiniteTor_lowerShriek_of_finiteType
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f) :
    (∀ K, DerivedCategory.localizingConstructibleFiniteTor Λ X K →
      DerivedCategory.localizingConstructibleFiniteTor Λ Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) ∧
    (∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) ∧
    ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.localizingConstructibleFiniteTor Λ X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) :=
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have := quasiSeparatedSpace_of_quasiSeparated aY
  DerivedCategory.localizingConstructibleFiniteTor_lowerShriek Λ aY c

section LowerShriek

variable {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)

/-- The compact-support direct image `Rf_! = Rp_* ∘ j_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))` on
the localizing closures, attached to a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`: the
restriction of `Rf_!(c)` (blueprint `proposition-construction-independence-rf-shriek`). -/
noncomputable abbrev rightDerivedLowerShriekLocalizing :
    DerivedCategoryLocalizingFiniteTor Λ X ⥤ DerivedCategoryLocalizingFiniteTor Λ Y :=
  ObjectProperty.localizingClosureLift _ _
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
    (DerivedCategory.localizingConstructibleFiniteTor_lowerShriek_of_finiteType
      Λ aY c).1

/-- `Rf_!` on the localizing closures is compatible with the inclusions into the derived
categories. -/
noncomputable def rightDerivedLowerShriekLocalizingCompιIso :
    rightDerivedLowerShriekLocalizing Λ aY c ⋙
        (DerivedCategory.localizingConstructibleFiniteTor Λ Y).ι ≅
      (DerivedCategory.localizingConstructibleFiniteTor Λ X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c :=
  ObjectProperty.localizingClosureLiftCompιIso _ _ _ _

/-- `Rf_!` on the localizing closures preserves direct sums (blueprint
`proposition-construction-independence-rf-shriek`). -/
instance (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedLowerShriekLocalizing Λ aY c) :=
  have := (DerivedCategory.localizingConstructibleFiniteTor_lowerShriek_of_finiteType
    Λ aY c).2.2 J
  ObjectProperty.preservesColimitsOfShape_localizingClosureLift _ _ _ _ J

end LowerShriek

section UpperShriek

variable (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] [HasInvertibleExponent Λ X]
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)

include hk aX in
/-- Blueprint `theorem-existence-exceptional-inverse-image` (1):
`Rf_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))` is a left adjoint, by Brown representability. -/
theorem isLeftAdjoint_rightDerivedLowerShriekLocalizing :
    (rightDerivedLowerShriekLocalizing Λ aY c).IsLeftAdjoint :=
  have := (DerivedCategory.localizingConstructibleFiniteTor_lowerShriek_of_finiteType
    Λ aY c).2.2
  ObjectProperty.isLeftAdjoint_localizingClosureLift _ _ _ _
    (DerivedCategory.compactlyGeneratesLocalizingClosure_constructibleFiniteTor Λ hk aX).1

include hk aX in
/-- Blueprint `theorem-existence-exceptional-inverse-image`: the exceptional inverse image
`f^! : Loc(Dctf(Y, Λ)) ⥤ Loc(Dctf(X, Λ))` attached to a compactification `c` of `f`, a right
adjoint of `Rf_!` (Brown representability). It is an arbitrary choice of right adjoint, unique
up to unique isomorphism (`Adjunction.existsUnique_iso_comp_counit`); only the adjunction
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizingAdjunction` should be used about
it. -/
noncomputable def rightDerivedUpperShriekLocalizing :
    DerivedCategoryLocalizingFiniteTor Λ Y ⥤ DerivedCategoryLocalizingFiniteTor Λ X :=
  have := isLeftAdjoint_rightDerivedLowerShriekLocalizing Λ hk aX aY c
  (rightDerivedLowerShriekLocalizing Λ aY c).rightAdjoint

/-- Blueprint `theorem-existence-exceptional-inverse-image` (1): the adjunction `Rf_! ⊣ f^!` on the
localizing closures, `Hom(Rf_! M, N) ≃ Hom(M, f^! N)`. -/
noncomputable def rightDerivedUpperShriekLocalizingAdjunction :
    rightDerivedLowerShriekLocalizing Λ aY c ⊣ rightDerivedUpperShriekLocalizing Λ hk aX aY c :=
  have := isLeftAdjoint_rightDerivedLowerShriekLocalizing Λ hk aX aY c
  Adjunction.ofIsLeftAdjoint _

/-- `f^!` commutes with shifts, as a right adjoint of the functor `Rf_!` which commutes with
shifts. -/
noncomputable instance : (rightDerivedUpperShriekLocalizing Λ hk aX aY c).CommShift ℤ :=
  (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).rightAdjointCommShift ℤ

/-- The adjunction `Rf_! ⊣ f^!` is compatible with the shifts. -/
instance : (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).CommShift ℤ :=
  (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).commShift_of_leftAdjoint ℤ

/-- Blueprint `theorem-existence-exceptional-inverse-image` (2): `f^!` is triangulated. -/
instance : (rightDerivedUpperShriekLocalizing Λ hk aX aY c).IsTriangulated :=
  (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).isTriangulated_rightAdjoint

include hk aX in
/-- Blueprint `theorem-existence-exceptional-inverse-image--4`: `f^!` preserves direct sums, since
`Rf_!` maps the compact generators `Dctf(X, Λ)` to compact objects `Dctf(Y, Λ)` of
`Loc(Dctf(Y, Λ))`. -/
instance (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedUpperShriekLocalizing Λ hk aX aY c) :=
  have h := DerivedCategory.localizingConstructibleFiniteTor_lowerShriek_of_finiteType
    Λ aY c
  have := h.2.2
  ObjectProperty.preservesColimitsOfShape_of_localizingClosureLift_adjunction _ _ _ _
    (DerivedCategory.compactlyGeneratesLocalizingClosure_constructibleFiniteTor Λ hk aX).1
    (DerivedCategory.compactlyGeneratesLocalizingClosure_constructibleFiniteTor Λ hk aY).1 h.2.1
    (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c) J

include hk aX in
/-- Blueprint `theorem-existence-exceptional-inverse-image`: Existence of the exceptional inverse
image, for a finite coefficient ring `Λ` whose exponent is invertible on separated finite-type
`k`-schemes `X`, `Y`, over a field `k` which is finite or separably closed.
For a compactification `c` of `f : X ⟶ Y`, the coproduct-preserving functor
`Rf_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))` has a right adjoint `f^!`, which commutes with
shifts compatibly with the adjunction, is exact (triangulated), preserves direct sums and is
unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing :
    ∃ (G : DerivedCategoryLocalizingFiniteTor Λ Y ⥤ DerivedCategoryLocalizingFiniteTor Λ X)
      (adj : rightDerivedLowerShriekLocalizing Λ aY c ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : DerivedCategoryLocalizingFiniteTor Λ Y ⥤ DerivedCategoryLocalizingFiniteTor Λ X)
        (adj' : rightDerivedLowerShriekLocalizing Λ aY c ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing Λ aY c).map (e.hom.app N) ≫
          adj'.counit.app N = adj.counit.app N :=
  ⟨_, rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c, inferInstance, inferInstance,
    inferInstance, fun _ ↦ inferInstance,
    fun _ ↦
      (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).existsUnique_iso_comp_counit⟩

end UpperShriek

end AlgebraicGeometry.ProEtale
