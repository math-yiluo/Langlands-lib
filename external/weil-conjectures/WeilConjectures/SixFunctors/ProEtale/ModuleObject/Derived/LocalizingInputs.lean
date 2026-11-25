/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperPadicSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbientIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic
import WeilConjectures.Tactic.ExactModProofs

/-!
# Inputs from other subsections for the projection formula on `Loc(Dbc)`

The projection formula and proper base change on the localizing categories `Loc(Dbc(-, Λ))`
for the `ℓ`-adic coefficient rings `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` (blueprint
`lemma-projection-formula-integral-coefficients`,
`proposition-projection-formula-rational-coefficients`) rest on the following statements of other
subsections of the blueprint, stated here for the module objects over `Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`. Each theorem carries the blueprint id of the
node it formalises and states that node for one coefficient ring; the docstring lists the clauses of
the node which are not stated, for lack of the relevant notions for module objects. They are not
proved here, except that `proposition-six-operations-dctf--14` and
`proposition-direct-image-along-open-immersion` are deduced from the general statements
`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`, and that
the proper direct image maps `Loc(Dbc)` into `Loc(Dbc)` and preserves direct sums there is deduced
from `properLowerStarHypotheses_padicIntegersRingObj`,
`properLowerStarHypotheses_continuousMapRingObj` and `properLowerStarHypotheses_padicAlgClRingObj`
(`localizingBoundedConstructible_rightDerivedLowerStar_of_properLowerStarHypotheses`).

* `proposition-six-operations-dctf--14`: `⊗ᴸ` preserves bounded constructible complexes;
* `proposition-proper-direct-image-constructible-complexes`: proper
  direct image, proper base change and the projection formula on `Dbc(-, Λ)`;
* `proposition-compactness-proper-direct-image--2`,
`proposition-proper-direct-image-extension-zero`: the proper direct
  image maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there (and so does
  the extension by zero along an open immersion);
* `proposition-proper-base-change-localizing-categories--1`: proper
  base change on the localizing categories;
* `proposition-direct-image-along-open-immersion`: the direct image along a quasi-compact open
immersion preserves
  `Dbc(-, Λ)`.

## The setting

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes
are separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(blueprint `sk-def-sfb-dc-setting`), and the functors are those of the underlying morphisms of
schemes. The coefficient rings are the condensed rings `𝒪̲_E = Profinite.padicIntegersRingObj ℓ E`
(for a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`), `E̲ = Profinite.continuousMapRingObj E` (for a finite
subextension `E` of `ℚ̄_ℓ / ℚ_ℓ`, `E : PadicAlgCl.FiniteIntermediateField ℓ`) and
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻[" Λ "](" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- Blueprint `proposition-proper-direct-image-extension-zero` (formal part): if `Rp_*` has the
properties `ProperLowerStarHypotheses` (it maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧`, and its restriction to
`Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums), then `Rp_*` maps `Loc(Dᵇc(Z)⟦Λ⟧)` into
`Loc(Dᵇc(Y)⟦Λ⟧)` and preserves direct sums on `Loc(Dᵇc(Z)⟦Λ⟧)`. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_of_properLowerStarHypotheses
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {Z Y : Scheme.{u}} {p : Z ⟶ Y} (hp : ProperLowerStarHypotheses Λ p) :
    (∀ M, localizingBoundedConstructible Λ Z M →
      localizingBoundedConstructible Λ Y ((R((p)_*⟦Λ⟧)).obj M)) ∧
    (R((p)_*⟦Λ⟧)).PreservesCoproductsOn.{u + 1} (localizingBoundedConstructible Λ Z) := by
  let P := localizingBoundedConstructible Λ Z
  have hsum : (R((p)_*⟦Λ⟧)).PreservesCoproductsOn.{u + 1} P := by
    intro J K c hc hK
    let A : Discrete J ⥤ P.FullSubcategory := P.lift K hK
    let cA : Cocone A :=
      { pt := ⟨c.pt, P.prop_of_isColimit hc hK⟩
        ι :=
          { app := fun j ↦ ObjectProperty.homMk (c.ι.app j)
            naturality := fun i j f ↦ by
              apply ObjectProperty.hom_ext
              exact c.ι.naturality f } }
    have hcA' : IsColimit (P.ι.mapCocone cA) :=
      hc.ofIsoColimit (Cocone.ext (Iso.refl _) (fun j ↦ by simp [A, cA]))
    have hcA : IsColimit cA := isColimitOfReflects P.ι hcA'
    have := hp.2 J
    exact ⟨(isColimitOfPreserves (P.ι ⋙ R((p)_*⟦Λ⟧)) hcA).ofIsoColimit
      (Cocone.ext (Iso.refl _) (fun j ↦ by simp [A, cA]))⟩
  exact ⟨fun M hM ↦ ObjectProperty.localizingClosure_map (boundedConstructible
      (condensedRingObj Λ Z)) (boundedConstructible (condensedRingObj Λ Y)) R((p)_*⟦Λ⟧) hsum
      (fun K hK ↦ le_localizingBoundedConstructible Λ Y _ (hp.1 K hK)) hM, hsum⟩

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k

/-! ### The integral coefficient ring `𝒪̲_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- Blueprint `proposition-six-operations-dctf--14`: `⊗ᴸ` preserves bounded constructible complexes
(`ℓ`-adic `Λ`), stated for `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` by one declaration each; the case `Λ = 𝒪̲_E`.
If `K, L ∈ D(Mod_{𝒪_{E,X}})` are bounded constructible, then
so is `K ⊗ᴸ_{𝒪_{E,X}} L`. -/
theorem boundedConstructible_tensor_padicIntegersRingObj
    {K L : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      (K ⊗ L) :=
  ObjectProperty.prop_tensor hK hL

/-- Blueprint `proposition-proper-direct-image-constructible-complexes`: Proper direct image, base
change and projection formula for `𝒪_E`. Let `p : X ⟶ Y` be proper.

1. For `K ∈ Dbc(X, 𝒪_E)`, `Rp_*K` is derived `π_E`-complete, and
   `(Rp_*K) ⊗ᴸ 𝒪_{E,Y}/π_E ≃ Rp_*(K ⊗ᴸ 𝒪_{E,X}/π_E)`; hence `Rp_*K ∈ Dbc(Y, 𝒪_E)`.
2. (Derived Nakayama.) A derived `π_E`-complete `C` with `C ⊗ᴸ 𝒪_E/π_E = 0` is zero.
3. The proper base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` (for a cartesian square
   `g' ≫ p = p' ≫ g`) and the projection formula map `Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` are
   isomorphisms for `K ∈ Dbc(X, 𝒪_E)` and `M ∈ Dbc(Y, 𝒪_E)`.

Stated here: the conclusion `Rp_*K ∈ Dbc(Y, 𝒪_E)` of (1), and (3). Not stated: the derived
completeness and the reduction formula of (1), and (2): derived completeness and reduction
modulo `π_E` (`definition-derived-adic-completeness`) are not available for module objects over
`𝒪_{E,X}`. -/
theorem properDirectImage_baseChange_projectionFormula_padicIntegersRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K →
        boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
          ((R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K)) ∧
    (∀ {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' p' p g)
      (K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K →
        IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
          ((Over.forget _).map_commSq sq.toCommSq)).app K)) ∧
    (∀ (K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left))
      (M : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](Y.left)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K →
        boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left) M →
          IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E) p.left).app K).app M)) :=
  ⟨fun K hK ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E p ⟨K, hK⟩,
    fun sq K hK ↦ isIso_baseChangeMap_app_padicIntegers_of_isProper ℓ E sq
      ((Over.forget _).map_commSq sq.toCommSq) rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl K hK,
    fun K M hK hM ↦
      isIso_projectionMap_padicIntegersRingObj_of_boundedConstructible ℓ E p K M hK hM⟩

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- Blueprint `proposition-compactness-proper-direct-image--2`: Integral proper direct image on the
localizing categories. Let `p : X ⟶ Y` be proper, with fibres of dimension `≤ d`.

1. For `N ∈ Cons(X, 𝒪_E)`, `Rp_*N ∈ Dbc(Y, 𝒪_E)` has cohomology in degrees `[0, 2d + 1]`; for
   `N ∈ IndCons(X, 𝒪_E)`, `H^q Rp_*N ∈ IndCons(Y, 𝒪_E)` and vanishes outside `[0, 2d + 1]`.
2. For `K ∈ Dic(X, 𝒪_E)`, `H^q Rp_*K` depends only on the degrees `[q - 2d - 1, q]` of `K`, and
   `Rp_*` commutes with arbitrary direct sums of objects of `Dic(X, 𝒪_E)`.
3. `Rp_*` maps `Loc(Dbc(X, 𝒪_E))` into `Loc(Dbc(Y, 𝒪_E))` and preserves direct sums there.

Stated here: (3), which does not involve `d`. Not stated: (1) and (2), which are about the
ind-constructible sheaves `IndCons(-, 𝒪_E)` and the complexes `Dic(-, 𝒪_E)` with
ind-constructible cohomology, not available for module objects over `𝒪_{E,X}`. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ M, localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left M →
      localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y.left
        ((R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj M)) ∧
    (R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).PreservesCoproductsOn.{u + 1}
      (localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left) :=
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  localizingBoundedConstructible_rightDerivedLowerStar_of_properLowerStarHypotheses
    (properLowerStarHypotheses_padicIntegersRingObj ℓ E Y.hom p.left)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- Blueprint `proposition-proper-base-change-localizing-categories--1`: Extending proper base
change from `Dctf` to the localizing closure; the case `Λ = 𝒪̲_E` (for which `Dctf = Dbc`): for a
cartesian square `g' ≫ p = p' ≫ g` with `p` proper, if the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K`
is an isomorphism for every `K ∈ Dbc(X, 𝒪_E)`, then it is an isomorphism for every
`K ∈ Loc(Dbc(X, 𝒪_E))`. -/
theorem isIso_baseChangeMap_of_localizing_padicIntegersRingObj {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    (h : ∀ K, boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      K → IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
        ((Over.forget _).map_commSq sq.toCommSq)).app K))
    {K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
      ((Over.forget _).map_commSq sq.toCommSq)).app K) := by
  have : IsProper p'.left :=
    MorphismProperty.of_isPullback (P := @IsProper) (sq.map (Over.forget _)) ‹IsProper p.left›
  have h₁ := (localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj ℓ E p).2
  have h₂ := (localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj ℓ E p').2
  exact isIso_baseChangeMap_of_localizingBoundedConstructible
    (Profinite.padicIntegersRingObj ℓ E) ((Over.forget _).map_commSq sq.toCommSq) h₁ h₂
    (fun K hK ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g'.left K hK) h hK

/-- Blueprint `proposition-direct-image-along-open-immersion`: Direct image along an open immersion;
the case `Λ = 𝒪̲_E`: for a quasi-compact open immersion `j : U ⟶ X`, `Rj_*` maps `Dbc(U, 𝒪_E)` into
`Dbc(X, 𝒪_E)`. The node states this for `Λ = 𝒪_E, E, ℚ̄_ℓ`, by one declaration each. -/
theorem boundedConstructible_rightDerivedLowerStar_openImmersion_padicIntegersRingObj
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
    {K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
      ((R((j.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) :=
  PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E j ⟨K, hK⟩

end Integers


/-! ### The coefficient ring E̲ -/

section Field

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

set_option hygiene false in
/-- The condensed field `E̲`. -/
local notation "𝐄" => Profinite.continuousMapRingObj.{u} E

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- Blueprint `proposition-six-operations-dctf--14`: `⊗ᴸ` preserves bounded constructible complexes
(`ℓ`-adic `Λ`), stated for `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` by one declaration each; the case `Λ = E̲`.
If `K, L ∈ D(Mod_{Λ_X})` are bounded constructible, then
so is `K ⊗ᴸ_{Λ_X} L`. -/
theorem boundedConstructible_tensor_continuousMapRingObj
    {K L : 𝔻[𝐄](X.left)}
    (hK : boundedConstructible (condensedRingObj 𝐄 X.left) K)
    (hL : boundedConstructible (condensedRingObj 𝐄 X.left) L) :
    boundedConstructible (condensedRingObj 𝐄 X.left) (K ⊗ L) :=
  ObjectProperty.prop_tensor hK hL

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsSeparated Y'.hom] in
/-- Blueprint `proposition-proper-direct-image-constructible-complexes`: Proper direct image, base
change and projection formula for `E` and `ℚ̄_ℓ`; the case `Λ = E̲`. Let `p : X ⟶ Y` be proper.

1. For `K ∈ D(X_proét, 𝒪_E)` bounded below, `Rp_*(K[1/ℓ]) ≃ (Rp_*K)[1/ℓ]`; for
   `K ∈ D(X_proét, E)` bounded below and `F/E` finite, `Rp_*(K_F) ≃ (Rp_*K)_F` and
   `Rp_*(K_{ℚ̄_ℓ}) ≃ (Rp_*K)_{ℚ̄_ℓ}`, via the canonical maps.
2. `Rp_*` maps `Dbc(X, Λ)` into `Dbc(Y, Λ)`.
3. The proper base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` (for a cartesian square
   `g' ≫ p = p' ≫ g`) and the projection formula map `Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` are
   isomorphisms for `K ∈ Dbc(X, Λ)` and `M ∈ Dbc(Y, Λ)`.

Stated here: (2) and (3), for `Λ = E̲`. Not stated: the comparisons (1) of the direct image
with the changes of coefficients `𝒪_E → E`, `E → F`, `E → ℚ̄_ℓ` on bounded below complexes;
the comparison maps `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom` are defined only
for an exact extension of scalars; exactness is not available for `𝒪_{E,X} ⟶ E_X`, and for
`E_X ⟶ F_X`, `E_X ⟶ ℚ̄_ℓ,X` it is only an unproved input of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` (where the
comparisons for these two changes are also asserted, on all unbounded objects), which formalises
no blueprint node. The morphisms of condensed rings involved are constructed only for finite
subextensions of `ℚ̄_ℓ` (`PadicAlgCl.FiniteIntermediateField`). -/
theorem properDirectImage_baseChange_projectionFormula_continuousMapRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ K : 𝔻[𝐄](X.left), boundedConstructible (condensedRingObj 𝐄 X.left) K →
      boundedConstructible (condensedRingObj 𝐄 Y.left) ((R((p.left)_*⟦𝐄⟧)).obj K)) ∧
    (∀ {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' p' p g)
      (K : 𝔻[𝐄](X.left)), boundedConstructible (condensedRingObj 𝐄 X.left) K →
        IsIso ((baseChangeMap 𝐄 ((Over.forget _).map_commSq sq.toCommSq)).app K)) ∧
    (∀ (K : 𝔻[𝐄](X.left)) (M : 𝔻[𝐄](Y.left)), boundedConstructible (condensedRingObj 𝐄 X.left) K →
      boundedConstructible (condensedRingObj 𝐄 Y.left) M →
        IsIso (((projectionMap 𝐄 p.left).app K).app M)) := by
  refine ⟨fun K hK ↦ ?_, fun {g p' g'} sq K hK ↦ ?_, fun K M hK hM ↦ ?_⟩
  · exact ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E p ⟨K, hK⟩
  · have : IsNoetherian ((Over.forget (Spec (.of k))).obj Y) := isNoetherian_left Y
    have : IsNoetherian ((Over.forget (Spec (.of k))).obj Y') := isNoetherian_left Y'
    have : IsProper ((Over.forget (Spec (.of k))).map p) := ‹IsProper p.left›
    exact isIso_baseChangeMap_app_padicSubfield_of_isProper ℓ (Y := (Over.forget _).obj Y)
      (Y' := (Over.forget _).obj Y') Y.hom Y'.hom ((Over.forget _).map_commSq sq.toCommSq)
      (sq.map (Over.forget _)) E K hK
  · exact isIso_projectionMap_continuousMapRingObj_of_boundedConstructible ℓ E p K M hK hM

/-- Blueprint `proposition-proper-direct-image-extension-zero`: Proper direct image and extension by
zero; the case `Λ = E̲` (for which `Dctf = Dbc`). If `p : X ⟶ Y` is proper, `Rp_*` maps
`Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there. If `j : U ⟶ X` is an
open immersion, `j_!` maps `Dbc(U, Λ)` into `Dbc(X, Λ)`, preserves direct sums, and maps
`Loc(Dbc(U, Λ))` into `Loc(Dbc(X, Λ))`. Both functors are exact, being triangulated functors
of the ambient derived categories. The statement on `j_!` is
`localizingClosure_boundedConstructible_openImmersionLowerShriek` of this namespace (blueprint
`proposition-proper-direct-image-extension-zero`). -/
theorem localizingBoundedConstructible_lowerStar_lowerShriek_continuousMapRingObj :
    (∀ (p : X ⟶ Y) [IsProper p.left],
      (∀ M, localizingBoundedConstructible 𝐄 X.left M →
        localizingBoundedConstructible 𝐄 Y.left ((R((p.left)_*⟦𝐄⟧)).obj M)) ∧
      (R((p.left)_*⟦𝐄⟧)).PreservesCoproductsOn.{u + 1}
        (localizingBoundedConstructible 𝐄 X.left)) ∧
    (∀ (j : X' ⟶ X) [IsOpenImmersion j.left],
      boundedConstructible (condensedRingObj 𝐄 X'.left) ≤
          (boundedConstructible (condensedRingObj 𝐄 X.left)).inverseImage D((j.left)_!open⟦𝐄⟧) ∧
        (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) D((j.left)_!open⟦𝐄⟧)) ∧
        localizingBoundedConstructible 𝐄 X'.left ≤
          (localizingBoundedConstructible 𝐄 X.left).inverseImage D((j.left)_!open⟦𝐄⟧)) :=
  ⟨fun p _ ↦
      have := isNoetherian_of_locallyOfFiniteType Y.hom
      localizingBoundedConstructible_rightDerivedLowerStar_of_properLowerStarHypotheses
        (properLowerStarHypotheses_continuousMapRingObj ℓ E Y.hom p.left),
    fun j _ ↦ localizingClosure_boundedConstructible_openImmersionLowerShriek 𝐄 ℓ j⟩

/-- Blueprint `proposition-proper-base-change-localizing-categories--1`: Proper base change on the
localizing categories, for `Λ = E̲` (for which `Dctf = Dbc`): for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper, the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` is an
isomorphism for every `K ∈ Loc(Dbc(X, Λ))`. -/
theorem isIso_baseChangeMap_of_localizing_continuousMapRingObj {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    {K : 𝔻[𝐄](X.left)} (hK : localizingBoundedConstructible 𝐄 X.left K) :
    IsIso ((baseChangeMap 𝐄 ((Over.forget _).map_commSq sq.toCommSq)).app K) := by
  have : IsProper p'.left :=
    MorphismProperty.of_isPullback (P := @IsProper) (sq.map (Over.forget _)) ‹IsProper p.left›
  have h₁ :=
    ((localizingBoundedConstructible_lowerStar_lowerShriek_continuousMapRingObj (X' := X) ℓ E).1
      p).2
  have h₂ :=
    ((localizingBoundedConstructible_lowerStar_lowerShriek_continuousMapRingObj (X' := X') ℓ E).1
      p').2
  exact isIso_baseChangeMap_of_localizingBoundedConstructible 𝐄
    ((Over.forget _).map_commSq sq.toCommSq) h₁ h₂
    (fun K hK ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g'.left K hK)
    (fun K hK ↦ (properDirectImage_baseChange_projectionFormula_continuousMapRingObj ℓ E p).2.1
      sq K hK) hK

/-- Blueprint `proposition-direct-image-along-open-immersion`: Direct image along an open immersion;
the case `Λ = E̲`: for a quasi-compact open immersion `j : U ⟶ X`, `Rj_*` maps `Dbc(U, Λ)` into
`Dbc(X, Λ)`. -/
theorem boundedConstructible_rightDerivedLowerStar_openImmersion_continuousMapRingObj
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
    {K : 𝔻[𝐄](X.left)} (hK : boundedConstructible (condensedRingObj 𝐄 X.left) K) :
    boundedConstructible (condensedRingObj 𝐄 Y.left) ((R((j.left)_*⟦𝐄⟧)).obj K) :=
  ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E j ⟨K, hK⟩

end Field

/-! ### The coefficient ring ℚ̲̄_ℓ -/

section AlgCl

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- Blueprint `proposition-six-operations-dctf--14`: `⊗ᴸ` preserves bounded constructible complexes
(`ℓ`-adic `Λ`), stated for `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` by one declaration each; the case `Λ = ℚ̲̄_ℓ`.
If `K, L ∈ D(Mod_{Λ_X})` are bounded constructible, then
so is `K ⊗ᴸ_{Λ_X} L`. -/
theorem boundedConstructible_tensor_padicAlgClRingObj
    {K L : 𝔻[𝐐](X.left)}
    (hK : boundedConstructible (condensedRingObj 𝐐 X.left) K)
    (hL : boundedConstructible (condensedRingObj 𝐐 X.left) L) :
    boundedConstructible (condensedRingObj 𝐐 X.left) (K ⊗ L) :=
  ObjectProperty.prop_tensor hK hL

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsSeparated Y'.hom] in
/-- Blueprint `proposition-proper-direct-image-constructible-complexes`: Proper direct image, base
change and projection formula for `E` and `ℚ̄_ℓ`; the case `Λ = ℚ̲̄_ℓ`. Let `p : X ⟶ Y` be proper.

1. For `K ∈ D(X_proét, 𝒪_E)` bounded below, `Rp_*(K[1/ℓ]) ≃ (Rp_*K)[1/ℓ]`; for
   `K ∈ D(X_proét, E)` bounded below and `F/E` finite, `Rp_*(K_F) ≃ (Rp_*K)_F` and
   `Rp_*(K_{ℚ̄_ℓ}) ≃ (Rp_*K)_{ℚ̄_ℓ}`, via the canonical maps.
2. `Rp_*` maps `Dbc(X, Λ)` into `Dbc(Y, Λ)`.
3. The proper base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` (for a cartesian square
   `g' ≫ p = p' ≫ g`) and the projection formula map `Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` are
   isomorphisms for `K ∈ Dbc(X, Λ)` and `M ∈ Dbc(Y, Λ)`.

Stated here: (2) and (3), for `Λ = ℚ̲̄_ℓ`. Not stated: the comparisons (1) of the direct image
with the changes of coefficients `𝒪_E → E`, `E → F`, `E → ℚ̄_ℓ` on bounded below complexes;
the comparison maps `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom` are defined only
for an exact extension of scalars; exactness is not available for `𝒪_{E,X} ⟶ E_X`, and for
`E_X ⟶ F_X`, `E_X ⟶ ℚ̄_ℓ,X` it is only an unproved input of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` (where the
comparisons for these two changes are also asserted, on all unbounded objects), which formalises
no blueprint node. The morphisms of condensed rings involved are constructed only for finite
subextensions of `ℚ̄_ℓ` (`PadicAlgCl.FiniteIntermediateField`). -/
theorem properDirectImage_baseChange_projectionFormula_padicAlgClRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ K : 𝔻[𝐐](X.left), boundedConstructible (condensedRingObj 𝐐 X.left) K →
      boundedConstructible (condensedRingObj 𝐐 Y.left) ((R((p.left)_*⟦𝐐⟧)).obj K)) ∧
    (∀ {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' p' p g)
      (K : 𝔻[𝐐](X.left)), boundedConstructible (condensedRingObj 𝐐 X.left) K →
        IsIso ((baseChangeMap 𝐐 ((Over.forget _).map_commSq sq.toCommSq)).app K)) ∧
    (∀ (K : 𝔻[𝐐](X.left)) (M : 𝔻[𝐐](Y.left)), boundedConstructible (condensedRingObj 𝐐 X.left) K →
      boundedConstructible (condensedRingObj 𝐐 Y.left) M →
        IsIso (((projectionMap 𝐐 p.left).app K).app M)) :=
  ⟨fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ p ⟨K, hK⟩,
    fun sq K hK ↦ by
      have : IsNoetherian ((Over.forget (Spec (.of k))).obj Y) := isNoetherian_left Y
      have : IsNoetherian ((Over.forget (Spec (.of k))).obj Y') := isNoetherian_left Y'
      have : IsProper ((Over.forget (Spec (.of k))).map p) := ‹IsProper p.left›
      exact isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ (Y := (Over.forget _).obj Y)
        (Y' := (Over.forget _).obj Y') Y.hom Y'.hom ((Over.forget _).map_commSq sq.toCommSq)
        (sq.map (Over.forget _)) K hK,
    fun K M hK hM ↦ isIso_projectionMap_padicAlgClRingObj_of_integral ℓ p
      (fun E K M hK hM ↦ by
        exact_mod_proofs (properDirectImage_baseChange_projectionFormula_padicIntegersRingObj ℓ
          (X' := X) (Y' := Y) E.1 p).2.2 K M hK hM) K M hK hM⟩

/-- Blueprint `proposition-proper-direct-image-extension-zero`: Proper direct image and extension by
zero; the case `Λ = ℚ̲̄_ℓ` (for which `Dctf = Dbc`). If `p : X ⟶ Y` is proper, `Rp_*` maps
`Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there. If `j : U ⟶ X` is an
open immersion, `j_!` maps `Dbc(U, Λ)` into `Dbc(X, Λ)`, preserves direct sums, and maps
`Loc(Dbc(U, Λ))` into `Loc(Dbc(X, Λ))`. Both functors are exact, being triangulated functors
of the ambient derived categories. The statement on `j_!` is
`localizingClosure_boundedConstructible_openImmersionLowerShriek` of this namespace (blueprint
`proposition-proper-direct-image-extension-zero`). -/
theorem localizingBoundedConstructible_lowerStar_lowerShriek_padicAlgClRingObj :
    (∀ (p : X ⟶ Y) [IsProper p.left],
      (∀ M, localizingBoundedConstructible 𝐐 X.left M →
        localizingBoundedConstructible 𝐐 Y.left ((R((p.left)_*⟦𝐐⟧)).obj M)) ∧
      (R((p.left)_*⟦𝐐⟧)).PreservesCoproductsOn.{u + 1}
        (localizingBoundedConstructible 𝐐 X.left)) ∧
    (∀ (j : X' ⟶ X) [IsOpenImmersion j.left],
      boundedConstructible (condensedRingObj 𝐐 X'.left) ≤
          (boundedConstructible (condensedRingObj 𝐐 X.left)).inverseImage D((j.left)_!open⟦𝐐⟧) ∧
        (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) D((j.left)_!open⟦𝐐⟧)) ∧
        localizingBoundedConstructible 𝐐 X'.left ≤
          (localizingBoundedConstructible 𝐐 X.left).inverseImage D((j.left)_!open⟦𝐐⟧)) :=
  ⟨fun p _ ↦
      have := isNoetherian_of_locallyOfFiniteType Y.hom
      localizingBoundedConstructible_rightDerivedLowerStar_of_properLowerStarHypotheses
        (properLowerStarHypotheses_padicAlgClRingObj ℓ Y.hom p.left),
    fun j _ ↦ localizingClosure_boundedConstructible_openImmersionLowerShriek 𝐐 ℓ j⟩

/-- Blueprint `proposition-proper-base-change-localizing-categories--1`: Proper base change on the
localizing categories, for `Λ = ℚ̲̄_ℓ` (for which `Dctf = Dbc`): for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper, the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` is an
isomorphism for every `K ∈ Loc(Dbc(X, Λ))`. -/
theorem isIso_baseChangeMap_of_localizing_padicAlgClRingObj {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    {K : 𝔻[𝐐](X.left)} (hK : localizingBoundedConstructible 𝐐 X.left K) :
    IsIso ((baseChangeMap 𝐐 ((Over.forget _).map_commSq sq.toCommSq)).app K) := by
  have : IsProper p'.left :=
    MorphismProperty.of_isPullback (P := @IsProper) (sq.map (Over.forget _)) ‹IsProper p.left›
  have h₁ :=
    ((localizingBoundedConstructible_lowerStar_lowerShriek_padicAlgClRingObj (X' := X) ℓ).1 p).2
  have h₂ :=
    ((localizingBoundedConstructible_lowerStar_lowerShriek_padicAlgClRingObj (X' := X') ℓ).1
      p').2
  exact isIso_baseChangeMap_of_localizingBoundedConstructible 𝐐
    ((Over.forget _).map_commSq sq.toCommSq) h₁ h₂
    (fun K hK ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g'.left K hK)
    (fun K hK ↦ (properDirectImage_baseChange_projectionFormula_padicAlgClRingObj ℓ p).2.1
      sq K hK) hK

/-- Blueprint `proposition-direct-image-along-open-immersion`: Direct image along an open immersion;
the case `Λ = ℚ̲̄_ℓ`: for a quasi-compact open immersion `j : U ⟶ X`, `Rj_*` maps `Dbc(U, Λ)` into
`Dbc(X, Λ)`. -/
theorem boundedConstructible_rightDerivedLowerStar_openImmersion_padicAlgClRingObj
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
    {K : 𝔻[𝐐](X.left)} (hK : boundedConstructible (condensedRingObj 𝐐 X.left) K) :
    boundedConstructible (condensedRingObj 𝐐 Y.left) ((R((j.left)_*⟦𝐐⟧)).obj K) :=
  boundedConstructible_rightDerivedLowerStar_obj ℓ j ⟨K, hK⟩

end AlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
