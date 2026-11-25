/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Finite-stage étale Verdier biduality over a general base field

`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed` proves Verdier biduality
on `Dctf(X, Λ)` for `X` separated of finite type over an algebraically closed field. This file
extends it to other base fields `k` (blueprint `theorem-verdier-biduality`, (i)): biduality is
local on `X` (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_forall_isAffine`), and
for `X` affine, closed in `𝔸ⁿ_k`, a field extension `k ⟶ k'` gives a surjective base change
`g : X_{k'} ⟶ X`, along which `Lg^* ω_X ≅ ω_{X_{k'}} ⊗ᴸ L` with `L` invertible
(`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic`, for
`Spec k' ⟶ Spec k`). Hence `Lg^* δ_K` is an isomorphism as soon as `δ_{Lg^* K}` is, provided
`Lg^*` commutes with the two internal Homs into `ω_X`.

- Over a perfect field, take `k' = k̄`: the internal-hom comparisons hold by the generic
  internal-hom exchange, `𝔻_X K` lying in `Dctf` (this is where perfectness enters, through
  `AlgebraicGeometry.Etale.constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField`).
- Over an arbitrary field, take `k'` the perfect closure of `k` (in `k̄`): `Spec k' ⟶ Spec k` is
  a universal homeomorphism, hence so is `g`, so that `Lg^*` is an equivalence and commutes
  with all internal Homs
  (`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_isUniversalHomeomorphism`),
  and biduality on `X_{k'}` is the perfect case.

## Main results

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_perfectField`: biduality over a
  perfect field.
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_field`: biduality over an
  arbitrary field.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The morphism `Spec L ⟶ Spec K` of a field extension is surjective: its target is a
point. -/
lemma surjective_spec_map_algebraMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩

section UniversalHomeomorphism

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsUniversalHomeomorphism g]

omit [Finite Λ] in
/-- For a universal homeomorphism `g`, the counit of `Lg^* ⊣ Rg_*` is invertible: `g_*` is an
equivalence (topological invariance, `AlgebraicGeometry.Etale.isEquivalence_lowerStar`), so
`Rg_*` is fully faithful. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_counit_of_isUniversalHomeomorphism :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit := by
  have := isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) g
  exact (derivedUpperStarLowerStarAdjunction _ g).counit_isIso_of_R_fully_faithful

omit [Finite Λ] in
/-- For a universal homeomorphism `g`, the unit `M ⟶ Rg_* Lg^* M` of `Lg^* ⊣ Rg_*` is
invertible: its image under `Lg^*` is inverse to the (invertible) counit by the triangle
identity, and `Lg^*` is conservative, `g` being surjective. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isUniversalHomeomorphism
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app M) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isUniversalHomeomorphism Λ g
  refine isIso_of_forall_isIso_leftDerivedUpperStar_map Λ (fun _ : PUnit.{u + 1} ↦ g)
    (fun x ↦ ?_) _ fun _ ↦ ?_
  · obtain ⟨y, hy⟩ := g.surjective x
    exact ⟨PUnit.unit, y, hy⟩
  · have : IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map (adj.unit.app M) ≫
        adj.counit.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
      rw [adj.left_triangle_components M]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)

omit [Finite Λ] in
/-- **The internal Hom commutes with pullback along a universal homeomorphism.** For a
universal homeomorphism `g : Y ⟶ X`, the comparison `Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)`
is an isomorphism for all `K` and `M`: `M ≅ Rg_* Lg^* M`, and the comparison is invertible at
`(K, Rg_* N)` since `Rg_*` is fully faithful. -/
lemma isIso_derivedHomUpperStarComparison_of_isUniversalHomeomorphism
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g K M) := by
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isUniversalHomeomorphism Λ g
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isUniversalHomeomorphism Λ g M
  refine (isIso_derivedHomUpperStarComparison_iff_of_iso_right _ g K
    (asIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app M))).2 ?_
  exact isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ g K _

end UniversalHomeomorphism

/-- Blueprint `theorem-verdier-biduality`, (i), **reduction to the affine case**: if
biduality holds for every affine scheme separated, quasi-compact and locally of finite type over
`k`, it holds for every such `X`. Biduality is local (`corollary-verdier-exchange-formulas--5`,
`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff`), and the
affine opens cover `X`. -/
theorem isIso_verdierDualDoubleDual_app_of_forall_isAffine {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (haff : ∀ {U : Scheme.{u}} [IsAffine U] (aU : U ⟶ Spec (.of k)) [IsSeparated aU]
      [LocallyOfFiniteType aU] [QuasiCompact aU]
      {N : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U N →
      IsIso ((verdierDualDoubleDual Λ aU).app N))
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  refine isIso_of_forall_isIso_leftDerivedUpperStar_map Λ
    (fun U : X.affineOpens ↦ Scheme.Opens.ι (U : X.Opens)) (fun x ↦ ?_) _ fun U ↦ ?_
  · obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hxU⟩, rfl⟩
  have : IsAffine (U : X.Opens) := U.2
  rw [← isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff Λ aX]
  exact haff _ (constructibleFiniteTor_leftDerivedUpperStar _ _ hK)

/-- Blueprint `theorem-verdier-biduality`, (i), the affine case over a perfect field: for
`X` affine of finite type over a perfect field `k`, closed in `𝔸ⁿ_k`, the double-dual map `δ_K`
is an isomorphism for every `K ∈ Dctf(X, Λ)`. The pullback `g : X_{k̄} ⟶ X` is surjective, so it
suffices that `Lg^* δ_K` is an isomorphism; by the geometric generic fibre comparison
`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic`
(for `S = Spec k`, `T = Spec k̄`), this is `δ_{Lg^* K}`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed`. -/
theorem isIso_verdierDualDoubleDual_app_of_perfectField_of_isAffine {k : Type u} [Field k]
    [PerfectField k] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [IsAffine X]
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) := by
  obtain ⟨n, i, hip, hi⟩ := exists_isClosedImmersion_affineSpace_of_isAffine aX
  let S := Spec (.of k)
  let t : Spec (.of (AlgebraicClosure k)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : Surjective t := surjective_spec_map_algebraMap k _
  let proj : 𝔸(ULift.{u} (Fin n); S) ⟶ S := 𝔸(ULift.{u} (Fin n); S) ↘ S
  let g' := pullback.fst aX t
  let fT := pullback.snd aX t
  let i' : pullback aX t ⟶ pullback proj t :=
    pullback.lift (g' ≫ i) fT (by rw [Category.assoc, hip, pullback.condition])
  have hi'T : i' ≫ pullback.snd proj t = fT := pullback.lift_snd _ _ _
  have sqP := IsPullback.of_hasPullback proj t
  have sqX : IsPullback g' i' i (pullback.fst proj t) :=
    IsPullback.of_bot
      (by
        rw [hi'T, hip]
        exact IsPullback.of_hasPullback aX t)
      (pullback.lift_fst _ _ _).symm sqP
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom t
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback sqX hi
  have hM := constructibleFiniteTor_leftDerivedUpperStar _ g' hK
  have hδ' := isIso_verdierDualDoubleDual_app_of_isAlgClosed Λ fT hM
  have hgen := (isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic Λ (𝟙 S)
    (isInvertible_dualizingComplex (d := 0) Λ (𝟙 S)) t (fun _ ↦ Subsingleton.elim _ _) proj
    (Nat.card (ULift.{u} (Fin n))) sqP i sqX aX (by rw [Category.comp_id, hip]) fT hi'T
    (leftDerivedUpperStarBraided _ g') hK).2 hδ'
  refine isIso_of_forall_isIso_leftDerivedUpperStar_map Λ (fun _ : PUnit.{u + 1} ↦ g')
    (fun x ↦ ?_) _ fun _ ↦ hgen
  obtain ⟨y, hy⟩ := g'.surjective x
  exact ⟨PUnit.unit, y, hy⟩

/-- **Finite-stage étale Verdier biduality over a perfect field** (blueprint
`theorem-verdier-biduality`, (i)): for a finite ring `Λ` whose exponent is invertible on the
perfect field `k` and `X` separated, quasi-compact and locally of finite type over `k`, the
double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every `K ∈ Dctf(X, Λ)`. -/
theorem isIso_verdierDualDoubleDual_app_of_perfectField {k : Type u} [Field k] [PerfectField k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) :=
  isIso_verdierDualDoubleDual_app_of_forall_isAffine Λ
    (fun aU _ _ _ _ hN ↦ isIso_verdierDualDoubleDual_app_of_perfectField_of_isAffine Λ aU hN) aX
    hK

/-- Blueprint `theorem-verdier-biduality`, (i), the affine case over an arbitrary field:
for `X` affine of finite type over a field `k`, closed in `𝔸ⁿ_k`, the double-dual map `δ_K` is
an isomorphism for every `K ∈ Dctf(X, Λ)`. Let `k'` be the perfect closure of `k` (in `k̄`);
`Spec k' ⟶ Spec k` is a universal homeomorphism, hence so is the base change
`g : X_{k'} ⟶ X`. Then `Lg^* ω_X ≅ ω_{X_{k'}} ⊗ᴸ L` with `L` invertible
(`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic`), `Lg^*`
commutes with all internal Homs
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_isUniversalHomeomorphism`), so
`Lg^* δ_K` is an isomorphism if and only if `δ_{Lg^* K}` is
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff`), which
holds over the perfect field `k'`. Since `g` is surjective, `δ_K` is an isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_of_field_of_isAffine {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [IsAffine X]
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) := by
  obtain ⟨n, i, hip, hi⟩ := exists_isClosedImmersion_affineSpace_of_isAffine aX
  let k' := perfectClosure k (AlgebraicClosure k)
  let S := Spec (.of k)
  let t : Spec (.of k') ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have : IsUniversalHomeomorphism t :=
    (Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable k k').isUniversalHomeomorphism
  let proj : 𝔸(ULift.{u} (Fin n); S) ⟶ S := 𝔸(ULift.{u} (Fin n); S) ↘ S
  let g' := pullback.fst aX t
  let fT := pullback.snd aX t
  let i' : pullback aX t ⟶ pullback proj t :=
    pullback.lift (g' ≫ i) fT (by rw [Category.assoc, hip, pullback.condition])
  have hi'T : i' ≫ pullback.snd proj t = fT := pullback.lift_snd _ _ _
  have sqP := IsPullback.of_hasPullback proj t
  have sqX : IsPullback g' i' i (pullback.fst proj t) :=
    IsPullback.of_bot
      (by
        rw [hi'T, hip]
        exact IsPullback.of_hasPullback aX t)
      (pullback.lift_fst _ _ _).symm sqP
  have : HasInvertibleExponent Λ (Spec (.of k')) := .of_hom t
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback sqX hi
  have : IsUniversalHomeomorphism g' := MorphismProperty.pullback_fst _ _ inferInstance
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_iso_leftDerivedUpperStar_dualizingComplex_of_generic Λ (𝟙 S)
    (isInvertible_dualizingComplex (d := 0) Λ (𝟙 S)) t (fun _ ↦ Subsingleton.elim _ _) proj
    (Nat.card (ULift.{u} (Fin n))) sqP i sqX aX (by rw [Category.comp_id, hip]) fT hi'T
  have hM := constructibleFiniteTor_leftDerivedUpperStar _ g' hK
  have hgen := (isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff Λ aX fT g'
    (leftDerivedUpperStarBraided _ g') ((isInvertible_iff_exists_derivedTensor _).2 hL) e K
    (isIso_derivedHomUpperStarComparison_of_isUniversalHomeomorphism Λ g' _ _)
    (isIso_derivedHomUpperStarComparison_of_isUniversalHomeomorphism Λ g' _ _)).2
    (isIso_verdierDualDoubleDual_app_of_perfectField Λ fT hM)
  refine isIso_of_forall_isIso_leftDerivedUpperStar_map Λ (fun _ : PUnit.{u + 1} ↦ g')
    (fun x ↦ ?_) _ fun _ ↦ hgen
  obtain ⟨y, hy⟩ := g'.surjective x
  exact ⟨PUnit.unit, y, hy⟩

/-- **Finite-stage étale Verdier biduality over an arbitrary field** (blueprint
`theorem-verdier-biduality`, (i)): for a finite ring `Λ` whose exponent is invertible on the
field `k` and `X` separated, quasi-compact and locally of finite type over `k`, the double-dual
morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every `K ∈ Dctf(X, Λ)`. -/
theorem isIso_verdierDualDoubleDual_app_of_field {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) :=
  isIso_verdierDualDoubleDual_app_of_forall_isAffine Λ
    (fun aU _ _ _ _ hN ↦ isIso_verdierDualDoubleDual_app_of_field_of_isAffine Λ aU hN) aX hK

end AlgebraicGeometry.Etale
