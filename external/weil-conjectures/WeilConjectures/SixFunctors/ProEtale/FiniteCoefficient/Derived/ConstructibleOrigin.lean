/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology

/-!
# Intrinsically constructible pro-étale complexes are of étale origin

Let `Λ` be a finite commutative ring and `X` a scheme. A bounded complex of pro-étale sheaves of
`Λ`-modules with constructible cohomology sheaves (in the intrinsic sense of
`AlgebraicGeometry.ProEtale.IsConstructible`) is of étale origin: it is `D(ν^*) K'` for a bounded
complex `K'` of étale sheaves with constructible cohomology sheaves. This is clause (ii) of
blueprint `theorem-comparison-constructible-sheaves`, deduced from its clause (i)
(`AlgebraicGeometry.ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`) by
dévissage along the truncation triangles
(`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology`) and the
full faithfulness of `ν^*`.

## Main statements

- `ProEtale.DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic`:
  intrinsically bounded constructible complexes are of étale origin.
- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic_eq`: the two readings
  of `Dᵇc(X_proét, Λ)` agree.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

/-- Blueprint `theorem-comparison-constructible-sheaves`, clause (ii): at a finite coefficient ring,
a bounded pro-étale complex with constructible cohomology sheaves is of étale origin. By clause
(i) its cohomology sheaves are `ν^*` of constructible étale sheaves, so it is `D(ν^*) K'` for a
bounded below étale complex `K'` (dévissage along the truncation triangles); `K'` is bounded with
constructible cohomology since `ν^*` is exact and fully faithful. -/
theorem DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleIntrinsic Λ X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  obtain ⟨hb, hc⟩ := hK
  have hE : DerivedCategory.etaleOriginHomology Λ X K := fun n ↦
    have ⟨G, _, he⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ (hc n)
    ⟨G, he⟩
  obtain ⟨K', -, ⟨e⟩⟩ := DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology Λ X hE hb
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  refine ⟨K', ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun n ↦ ?_⟩, ⟨e⟩⟩
  · exact isGE_of_isGE_mapDerivedCategory_comparisonUpperStar
      (_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a)
  · exact isLE_of_isLE_mapDerivedCategory_comparisonUpperStar
      (_root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b)
  · obtain ⟨G, hG, ⟨e'⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ (hc n)
    let f := ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app K' ≪≫
      (_root_.DerivedCategory.homologyFunctor _ n).mapIso e ≪≫ e'.symm
    exact IsConstructibleSheaf.of_iso ((ν^*(X)[ModuleCat.{u + 1} Λ]).preimageIso f).symm

variable (Λ X) in
/-- Blueprint `theorem-comparison-constructible-sheaves`, clause (ii): at a finite coefficient ring,
the intrinsic and the étale-origin readings of `Dᵇc(X_proét, Λ)` agree. -/
theorem DerivedCategory.boundedConstructibleIntrinsic_eq :
    DerivedCategory.boundedConstructibleIntrinsic Λ X =
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X :=
  le_antisymm (fun _ hK ↦ DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic hK)
    (DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic)

end AlgebraicGeometry.ProEtale
