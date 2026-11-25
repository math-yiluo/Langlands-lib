/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangePadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The base-change morphism and the coefficient changes `𝒪_E ⟶ ℚ̄_ℓ` and `𝒪_E ⟶ 𝔽_E`

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and let
`Φ_X = ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} -) : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` be the extension of scalars along
the composite coefficient map `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` (`ProEtale.boundedConstructibleExtendScalars`
followed by `ProEtale.constructibleToPadicAlgCl`). For a cartesian square of schemes separated
and of finite type over the field `k`, the scalar comparisons identify `Φ` of the integral
base-change morphism `BC_sq` with the `ℚ̄_ℓ`-base-change morphism at `Φ K₀`
(blueprint `lemma-naturality-pasting-comparison`, section `chap-Smooth-base-change`). Together with
the integral models of `ℚ̄_ℓ`-complexes (`ProEtale.exists_padicAlgCl_iso_integralModel`), this
reduces the invertibility of a `ℚ̄_ℓ`-base-change morphism to the integral one
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral`).

Similarly, the scalar comparisons for the residue map `𝒪_E ⟶ 𝔽_E` identify the first derived
reduction of the integral base-change morphism with the pro-étale base-change morphism with
finite coefficients at the first derived reduction of `K₀`; by derived Nakayama
(`ProEtale.isIso_of_isIso_derivedReduction_map`) this reduces the invertibility of the integral
base-change morphism to finite coefficients
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_integral_app_of_reduction`).

Both identifications are proved
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_integralToPadicAlgCl`,
`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_boundedConstructibleBaseChange`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

section Rational

variable (E : FiniteIntermediateField ℓ)

/-- Blueprint `lemma-naturality-pasting-comparison` (section `chap-Smooth-base-change`), its last
assertion for the coefficient map `𝒪_E ⟶ ℚ̄_ℓ` of `proposition-six-operations-change-coefficients`
(the composite of the localization `𝒪_E ⟶ E` and the inclusion `E ⟶ ℚ̄_ℓ`): for a cartesian square
of schemes separated and of finite type over `k`

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and `K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`, the scalar comparisons identify the extension of scalars
`ℚ̄_ℓ ⊗ᴸ_{𝒪_E} BC_sq(K₀)` of the integral base-change morphism
`BC_sq(K₀) : Lg^* Rf_* K₀ ⟶ Rf'_* Lg'^* K₀` with the base-change morphism
`BC_sq(ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀)` of `Dᵇc(-)⟦ℚ̄_ℓ⟧`, as arrows. This holds for every commutative square.
It is the composite of the integral stage `𝒪_E ⟶ E`
(`nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational`) and the rational stage
`E ⟶ ℚ̄_ℓ` (`nonempty_arrowIso_boundedConstructibleBaseChange_rationalToPadicAlgCl`), whose (Push)
comparisons are invertible on bounded below complexes
(`isIso_derivedPushHom_app_padicIntegers_of_isGE`,
`isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`). -/
theorem nonempty_arrowIso_boundedConstructibleBaseChange_integralToPadicAlgCl
    (sq : CommSq g' f' f g) (_hsq : IsPullback g'.left f'.left f.left g.left)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    Nonempty (Arrow.mk ((constructibleToPadicAlgCl Y'.left ℓ E).map
        ((boundedConstructibleExtendScalars Y'.left ℓ E).map
          ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E.1 sq).app
            K₀))) ≅
      Arrow.mk ((boundedConstructibleBaseChange ℓ sq).app
        ((constructibleToPadicAlgCl X.left ℓ E).obj
          ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀)))) :=
  ⟨(constructibleToPadicAlgCl Y'.left ℓ E).mapArrow.mapIso
      (nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational ℓ E sq K₀).some ≪≫
    (nonempty_arrowIso_boundedConstructibleBaseChange_rationalToPadicAlgCl ℓ E
      (fun p _ _ K n _ ↦
        isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
      sq _).some⟩

/-- The invertibility of a `ℚ̄_ℓ`-base-change morphism reduces to the integral one: if the
base-change morphism `BC_sq` of a cartesian square is invertible on `Dᵇc(-)⟦𝒪_E⟧` for every finite
subextension `E ⊆ ℚ̄_ℓ`, it is invertible on `Dᵇc(-)⟦ℚ̄_ℓ⟧`. Every bounded constructible
`ℚ̄_ℓ`-complex is `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀` for some `E` and some `K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`
(`ProEtale.exists_padicAlgCl_iso_integralModel`), and the scalar comparisons identify the
`ℚ̄_ℓ`-base-change morphism at `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀` with the extension of scalars of the integral one
(`nonempty_arrowIso_boundedConstructibleBaseChange_integralToPadicAlgCl`). -/
theorem isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral
    [TopologicalSpace.NoetherianSpace X.left]
    (sq : CommSq g' f' f g) (hsq : IsPullback g'.left f'.left f.left g.left)
    (h : ∀ (E : FiniteIntermediateField ℓ) (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      IsIso ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E.1 sq).app K₀)) :
    IsIso (boundedConstructibleBaseChange ℓ sq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel X.left ℓ K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  obtain ⟨α⟩ := nonempty_arrowIso_boundedConstructibleBaseChange_integralToPadicAlgCl ℓ E sq hsq K₀
  have := h E K₀
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).1 (by
    simp only [MorphismProperty.isomorphisms.iff]
    infer_instance)

end Rational

section Integral

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

-- the bounded constructible and the ambient forms of the exchange morphism are unified
/-- Blueprint `lemma-naturality-pasting-comparison` (section `chap-Smooth-base-change`), its last
assertion for the residue map `𝒪_E ⟶ 𝔽_E` to a finite admissible ring of
`proposition-six-operations-change-coefficients`: for a cartesian square of schemes separated and of
finite type over `k`

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and `K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`, the scalar comparisons identify the first derived reduction
`BC_sq(K₀) ⊗ᴸ_{𝒪_E} 𝔽_E` of the integral base-change morphism with the pro-étale base-change
morphism `g^* Rf_* ⟶ Rf'_* g'^*` with finite coefficients `𝔽_E` at the first derived reduction of
`K₀` (`ProEtale.derivedReduction`). Here we only record that the two morphisms are isomorphic as
arrows.

On the ambient derived categories, `BC_sq(K₀)` is the exchange morphism of the pullback
comparison (`Adjunction.nonempty_arrowIso_map_ι_map_app_of_eq_exchangeRight`), whose first derived
reduction is computed by `nonempty_arrowIso_derivedReduction_map_exchangeRight`. -/
theorem nonempty_arrowIso_derivedReduction_boundedConstructibleBaseChange
    (sq : CommSq g' f' f g) (hsq : IsPullback g'.left f'.left f.left g.left)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Nonempty (Arrow.mk ((derivedReduction Y'.left ℓ E).map ((boundedConstructible _).ι.map
        ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E sq).app
          K₀))) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) hsq.toCommSq).app
        ((derivedReduction X.left ℓ E).obj K₀.obj))) := by
  have ha := K₀.property.1.1.choose_spec
  have : K₀.obj.IsGE K₀.property.1.1.choose := ha
  have e := nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E hsq.toCommSq K₀.obj
    K₀.property.1.1.choose
  exact Adjunction.nonempty_arrowIso_map_ι_map_app_of_eq_exchangeRight
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f.left)
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f'.left)
    (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) hsq.toCommSq)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K)
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K)
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ g K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ g' K)
    (boundedConstructiblePullbackSquareComparison _ ℓ sq)
    (by exact_mod_proofs
      (pullbackSquareComparison_hom_app_hom_lift ℓ (Profinite.padicIntegersRingObj ℓ E) sq))
    (PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E sq)
    (PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight ℓ E sq)
    (derivedReduction Y'.left ℓ E) K₀ (by transport_mod_proofs e)

/-- The invertibility of an integral base-change morphism reduces to finite coefficients: for a
cartesian square with noetherian `Y'` and `K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`, if the pro-étale base-change
morphism with coefficients `𝔽_E` is invertible at the first derived reduction of `K₀`, then
`BC_sq(K₀)` is invertible. The scalar comparisons identify the first derived reduction of
`BC_sq(K₀)` with the former
(`nonempty_arrowIso_derivedReduction_boundedConstructibleBaseChange`), and a morphism of bounded
constructible `𝒪_E`-complexes whose first derived reduction is invertible is invertible (derived
Nakayama, `ProEtale.isIso_of_isIso_derivedReduction_map`). -/
theorem isIso_boundedConstructibleBaseChange_integral_app_of_reduction [IsNoetherian Y'.left]
    (sq : CommSq g' f' f g) (hsq : IsPullback g'.left f'.left f.left g.left)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (h : IsIso ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) hsq.toCommSq).app
        ((derivedReduction X.left ℓ E).obj K₀.obj))) :
    IsIso ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E sq).app
      K₀) := by
  apply isIso_of_isIso_derivedReduction_map Y'.left ℓ E
  obtain ⟨β⟩ := nonempty_arrowIso_derivedReduction_boundedConstructibleBaseChange ℓ E sq hsq K₀
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff β).2 h

end Integral

end AlgebraicGeometry.ProEtale.CondensedRing
