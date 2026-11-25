/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.TraceFormula.Product
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.OpenImmersionFieldBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!

# Base change along a product projection

Let `f : U ⟶ Y` be a morphism of separated `k`-schemes of finite type and `X` a separated
`k`-scheme of finite type. The square
```
X ⨯ U ──(𝟙 × f)──▶ X ⨯ Y
  │ p_U               │ p_Y
  ▼                   ▼
  U ────── f ───────▶ Y
```
(`ProEtale.CondensedRing.commSq_prodMap_snd`) is cartesian, and its base change morphism
`Lp_Y^* Rf_* ⟶ R(𝟙 × f)_* Lp_U^*` on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is an isomorphism
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`; blueprint
`lemma-base-change-along-product-projection`). Since `X` may be singular, smooth base change does
not apply. Following the blueprint (`lemma-base-change-along-product-projection--1`), we choose a
compactification `f = p ∘ i` with `i` an open immersion and `p` proper (Nagata). The square of `f`
is the vertical pasting of the squares of `i` and of `p`, so its base change morphism is the pasting
of theirs (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap_comp`). The one of
`p` is an isomorphism by proper base change, the one of `i` by base change for open direct images
over a field.

The latter
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion`, the
`ℚ̄_ℓ` form of blueprint `corollary-open-direct-image-over-field--2`) is deduced from finite
coefficients as in the proof of blueprint `theorem-smooth-base-change-all-admissible`: a bounded
constructible `ℚ̄_ℓ`-complex has an integral model `K₀` over some `𝒪_E`
(`ProEtale.exists_padicAlgCl_iso_integralModel`), the scalar comparisons identify the base change
morphism at `ℚ̄_ℓ ⊗ᴸ K₀` with the extension of scalars of the integral one
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral`), derived
Nakayama reduces the integral one to its first derived reduction `K₀ ⊗ᴸ 𝔽_E`
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_integral_app_of_reduction`), which
is the pro-étale base change morphism with coefficients `𝔽_E` at a complex of étale origin, an
isomorphism by the étale theorem
(`ProEtale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_field`).

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion`:
  base change for open direct images over a field (blueprint
  `corollary-open-direct-image-over-field`, `corollary-open-direct-image-over-field--2`, section
  `chap-Construction-of-f`), in its `ℚ̄_ℓ` form.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`: generic base change
  over the field `k` along `X ⨯ Y ⟶ Y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom]
  [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The commutative square
```
X ⨯ U ──(𝟙 × f)──▶ X ⨯ Y
  │ p_U               │ p_Y
  ▼                   ▼
  U ────── f ───────▶ Y
```
of the second projections, the base change of `f` along `X ⨯ Y ⟶ Y`. -/
lemma commSq_prodMap_snd (f : U ⟶ Y) :
    CommSq (prod.snd : X ⨯ U ⟶ U) (prod.map (𝟙 X) f) f prod.snd :=
  ⟨(prod.map_snd _ _).symm⟩

/-- **Base change for open direct images over a field**, in its `ℚ̄_ℓ` form: for an open
immersion `j : U ⟶ Y` of separated `k`-schemes of finite type and any separated `k`-scheme of
finite type `X`, the base change morphism `Lp_Y^* Rj_* ⟶ R(𝟙 × j)_* Lp_U^*` of the square
`commSq_prodMap_snd` is an isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`.

This is the blueprint node `corollary-open-direct-image-over-field--2` (equivalently the base change
assertion of `corollary-open-direct-image-over-field`), section `chap-Construction-of-f`, which
states it for finite `ℓ`-primary coefficients; it is Deligne's generic base change theorem (SGA 4½,
[Th. finitude], Théorème 1.9) over the base `Spec k`, whose only nonempty open is itself.

The finite-coefficient statement is
`ProEtale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_field`. As in the proof of blueprint
`theorem-smooth-base-change-all-admissible`, a bounded constructible `ℚ̄_ℓ`-complex has an integral
model `K₀` over some `𝒪_E`, the scalar comparisons reduce to the integral base change morphism at
`K₀` (`isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral`), and derived Nakayama to its
first derived reduction, the pro-étale base change morphism with coefficients `𝔽_E` at a complex
of étale origin (`isIso_boundedConstructibleBaseChange_integral_app_of_reduction`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion (j : U ⟶ Y)
    [IsOpenImmersion j.left] :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) j)) := by
  have hW : IsPullback (prod.snd : X ⨯ Y ⟶ Y).left (prod.fst : X ⨯ Y ⟶ X).left Y.hom X.hom :=
    (isPullback_prod_left X Y).flip
  have hsq : IsPullback (prod.snd : X ⨯ U ⟶ U).left (prod.map (𝟙 X) j).left j.left
      (prod.snd : X ⨯ Y ⟶ Y).left := by
    refine IsPullback.of_bot ?_ (congrArg CommaMorphism.left (commSq_prodMap_snd j).w) hW
    have h₁ : (prod.map (𝟙 X) j).left ≫ (prod.fst : X ⨯ Y ⟶ X).left =
        (prod.fst : X ⨯ U ⟶ X).left := by
      rw [← Over.comp_left, prod.map_fst, Category.comp_id]
    rw [h₁, Over.w j]
    exact (isPullback_prod_left X U).flip
  have : CompactSpace (X ⨯ Y).left := QuasiCompact.compactSpace_of_compactSpace (X ⨯ Y).hom
  have : IsLocallyNoetherian (X ⨯ Y).left :=
    LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom
  have : IsNoetherian (X ⨯ Y).left := {}
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : IsNoetherian U.left := {}
  have hℓ : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
      ((ringChar.spec k ℓ).1 h)
  refine isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral ℓ _ hsq fun E K₀ ↦ ?_
  have hΛ := ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E.1
  refine isIso_boundedConstructibleBaseChange_integral_app_of_reduction ℓ E.1 _ hsq K₀ ?_
  exact ProEtale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_field _ Y.hom X.hom j.left
    hW hsq ℓ hℓ hΛ _ (ProEtale.boundedConstructible_derivedReduction_obj U.left ℓ E.1 _ K₀.property)

/-- Base change along a product projection for a proper morphism `p`: the square
`commSq_prodMap_snd p` is cartesian, so its base change morphism is an isomorphism by proper base
change (`isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap_of_isProper (p : U ⟶ Y) [IsProper p.left] :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) p)) :=
  isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (IsPullback.of_prod_snd_with_id p X)

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

/-- **Pasting of base change along a product projection**: if the base change morphisms of the
squares `commSq_prodMap_snd i` and `commSq_prodMap_snd p` are isomorphisms, so is the one of
`commSq_prodMap_snd (i ≫ p)`, the vertical pasting of the two squares (blueprint
`lemma-base-change-along-product-projection--1`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap_comp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (i : U ⟶ Z) (p : Z ⟶ Y)
    (hi : IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) i)))
    (hp : IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) p))) :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) (i ≫ p))) := by
  rw [boundedConstructibleBaseChange_eq_pfBaseChange] at hi hp
  have h := (𝔽).pfBaseChange_paste_vert (SepFinType.homMk (prod.snd : X ⨯ U ⟶ U))
    (SepFinType.homMk (prod.snd : X ⨯ Z ⟶ Z)) (SepFinType.homMk (prod.snd : X ⨯ Y ⟶ Y))
    (SepFinType.homMk (prod.map (𝟙 X) i)) (SepFinType.homMk i)
    (SepFinType.homMk (prod.map (𝟙 X) p)) (SepFinType.homMk p)
    (SepFinType.homMk (prod.map (𝟙 X) (i ≫ p))) (SepFinType.homMk (i ≫ p))
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd i).w)
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd p).w)
    (ObjectProperty.hom_ext _ (by simp)) (ObjectProperty.hom_ext _ rfl)
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd (i ≫ p)).w)
  have key : IsIso ((𝔽).pfBaseChange (SepFinType.homMk (prod.snd : X ⨯ U ⟶ U))
      (SepFinType.homMk (prod.map (𝟙 X) (i ≫ p))) (SepFinType.homMk (i ≫ p))
      (SepFinType.homMk (prod.snd : X ⨯ Y ⟶ Y))
      (SepFinType.homMk_comp_homMk (commSq_prodMap_snd (i ≫ p)).w)) := by
    rw [h]
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]
    infer_instance
  rw [boundedConstructibleBaseChange_eq_pfBaseChange]
  exact key

/-- **Generic base change over the field `k`**: for any morphism `f : U ⟶ Y` of separated
`k`-schemes of finite type and any `X`, the base change morphism
`Lp_Y^* Rf_* ⟶ R(𝟙 × f)_* Lp_U^*` of the square `commSq_prodMap_snd`, i.e. of the base change
of `f` along `X ⨯ Y ⟶ Y`, is an isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (blueprint
`lemma-base-change-along-product-projection`, stated there for finite coefficients; SGA 4½,
[Th. finitude], Théorème 1.9 over `Spec k`).

Following the blueprint (`lemma-base-change-along-product-projection--1`), a Nagata compactification
`f = p ∘ i` reduces it to the open immersion `i`
(`isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion`) and the proper morphism `p`
(`isIso_boundedConstructibleBaseChange_prodMap_of_isProper`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap (f : U ⟶ Y) :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) f)) := by
  let c := compactificationOverField f
  have hf : c.overI ≫ c.overG = f := c.overI_overG
  have := isIso_boundedConstructibleBaseChange_prodMap_comp ℓ (X := X) c.overI c.overG
    (isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion ℓ c.overI)
    (isIso_boundedConstructibleBaseChange_prodMap_of_isProper ℓ c.overG)
  rwa [hf] at this

end AlgebraicGeometry.ProEtale.CondensedRing
