/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.PurityDevissage

/-!

# Compatibilities of smooth purity used by the Künneth–Verdier theorem

The Künneth–Verdier theorem for `ℚ̄_ℓ`-coefficients
(`ProEtale.CondensedRing.isIso_kunnethVerdierMap`, blueprint
`lemma-external-duality-trace-morphism--1`) uses smooth purity through a single statement: for `Y`
smooth over `k`, the exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp_X^! M` of the projection
`p_X : X ⨯ Y ⟶ X` is an isomorphism
(`ProEtale.CondensedRing.isIso_exceptionalKunnethMap_of_smooth`).

The map `α` factors as the exceptional base change map of the product square at the unit,
`Lp_Y^* Ra_Y^! ℚ̄_ℓ ⟶ Rp_X^! ℚ̄_ℓ`, followed by the purity map
`γ_{p_X, M} : Lp_X^* M ⊗ Rp_X^! ℚ̄_ℓ ⟶ Rp_X^! M`
(`ProEtale.CondensedRing.exceptionalKunnethMap_eq`). Both are isomorphisms by smooth purity.

## Main definitions

- `ProEtale.CondensedRing.prodUpperShriekBaseChangeUnit`: the exceptional base change map of the
  product square at the unit. The purity map `upperShriekUnitTensorMap` and the exceptional base
  change map `upperShriekBaseChange` are defined in `WeilConjectures.TraceFormula.PurityTensorMap`.

## Smooth purity

- `ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`: smooth purity for arbitrary
  coefficients (SGA 4, Exposé XVIII, Théorème 3.2.5; blueprint `theorem-sp-qbar`), proved in
  `WeilConjectures.TraceFormula.PurityDevissage`.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_smooth`: `Rf^!` commutes with base
  change for `f` smooth (SGA 4, Exposé XVIII, Théorème 3.2.5 and Théorème 2.9 (Var 4); blueprint
  `proposition-compatibility-purity-base-change`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-- The calculation of the adjoint factorization uses only braiding and the naturality of
the projection formula. Keeping the functor abstract avoids unfolding the six functors. -/
private lemma exceptionalKunnethMap_factorization_aux
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [MonoidalCategory 𝒞]
    [MonoidalCategory 𝒟] [BraidedCategory 𝒟] (F : 𝒟 ⥤ 𝒞)
    (M : 𝒞) (A : 𝒟) {W U : 𝒟} (t : W ⟶ U)
    (pW : F.obj W ⊗ M ⟶ F.obj (W ⊗ A))
    (pU : F.obj U ⊗ M ⟶ F.obj (U ⊗ A))
    [IsIso pW] [IsIso pU]
    (hp : (F.map t ▷ M) ≫ pU = pW ≫ F.map (t ▷ A))
    {T₁ T₂ : 𝒞} (b : F.obj W ⟶ T₁) (c : T₁ ⟶ T₂) (e : T₂ ⟶ 𝟙_ 𝒞)
    (q : F.obj U ⟶ 𝟙_ 𝒞) (ht : F.map t ≫ q = b ≫ c ≫ e) :
    F.map (β_ A W).hom ≫ inv pW ≫ (b ▷ M) ≫ (c ▷ M) ≫ (e ▷ M) ≫ (λ_ M).hom =
      F.map (A ◁ t) ≫ F.map (β_ A U).hom ≫ inv pU ≫ (q ▷ M) ≫ (λ_ M).hom := by
  have hPF : F.map (t ▷ A) ≫ inv pU = inv pW ≫ (F.map t ▷ M) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hp.symm
  rw [← F.map_comp_assoc, BraidedCategory.braiding_naturality_right, F.map_comp_assoc,
    reassoc_of% hPF]
  conv_rhs => rw [← comp_whiskerRight_assoc, ht]
  simp only [comp_whiskerRight, Category.assoc]

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section General

variable {X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The exceptional inverse image along a smooth morphism commutes with base change** (SGA 4,
Exposé XVIII, Théorème 3.2.5 together with the compatibility of the trace with base change,
Théorème 2.9 (Var 4); blueprint `proposition-compatibility-purity-base-change`): for a cartesian
square with `f` smooth, the exceptional base change map `Lg'^* Rf^! L ⟶ Rf'^! Lg^* L` is an
isomorphism. By the compatibility of the purity map with base change
(`isIso_upperShriekBaseChange_of_isIso_unit`) this follows from smooth purity for `f` and its base
change `f'` (`isIso_upperShriekUnitTensorMap_of_smooth`) and from the base change of the relative
dualizing complex (`isIso_upperShriekBaseChange_unit_of_smooth`). -/
theorem isIso_upperShriekBaseChange_of_smooth (sq : IsPullback g' f' f g) [Smooth f.left]
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (upperShriekBaseChange ℓ sq L) := by
  have hsq : IsPullback g'.left f'.left f.left g.left := by
    simpa only [Over.forget_map] using sq.map (Over.forget _)
  have : Smooth f'.left := MorphismProperty.of_isPullback hsq inferInstance
  have := isIso_upperShriekUnitTensorMap_of_smooth ℓ f L
  have := isIso_upperShriekUnitTensorMap_of_smooth ℓ f'
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L)
  have := isIso_upperShriekBaseChange_unit_of_smooth ℓ sq
  exact isIso_upperShriekBaseChange_of_isIso_unit ℓ sq L

end General

/-- The exceptional base change map of the product square at the unit,
`Lp_Y^* ω_Y = Lp_Y^* Ra_Y^! ℚ̄_ℓ ⟶ Rp_X^! La_X^* ℚ̄_ℓ ≅ Rp_X^! ℚ̄_ℓ`. -/
noncomputable def prodUpperShriekBaseChangeUnit :
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj (dualizingComplex' ℓ Y) ⟶
      (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj (𝟙_ _) :=
  upperShriekBaseChange ℓ (isPullback_prod_toPoint X Y) (𝟙_ _) ≫
    (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv

/-- Transposing the base change map at the unit gives the inverse compact-support base
change, followed by the pulled-back counit and the monoidal unit isomorphism. -/
private lemma prodUpperShriekBaseChangeUnit_homEquiv_symm :
    ((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : X ⨯ Y ⟶ X)).homEquiv _ _).symm
        (prodUpperShriekBaseChangeUnit ℓ (X := X) (Y := Y)) =
      (prodBaseChangeIso ℓ X Y).hom.app (dualizingComplex' ℓ Y) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_prod_toPoint X Y)
  rw [prodUpperShriekBaseChangeUnit, upperShriekBaseChange,
    Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_apply, Category.assoc]
  congr 1
  simp only [prodBaseChangeIso, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]

/-- The exceptional Künneth map `α : Lp_X^* M ⊗ Lp_Y^* ω_Y ⟶ Rp_X^! M` factors as the exceptional
base change map of the product square at the unit, `Lp_Y^* ω_Y ⟶ Rp_X^! ℚ̄_ℓ`, followed by the
purity map `γ_{p_X, M} : Lp_X^* M ⊗ Rp_X^! ℚ̄_ℓ ⟶ Rp_X^! M`. -/
lemma exceptionalKunnethMap_eq (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    exceptionalKunnethMap ℓ (Y := Y) M =
      (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ◁
          prodUpperShriekBaseChangeUnit ℓ ≫
        upperShriekUnitTensorMap ℓ (prod.fst : X ⨯ Y ⟶ X) M := by
  have hx := prodUpperShriekBaseChangeUnit_homEquiv_symm ℓ (X := X) (Y := Y)
  have hx' := ((boundedConstructibleUpperShriekAdjunction ℓ
    (prod.fst : X ⨯ Y ⟶ X)).homEquiv_counit
      (g := prodUpperShriekBaseChangeUnit ℓ (X := X) (Y := Y))).symm.trans hx
  have key := exceptionalKunnethMap_factorization_aux
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)) M
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)
    (prodUpperShriekBaseChangeUnit ℓ)
    (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
        (dualizingComplex' ℓ Y))).app M)
    (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
      ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj (𝟙_ _))).app M)
    (boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ _
      (prodUpperShriekBaseChangeUnit ℓ) M)
    ((prodBaseChangeIso ℓ X Y).hom.app (dualizingComplex' ℓ Y))
    ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv
    ((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : X ⨯ Y ⟶ X)).counit.app (𝟙_ _)) hx'
  rw [exceptionalKunnethMap, exceptionalKunnethAdjoint, key,
    Adjunction.homEquiv_naturality_left]
  rfl

/-- **Purity for a smooth projection** (blueprint `theorem-sp-qbar`,
`proposition-compatibility-purity-base-change`). Let `Y` be smooth over `k`. The exceptional Künneth
map
```
α : Lp_X^* M ⊗ᴸ Lp_Y^* ω_Y ⟶ Rp_X^! M
```
of the projection `p_X : X ⨯ Y ⟶ X` (`exceptionalKunnethMap`) is an isomorphism for every bounded
constructible `M` on `X`: it is the exceptional base change map of the product square at the unit
followed by the purity map of `p_X` (`exceptionalKunnethMap_eq`), and both are isomorphisms since
`a_Y` and its base change `p_X` are smooth (`isIso_upperShriekBaseChange_of_smooth`,
`isIso_upperShriekUnitTensorMap_of_smooth`). -/
theorem isIso_exceptionalKunnethMap_of_smooth [Smooth Y.hom]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (exceptionalKunnethMap ℓ (Y := Y) M) := by
  have : Smooth (toPoint Y).left := by rw [toPoint_left]; infer_instance
  have : Smooth (prod.fst : X ⨯ Y ⟶ X).left :=
    MorphismProperty.of_isPullback (isPullback_prod_left X Y).flip inferInstance
  have := isIso_upperShriekBaseChange_of_smooth ℓ (isPullback_prod_toPoint X Y) (𝟙_ _)
  have := isIso_upperShriekUnitTensorMap_of_smooth ℓ (prod.fst : X ⨯ Y ⟶ X) M
  rw [exceptionalKunnethMap_eq]
  dsimp only [prodUpperShriekBaseChangeUnit]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
