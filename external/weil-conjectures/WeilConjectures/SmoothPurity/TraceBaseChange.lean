/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationBaseChange

/-!

# Compatibility of the smooth trace with base change

Let `f : X ⟶ Y` be smooth of pure relative dimension `d` and consider a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type. The smooth trace `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is compatible with base change (SGA 4,
Exposé XVIII, Théorème 2.9 (Var 4)): pulled back along `g` and read through compact-support base
change `Lg^* Rf_! ≅ Rf'_! Lg'^*`, it is the trace of `f'`, up to the identification
`Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists.

The smooth trace is the composite `Tr_f ∘ Rf_!(γ_f)` of the orientation and the counit of
`Rf_! ⊣ Rf^!` (`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace_eq`), so the compatibility
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_iso_smoothTrace_baseChange`, blueprint
`proposition-compatibility-purity-base-change`, trace form) follows from two facts:

- the counit of `Rf_! ⊣ Rf^!` commutes with base change, through the exceptional base change
  map, which is its mate
  (`AlgebraicGeometry.ProEtale.CondensedRing.homEquiv_symm_map_comp_upperShriekBaseChange`);
- the orientation `γ_f` commutes with base change
  (`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation_baseChange`, blueprint
  `proposition-compatibility-purity-base-change` at the unit, owed by the smooth purity section).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The counit of `Rf_! ⊣ Rf^!` is compatible with base change**: for `φ : A ⟶ Rf^! L`, the
exceptional adjoint (for `Rf'_! ⊣ Rf'^!`) of `Lg'^* φ` followed by the exceptional base change
map is the pullback of the adjoint `Rf_! A ⟶ L` of `φ`, read through compact-support base change:
```
Rf'_! Lg'^* A ≅ Lg^* Rf_! A --Lg^* Rf_! φ--> Lg^* Rf_! Rf^! L --Lg^* ε--> Lg^* L.
```
-/
lemma homEquiv_symm_map_comp_upperShriekBaseChange (sq : IsPullback g' f' f g)
    {A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : A ⟶ (boundedConstructibleUpperShriek ℓ f).obj L) :
    haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
    ((boundedConstructibleUpperShriekAdjunction ℓ f').homEquiv _ _).symm
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map φ ≫
          upperShriekBaseChange ℓ sq L) =
      inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app A) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleLowerShriek ℓ f).map φ ≫
            (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app L) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  -- naturality of compact-support base change at `φ`
  have hβ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality φ
  rw [Functor.comp_map, Functor.comp_map, ← IsIso.eq_comp_inv, Category.assoc,
    ← IsIso.inv_comp_eq] at hβ
  rw [Adjunction.homEquiv_naturality_left_symm, upperShriekBaseChange, Equiv.symm_apply_apply,
    ← Category.assoc, ← hβ, Category.assoc, ← Functor.map_comp]

/-- Blueprint `proposition-compatibility-purity-base-change`, trace form (owed by the smooth purity
section, `chap-Smooth-purity`): **the smooth trace is compatible with base change** (SGA 4, Exposé
XVIII, Théorème 2.9 (Var 4)), deduced from the compatibility of the orientation
(`smoothOrientation_baseChange`) and of the counit with base change. For a cartesian square
with `f` (hence `f'`) smooth of pure relative dimension `d`, the trace of `f'` is, up to an
isomorphism `Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists, the pullback of the trace
of `f` read through compact-support base change:
```
Rf'_! Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ Lg^* Rf_! ℚ̄_ℓ,X(d)[2d] --Lg^* Tr_f--> Lg^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Y'.
```
-/
theorem exists_iso_smoothTrace_baseChange (sq : IsPullback g' f' f g) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
      (boundedConstructibleLowerShriek ℓ f').map τ.hom ≫ smoothTrace ℓ f' d =
        inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
            (boundedConstructibleTateTwist ℓ X d (2 * d))) ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
            (smoothTrace ℓ f d) ≫
          η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) := by
  obtain ⟨τ, hτ⟩ := smoothOrientation_baseChange ℓ sq d
  refine ⟨τ, ?_⟩
  have h : (boundedConstructibleLowerShriek ℓ f').map τ.hom ≫ smoothTrace ℓ f' d =
      ((boundedConstructibleUpperShriekAdjunction ℓ f').homEquiv _ _).symm
        (τ.hom ≫ smoothOrientation ℓ f' d) := by
    rw [smoothTrace_eq, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [h, ← hτ, ← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_map_comp_upperShriekBaseChange, smoothTrace_eq, Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
