/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionAssoc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-!

# Coherence of the lower shriek on bounded constructible `ℚ̄_ℓ`-sheaves

This file records the coherence of the compactly supported direct image `Rf_!` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` with its composition isomorphisms, with the
identification `Rf_! ≅ Rf_*` for proper `f` and with the compact-support base-change morphism
`Ex_!`, and derives the formal consequences used by the Frobenius comparison of the trace
formula.

## Main statements

The following clauses of the six-functor package, proved in
`…LowerShriek.CompositionAssoc`, `…LowerShriek.CompositionUnit` and `…LowerShriek.BaseChangeMate`:

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_assoc`,
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_id_left` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_id_right`: the
  associativity and identity equations of the composition isomorphisms
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (blueprint `prop-functor-package`, clause (3)).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp`: the
  identification `Rf_! ≅ Rf_*` of a proper `f` is compatible with composition (blueprint
  `prop-functor-package`, clause (3)).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv`:
  for a cartesian square whose horizontal maps are proper, `Ex_!` is the mate of the composition
  isomorphism `Rg'_! ⋙ Rf_! ≅ R(g' ≫ f)_! = R(f' ≫ g)_! ≅ Rf'_! ⋙ Rg_!` (blueprint
  `proposition-composition-base-change-rf-shriek`, clause (4)).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl`: the
  adjunction `Lf^* ⊣ Rf_!` of a proper `f`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Composition

variable {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **Associativity of the composition isomorphisms of the lower shriek** (blueprint
`proposition-composition-base-change-rf-shriek--2`, clause (3)): the two identifications of
`R(f ≫ g ≫ h)_!` with `Rf_! ⋙ Rg_! ⋙ Rh_!` agree. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_assoc (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (K : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (f ≫ g) h).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ h).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K) =
      eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (g ≫ h)).hom.app K ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) :=
  boundedConstructibleLowerShriekComp_padicAlgCl_assoc' ℓ f g h K

/-- **Left identity equation of the composition isomorphisms of the lower shriek** (blueprint
`proposition-composition-base-change-rf-shriek--3`, clause (3)):
`R(𝟙 ≫ f)_! ≅ R(𝟙)_! ⋙ Rf_! ≅ R(𝟙)_* ⋙ Rf_! ≅ Rf_!` is the identity. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_id_left (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) f).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X)).hom.app K ≫
            (boundedConstructibleLowerStarId ℓ X).hom.app K) =
      eqToHom (by rw [Category.id_comp]; rfl) :=
  boundedConstructibleLowerShriekComp_padicAlgCl_id_left' ℓ f K

/-- **Right identity equation of the composition isomorphisms of the lower shriek** (blueprint
`proposition-composition-base-change-rf-shriek--3`, clause (3)):
`R(f ≫ 𝟙)_! ≅ Rf_! ⋙ R(𝟙)_! ≅ Rf_! ⋙ R(𝟙)_* ≅ Rf_!` is the identity. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_id_right (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 Y)).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleLowerStarId ℓ Y).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) =
      eqToHom (by rw [Category.comp_id]; rfl) :=
  boundedConstructibleLowerShriekComp_padicAlgCl_id_right' ℓ f K

/-- **The identification `Rf_! ≅ Rf_*` is compatible with composition** (blueprint
`prop-functor-package`, clause (3)): for proper `f` and `g`,
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_! ≅ Rf_* ⋙ Rg_*` is `R(f ≫ g)_! ≅ R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`. -/
theorem boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleLowerStar ℓ g).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g)).hom.app K ≫
        (boundedConstructibleLowerStarComp ℓ f g).inv.app K :=
  boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp' ℓ f g K

end Composition

section Adjunction

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The adjunction `Lf^* ⊣ Rf_!` of a proper morphism `f` on bounded constructible
`ℚ̄_ℓ`-sheaves: the adjunction `Lf^* ⊣ Rf_*` transported along `Rf_! ≅ Rf_*`. -/
noncomputable def boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl (f : X ⟶ Y)
    [IsProper f.left] :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⊣
      boundedConstructibleLowerShriek ℓ f :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ
    f).ofNatIsoRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).symm

end Adjunction

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The composition isomorphism `Rg'_! ⋙ Rf_! ≅ R(g' ≫ f)_! = R(f' ≫ g)_! ≅ Rf'_! ⋙ Rg_!` of a
commutative square `g' ≫ f = f' ≫ g`, as a 2-square. -/
noncomputable def boundedConstructibleLowerShriekSquareIso_padicAlgCl (w : g' ≫ f = f' ≫ g) :
    boundedConstructibleLowerShriek ℓ g' ⋙
        boundedConstructibleLowerShriek ℓ f ≅
      boundedConstructibleLowerShriek ℓ f' ⋙
        boundedConstructibleLowerShriek ℓ g :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g' f).symm ≪≫ eqToIso (by rw [w]) ≪≫
    boundedConstructibleLowerShriekComp_padicAlgCl ℓ f' g

/-- **`Ex_!` is the mate of the composition isomorphism** (blueprint
`proposition-composition-base-change-rf-shriek`, clause (4)): for a cartesian square
`sq : g' ≫ f = f' ≫ g` with `g` and `g'` proper, the compact-support base-change morphism
`Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is the mate, for the adjunctions `Lg'^* ⊣ Rg'_!` and
`Lg^* ⊣ Rg_!`, of the composition isomorphism
`Rg'_! ⋙ Rf_! ≅ R(g' ≫ f)_! = R(f' ≫ g)_! ≅ Rf'_! ⋙ Rg_!`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv
    (sq : IsPullback g' f' f g) [IsProper g.left] [IsProper g'.left] :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      (mateEquiv (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g')
        (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g)).symm
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ sq.w).hom :=
  boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv' ℓ sq

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
