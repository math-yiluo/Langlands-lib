/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardData

/-!
# Coefficient changes of the bounded constructible six functors

Let `Λ` and `Λ'` be coefficient rings with pushforward data `P` and `P'`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`: the functors `Rf_*` and the
adjunctions `Lf^* ⊣ Rf_*`). A *coefficient change* `Λ ⟶ Λ'`
(`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`) packages the data entering the
coefficient compatibilities of blueprint `sk-thm-sf-compatibility` (7):

* functors `T_X : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ'⟧` (extension of scalars) and commutation squares
  **(Pull)** `Lf^* ⋙ T_X ≅ T_Y ⋙ Lf^*`, given as parameters, so that they appear unfolded in the
  statements of the compatibilities;
* the compatibility of (Pull) with the composition isomorphisms of the pullbacks;
* commutation squares **(Shriek)** `j_! ⋙ T_X ≅ T_U ⋙ j_!` for open immersions `j`, whose mates
  for `j_! ⊣ Lj^*` are (Pull) for `j`;
* commutation squares **(Push)** `Rp_* ⋙ T_Y ≅ T_Z ⋙ Rp_*` for proper `p`, the mates of (Pull)
  for `Lp^* ⊣ Rp_*`.

From these, the formal compatibilities follow
(`WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate`); this file proves the one with
the pullback comparisons `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of commutative squares
(`BoundedConstructibleCoefficientChange.squareCompatible_pullbackSquareComparison`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (ℓ : ℕ) [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (P : BoundedConstructiblePushforwardData Λ ℓ k)
  (P' : BoundedConstructiblePushforwardData Λ' ℓ k)
  (T : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom], Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧)
  (pull : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T X ≅ T Y ⋙ boundedConstructibleUpperStar Λ' ℓ f)

/-- A *coefficient change* `Λ ⟶ Λ'` of the bounded constructible six functors, for pushforward
data `P` and `P'`, along the functors `T_X : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ'⟧` with the commutation squares
(Pull) `pull` with the pullbacks: (Pull) is compatible with the composition isomorphisms, and
there are commutation squares (Shriek) with the extensions by zero along open immersions, mated
with (Pull), and (Push) with the pushforwards along proper morphisms, mated with (Pull). -/
structure BoundedConstructibleCoefficientChange where
  /-- (Pull) is compatible with the composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
  pull_comp {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    NatTrans.SquareCompatible (pull (f ≫ g)) (Functor.pasteSquareIso (pull g) (pull f))
      (boundedConstructibleUpperStarComp Λ ℓ f g).hom
      (boundedConstructibleUpperStarComp Λ' ℓ f g).hom
  /-- **(Shriek)** `j_! ⋙ T_X ≅ T_U ⋙ j_!` for an open immersion `j`. -/
  shriek {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ T X ≅
      T U ⋙ boundedConstructibleOpenImmersionLowerShriek Λ' ℓ j
  /-- (Pull) for an open immersion `j` is the mate of the inverse of (Shriek). -/
  isMateSquare_shriek_pull {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (j : U ⟶ X) [IsOpenImmersion j.left] :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).IsMateSquare
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ j) (shriek j) (pull j)
  /-- **(Push)** `Rp_* ⋙ T_Y ≅ T_Z ⋙ Rp_*` for a proper `p`. -/
  push {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    P.lowerStar p ⋙ T Y ≅ T Z ⋙ P'.lowerStar p
  /-- (Push) is the mate of the inverse of (Pull). -/
  isMateSquare_pull_push {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (p : Z ⟶ Y) [IsProper p.left] :
    (P.adj p).IsMateSquare (P'.adj p) (pull p) (push p)

namespace BoundedConstructibleCoefficientChange

variable {Λ Λ' ℓ P P' T pull} (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)

section Pull

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

variable (pull) in
/-- (Pull) is compatible with the identifications `Lm^* = Lm'^*` for equal morphisms. -/
lemma squareCompatible_eqToHom {m m' : X ⟶ Y} (h : m = m')
    (h₁ : boundedConstructibleUpperStar Λ ℓ m = boundedConstructibleUpperStar Λ ℓ m')
    (h₂ : boundedConstructibleUpperStar Λ' ℓ m = boundedConstructibleUpperStar Λ' ℓ m') :
    NatTrans.SquareCompatible (pull m) (pull m') (eqToHom h₁) (eqToHom h₂) := by
  subst h
  simpa only [eqToHom_refl] using NatTrans.SquareCompatible.id (pull m)

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- (Pull) is compatible with the pullback comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a
commutative square. -/
lemma squareCompatible_pullbackSquareComparison
    (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull) (sq : CommSq g' f' f g) :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (pull g) (pull f'))
      (Functor.pasteSquareIso (pull f) (pull g'))
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom
      (boundedConstructiblePullbackSquareComparison Λ' ℓ sq).hom := by
  have h := NatTrans.SquareCompatible.comp
    (NatTrans.SquareCompatible.inv (e := boundedConstructibleUpperStarComp Λ ℓ f' g)
      (e' := boundedConstructibleUpperStarComp Λ' ℓ f' g) (C.pull_comp f' g))
    (NatTrans.SquareCompatible.comp
      (squareCompatible_eqToHom pull sq.w.symm (by rw [sq.w]) (by rw [sq.w]))
      (C.pull_comp g' f))
  simpa only [boundedConstructiblePullbackSquareComparison, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom] using h

end Pull

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
