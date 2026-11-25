/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# Components of the pullback comparison of a commutative square

The components of `ProEtale.CondensedRing.boundedConstructiblePullbackSquareComparison` in terms
of the composition isomorphisms of the derived pullback.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The components of the inverse of the pullback comparison of a commutative square. -/
lemma boundedConstructiblePullbackSquareComparison_inv_app (sq : CommSq g' f' f g)
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq).inv.app K =
      (boundedConstructibleUpperStarComp Λ ℓ g' f).inv.app K ≫ eqToHom (by rw [sq.w]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ f' g).hom.app K := by
  simp only [boundedConstructiblePullbackSquareComparison, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, Category.assoc]

omit [MonObj Λ] [IsCommMonObj Λ] [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- An isomorphism whose inverse is `u⁻¹ ≫ (cast) ≫ v` has `v⁻¹ ≫ (cast) ≫ u` as its forward
morphism. -/
lemma Iso.hom_eq_of_inv_eq_aux {C : Type*} [Category C] {P Q A B : C} (e : P ≅ Q) (u : B ≅ Q)
    (v : A ≅ P) (p : B = A) (h : e.inv = u.inv ≫ eqToHom p ≫ v.hom) :
    e.hom = v.inv ≫ eqToHom p.symm ≫ u.hom := by
  subst p
  rw [← cancel_epi e.inv, Iso.inv_hom_id, h]
  simp

/-- The components of the pullback comparison of a commutative square. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app (sq : CommSq g' f' f g)
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K =
      (boundedConstructibleUpperStarComp Λ ℓ f' g).inv.app K ≫ eqToHom (by rw [sq.w]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ g' f).hom.app K :=
  Iso.hom_eq_of_inv_eq_aux ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).app K)
    ((boundedConstructibleUpperStarComp Λ ℓ g' f).app K)
    ((boundedConstructibleUpperStarComp Λ ℓ f' g).app K) _
    (boundedConstructiblePullbackSquareComparison_inv_app Λ ℓ sq K)

end AlgebraicGeometry.ProEtale.CondensedRing
