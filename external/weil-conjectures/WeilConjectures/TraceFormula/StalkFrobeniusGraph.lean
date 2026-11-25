/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces

/-!

# The local Frobenius as a stalk map of the graph correspondence

Let `(K, φ)` be a Weil object on `X` for `Φ`, `m ≥ 1` and `x` a rational point fixed by `Φ_m`.
The local Frobenius `F_{x,m}` on the stalk `K_x` is the stalk map at `x` of the coefficient map
`φ_m : LΦ_m^* K ⟶ K` of the graph correspondence `c_m = (𝟙, Φ_m)`
(`ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius_eq_graphStalkMap`). This
identifies the local term of the Frobenius correspondence with the trace of the local Frobenius
(blueprint `proposition-frobenius-local-term-curve--1`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X}

set_option backward.isDefEq.respectTransparency true in
/-- The Frobenius of the stalk at a rational point `x` fixed by `Ψ` of a Weil object `(L, ψ)` for
`Ψ` is the stalk map `ψ_x : L_x ⟶ L_x` of the graph correspondence `(𝟙, Ψ)`. -/
lemma weilStalk_obj_frobenius_hom_eq_graphStalkMap {Ψ : X ⟶ X} (x : RationalPoint X)
    (hx : x ≫ Ψ = x) (L : WeilBoundedConstructible ℓ Ψ) :
    ((weilStalk ℓ Ψ x hx).obj L).frobenius.hom =
      Correspondence.graphStalkMap L.carrier Ψ L.str.hom x hx := by
  have hid := boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ x
    L.carrier
  have hid' : (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj L.carrier) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k)) x).inv.app
        L.carrier = eqToHom (by rw [Category.id_comp]; rfl) := by
    rw [← cancel_epi ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ
      (point k)).hom.app _), Iso.hom_inv_id_app_assoc, ← cancel_epi
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k)) x).hom.app
        L.carrier), Iso.hom_inv_id_app, reassoc_of% hid, eqToHom_trans, eqToHom_refl]
  have key : (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj L.carrier) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k)) x).inv.app
        L.carrier ≫ eqToHom (by rw [Category.id_comp, hx]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x Ψ).hom.app
        L.carrier ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          L.str.hom =
      eqToHom (by rw [hx]; rfl) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x Ψ).hom.app
        L.carrier ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          L.str.hom := by
    rw [reassoc_of% hid', eqToHom_trans_assoc]
  rw [weilStalk_obj_frobenius_hom]
  unfold weilStalk
  rw [weilUpperStar_obj_str, Iso.trans_hom, Iso.app_hom, weilUpperStarComparison_hom_app,
    Functor.mapIso_hom, Correspondence.graphStalkMap]
  simp only [Category.assoc]
  exact key

set_option backward.isDefEq.respectTransparency true in
/-- The local Frobenius `F_{x,m}` is the stalk map at `x` of the iterate `φ_m : LΦ_m^* K ⟶ K`. -/
lemma stalkFrobenius_eq_graphStalkMap (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    K.stalkFrobenius m x hx =
      Correspondence.graphStalkMap K.carrier (frobeniusIterate Φ m) (K.iterateStr m).hom x hx := by
  have h := weilStalk_obj_frobenius_hom_eq_graphStalkMap x hx (K.iterate m)
  rw [iterate_str, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.hom,
    Correspondence.graphStalkMap_eqToHom (K.iterate_carrier m)] at h
  have key : eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        x).obj (K.iterate_carrier m).symm) ≫
      (eqToHom (by rw [K.iterate_carrier m]) ≫ Correspondence.graphStalkMap K.carrier
        (frobeniusIterate Φ m) (K.iterateStr m).hom x hx ≫ eqToHom (by rw [K.iterate_carrier m])) ≫
      eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        (K.iterate_carrier m)) =
      Correspondence.graphStalkMap K.carrier (frobeniusIterate Φ m) (K.iterateStr m).hom x hx := by
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  rw [stalkFrobenius]
  unfold iterateStalk
  rw [h]
  exact key

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
