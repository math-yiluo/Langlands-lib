/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange

/-!
# The Frobenius coherence of the base change to geometric fibres

`WeilConjectures.WeilSheaf.CondensedModelBaseChange` reduces the Weil-structure version of the
base change of `Rf_!` to geometric fibres to a Frobenius compatibility of the pullback comparison
(`AlgebraicGeometry.ProEtale.CondensedRing.UpperStarWeilCompatible`). This file proves the
coherences behind it, for module objects over a condensed ring `Λ`:

- the pseudofunctor coherences of the pushforwards `lowerStarComp`, `lowerStarCongr` and
  `lowerStarId`, and the unit and counit of the equivalence `lowerStarEquivalenceOfIso`;
- the mate of the Frobenius exchange of the pushforward along the adjunctions `(F⁻¹)_* ⊣ F_*`
  (`AlgebraicGeometry.ProEtale.CondensedRing.leftMateIso_lowerStarFrobeniusExchange`);
- the Frobenius compatibility of the comparison `φ^* pX^* ≅ pY^* φ'^*` for a commutative square
  with Frobenius-invariant projections
  (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarSquareComparison_inv_app_frobenius`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

section LowerStarCoherence

variable {X Y Z V : Scheme.{u}}

/-- Transport of the pushforward along `a = b` and then along `b = c` is transport along
`a = c`. -/
@[reassoc (attr := simp)]
lemma lowerStarCongr_hom_app_trans {a b c : X ⟶ Y} (e₁ : a = b) (e₂ : b = c)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarCongr Λ e₁).hom.app M ≫ (lowerStarCongr Λ e₂).hom.app M =
      (lowerStarCongr Λ (e₁.trans e₂)).hom.app M := by
  subst e₁ e₂
  exact Category.comp_id _

/-- Transport of the pushforward along `a = a` is the identity. -/
@[simp]
lemma lowerStarCongr_hom_app_self {a : X ⟶ Y} (e : a = a)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarCongr Λ e).hom.app M = 𝟙 _ :=
  rfl

/-- Transports along two proofs of the same equality agree. -/
lemma lowerStarCongr_proof_irrel {a b : X ⟶ Y} (e e' : a = b)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarCongr Λ e).hom.app M = (lowerStarCongr Λ e').hom.app M :=
  rfl

/-- The inverse of the transport along `a = b` is the transport along `b = a`. -/
lemma lowerStarCongr_inv_app {a b : X ⟶ Y} (e : a = b)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarCongr Λ e).inv.app M = (lowerStarCongr Λ e.symm).hom.app M := by
  subst e
  rfl

/-- The associativity law of the composition isomorphisms of the pushforwards, evaluated at a
module object. -/
@[reassoc]
lemma lowerStarComp_hom_app_comp_lowerStarComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ g h).hom.app ((f)_*⟦Λ⟧.obj M) ≫ (lowerStarComp Λ f (g ≫ h)).hom.app M =
      (h)_*⟦Λ⟧.map ((lowerStarComp Λ f g).hom.app M) ≫ (lowerStarComp Λ (f ≫ g) h).hom.app M ≫
        (lowerStarCongr Λ (Category.assoc f g h)).hom.app M := by
  have := congrArg (fun e ↦ e.hom.app M) (lowerStarComp_assoc Λ f g h)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp] using this

/-- The left unit law of the composition isomorphisms of the pushforwards, evaluated at a module
object. -/
lemma lowerStarComp_id_left_hom_app (t : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ (𝟙 X) t).hom.app M = (t)_*⟦Λ⟧.map ((lowerStarId Λ X).hom.app M) ≫
      (lowerStarCongr Λ (Category.id_comp t).symm).hom.app M := by
  rw [lowerStarComp_id_left, lowerStarCongr_symm]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- The right unit law of the composition isomorphisms of the pushforwards, evaluated at a module
object. -/
@[reassoc]
lemma lowerStarComp_id_right_hom_app (t : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ t (𝟙 Y)).hom.app M = (lowerStarId Λ Y).hom.app ((t)_*⟦Λ⟧.obj M) ≫
      (lowerStarCongr Λ (Category.comp_id t).symm).hom.app M := by
  rw [lowerStarComp_id_right, lowerStarCongr_symm]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- The composition isomorphism `a_* ⋙ y_* ≅ (a ≫ y)_*` is natural in `a` with respect to the
transports along equalities. -/
@[reassoc]
lemma lowerStar_map_lowerStarCongr_hom_app_comp_lowerStarComp_hom_app {a b : X ⟶ Y} (e : a = b)
    (y : Y ⟶ Z) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (y)_*⟦Λ⟧.map ((lowerStarCongr Λ e).hom.app M) ≫ (lowerStarComp Λ b y).hom.app M =
      (lowerStarComp Λ a y).hom.app M ≫ (lowerStarCongr Λ (congrArg (· ≫ y) e)).hom.app M := by
  subst e
  simp

/-- The composition isomorphism `x_* ⋙ a_* ≅ (x ≫ a)_*` is natural in `a` with respect to the
transports along equalities. -/
@[reassoc]
lemma lowerStarCongr_hom_app_comp_lowerStarComp_hom_app (x : X ⟶ Y) {a b : Y ⟶ Z} (e : a = b)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarCongr Λ e).hom.app ((x)_*⟦Λ⟧.obj M) ≫ (lowerStarComp Λ x b).hom.app M =
      (lowerStarComp Λ x a).hom.app M ≫ (lowerStarCongr Λ (congrArg (x ≫ ·) e)).hom.app M := by
  subst e
  simp

/-- The associativity law of the composition isomorphisms of the pushforwards, solved for
`h_* (f, g) ≫ (f ≫ g, h)`. -/
@[reassoc]
lemma lowerStar_map_lowerStarComp_hom_app_comp_lowerStarComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ V) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (h)_*⟦Λ⟧.map ((lowerStarComp Λ f g).hom.app M) ≫ (lowerStarComp Λ (f ≫ g) h).hom.app M =
      (lowerStarComp Λ g h).hom.app ((f)_*⟦Λ⟧.obj M) ≫ (lowerStarComp Λ f (g ≫ h)).hom.app M ≫
        (lowerStarCongr Λ (Category.assoc f g h).symm).hom.app M := by
  rw [lowerStarComp_hom_app_comp_lowerStarComp_hom_app_assoc, lowerStarCongr_hom_app_trans,
    lowerStarCongr_hom_app_self, Category.comp_id]

/-- The left unit law of the composition isomorphisms of the pushforwards, solved for the
pushforward of the identity isomorphism. -/
lemma lowerStar_map_lowerStarId_hom_app (t : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (t)_*⟦Λ⟧.map ((lowerStarId Λ X).hom.app M) = (lowerStarComp Λ (𝟙 X) t).hom.app M ≫
      (lowerStarCongr Λ (Category.id_comp t)).hom.app M := by
  rw [lowerStarComp_id_left_hom_app, Category.assoc, lowerStarCongr_hom_app_trans]
  exact (Category.comp_id _).symm

/-- The inverse of the composition isomorphism `a_* ⋙ y_* ≅ (a ≫ y)_*` is natural in `a` with
respect to the transports along equalities. -/
@[reassoc]
lemma lowerStarComp_inv_app_comp_map_lowerStarCongr_hom_app {a b : X ⟶ Y} (e : a = b)
    (y : Y ⟶ Z) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ a y).inv.app M ≫ (y)_*⟦Λ⟧.map ((lowerStarCongr Λ e).hom.app M) =
      (lowerStarCongr Λ (congrArg (· ≫ y) e)).hom.app M ≫ (lowerStarComp Λ b y).inv.app M := by
  subst e
  simp

/-- The inverse of the composition isomorphism `x_* ⋙ y_* ≅ (x ≫ y)_*` is natural. -/
@[reassoc]
lemma lowerStarComp_inv_app_comp_map_map (x : X ⟶ Y) (y : Y ⟶ Z)
    {M M' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (s : M ⟶ M') :
    (lowerStarComp Λ x y).inv.app M ≫ (y)_*⟦Λ⟧.map ((x)_*⟦Λ⟧.map s) =
      (x ≫ y)_*⟦Λ⟧.map s ≫ (lowerStarComp Λ x y).inv.app M' :=
  ((lowerStarComp Λ x y).inv.naturality s).symm

/-- The associativity law of the composition isomorphisms of the pushforwards, for the inverse
isomorphisms. -/
@[reassoc]
lemma lowerStarComp_inv_app_comp_map_lowerStarComp_inv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ V) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ (f ≫ g) h).inv.app M ≫ (h)_*⟦Λ⟧.map ((lowerStarComp Λ f g).inv.app M) =
      (lowerStarCongr Λ (Category.assoc f g h)).hom.app M ≫
        (lowerStarComp Λ f (g ≫ h)).inv.app M ≫ (lowerStarComp Λ g h).inv.app ((f)_*⟦Λ⟧.obj M) := by
  have := congrArg Iso.inv (Iso.ext (lowerStar_map_lowerStarComp_hom_app_comp_lowerStarComp_hom_app
    Λ f g h M) : (h)_*⟦Λ⟧.mapIso ((lowerStarComp Λ f g).app M) ≪≫
      (lowerStarComp Λ (f ≫ g) h).app M = (lowerStarComp Λ g h).app ((f)_*⟦Λ⟧.obj M) ≪≫
        (lowerStarComp Λ f (g ≫ h)).app M ≪≫
          (lowerStarCongr Λ (Category.assoc f g h).symm).app M)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at this
  rw [this, lowerStarCongr_inv_app]

variable [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- A unit coherence of the pushforwards: for `e : 𝟙 = b ≫ c`, the composite
`φ_* P ≅ (𝟙)_* φ_* P ≅ (b ≫ c)_* φ_* P ≅ c_* b_* φ_* P ≅ c_* (φ ≫ b)_* P ≅ ((φ ≫ b) ≫ c)_* P`
is a transport. -/
lemma lowerStarId_inv_app_comp_lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app
    (φ : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ Y) (e : 𝟙 Y = b ≫ c) (e' : φ = (φ ≫ b) ≫ c)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarId Λ Y).inv.app ((φ)_*⟦Λ⟧.obj P) ≫ (lowerStarCongr Λ e).hom.app _ ≫
        (lowerStarComp Λ b c).inv.app _ ≫ (c)_*⟦Λ⟧.map ((lowerStarComp Λ φ b).hom.app P) ≫
          (lowerStarComp Λ (φ ≫ b) c).hom.app P =
      (lowerStarCongr Λ e').hom.app P := by
  rw [lowerStar_map_lowerStarComp_hom_app_comp_lowerStarComp_hom_app, Iso.inv_hom_id_app_assoc,
    lowerStarCongr_hom_app_comp_lowerStarComp_hom_app_assoc,
    lowerStarComp_id_right_hom_app_assoc, Iso.inv_hom_id_app_assoc,
    lowerStarCongr_hom_app_trans_assoc, lowerStarCongr_hom_app_trans]

omit [IsCommMonObj Λ] in
/-- The form of
`lowerStarId_inv_app_comp_lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app` with the last
composition isomorphism inverted. -/
@[reassoc]
lemma lowerStarId_inv_app_comp_lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app'
    (φ : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ Y) (e : 𝟙 Y = b ≫ c) (e' : φ = (φ ≫ b) ≫ c)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarId Λ Y).inv.app ((φ)_*⟦Λ⟧.obj P) ≫ (lowerStarCongr Λ e).hom.app _ ≫
        (lowerStarComp Λ b c).inv.app _ ≫ (c)_*⟦Λ⟧.map ((lowerStarComp Λ φ b).hom.app P) =
      (lowerStarCongr Λ e').hom.app P ≫ (lowerStarComp Λ (φ ≫ b) c).inv.app P := by
  refine (Iso.eq_comp_inv ((lowerStarComp Λ (φ ≫ b) c).app P)).2 ?_
  simpa only [Category.assoc, Iso.app_hom] using
    lowerStarId_inv_app_comp_lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app Λ φ b c e e' P


omit [IsCommMonObj Λ] in
@[reassoc]
lemma lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app_lowerStarId
    (a : X ⟶ Y) (b : Y ⟶ X) (h : X ⟶ Z) (e : a ≫ b = 𝟙 X) (e' : a ≫ b ≫ h = h)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ b h).inv.app ((a)_*⟦Λ⟧.obj M) ≫ (h)_*⟦Λ⟧.map
        ((lowerStarComp Λ a b).hom.app M ≫ (lowerStarCongr Λ e).hom.app M ≫
          (lowerStarId Λ X).hom.app M) =
      (lowerStarComp Λ a (b ≫ h)).hom.app M ≫ (lowerStarCongr Λ e').hom.app M := by
  refine (Iso.inv_comp_eq ((lowerStarComp Λ b h).app ((a)_*⟦Λ⟧.obj M))).2 ?_
  rw [Iso.app_hom, lowerStarComp_hom_app_comp_lowerStarComp_hom_app_assoc, Functor.map_comp,
    Functor.map_comp, lowerStar_map_lowerStarId_hom_app,
    lowerStar_map_lowerStarCongr_hom_app_comp_lowerStarComp_hom_app_assoc,
    lowerStarCongr_hom_app_trans, lowerStarCongr_hom_app_trans]

omit [IsCommMonObj Λ] in
lemma lowerStarComp_frobeniusMate_app_aux {X Y : Scheme.{u}} (x₁ x₂ : X ⟶ X) (y₁ y₂ : Y ⟶ Y)
    (φ : X ⟶ Y) (hx : x₁ ≫ x₂ = 𝟙 X) (hy : 𝟙 Y = y₂ ≫ y₁) (hφ : φ ≫ y₂ = x₂ ≫ φ)
    (hφ' : x₁ ≫ φ = φ ≫ y₁)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarId Λ Y).inv.app ((φ)_*⟦Λ⟧.obj ((x₁)_*⟦Λ⟧.obj M)) ≫
        (lowerStarCongr Λ hy).hom.app _ ≫ (lowerStarComp Λ y₂ y₁).inv.app _ ≫
        (y₁)_*⟦Λ⟧.map ((lowerStarComp Λ φ y₂).hom.app ((x₁)_*⟦Λ⟧.obj M) ≫
          (lowerStarCongr Λ hφ).hom.app _ ≫ (lowerStarComp Λ x₂ φ).inv.app _) ≫
        (y₁)_*⟦Λ⟧.map ((φ)_*⟦Λ⟧.map ((lowerStarComp Λ x₁ x₂).hom.app M ≫
          (lowerStarCongr Λ hx).hom.app M ≫ (lowerStarId Λ X).hom.app M)) =
      (lowerStarComp Λ x₁ φ).hom.app M ≫ (lowerStarCongr Λ hφ').hom.app M ≫
        (lowerStarComp Λ φ y₁).inv.app ((𝟭 _).obj M) := by
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
    lowerStarId_inv_app_comp_lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app'_assoc Λ φ y₂ y₁
      hy (by rw [Category.assoc, ← hy, Category.comp_id]),
    lowerStarComp_inv_app_comp_map_lowerStarCongr_hom_app_assoc,
    lowerStarComp_inv_app_comp_map_lowerStarComp_inv_app_assoc,
    lowerStarComp_inv_app_comp_map_map,
    lowerStarComp_inv_app_comp_map_lowerStarComp_hom_app_lowerStarId_assoc Λ x₁ x₂ (φ ≫ y₁) hx
      (by rw [← Category.assoc, hx, Category.id_comp]),
    lowerStarCongr_hom_app_trans_assoc, lowerStarCongr_hom_app_trans_assoc,
    lowerStarCongr_hom_app_comp_lowerStarComp_hom_app_assoc]
  rewrite [lowerStarCongr_hom_app_trans_assoc]
  exact congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) (lowerStarCongr_proof_irrel Λ _ _ M) rfl)

omit [IsCommMonObj Λ] in
/-- `lowerStarComp_frobeniusMate_app_aux` with the transports of the unit and counit written as
inverses. -/
lemma lowerStarComp_frobeniusMate_app {X Y : Scheme.{u}} (x₁ x₂ : X ⟶ X) (y₁ y₂ : Y ⟶ Y)
    (φ : X ⟶ Y) (hx : 𝟙 X = x₁ ≫ x₂) (hy : y₂ ≫ y₁ = 𝟙 Y) (hφ : φ ≫ y₂ = x₂ ≫ φ)
    (hφ' : x₁ ≫ φ = φ ≫ y₁)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarId Λ Y).inv.app ((φ)_*⟦Λ⟧.obj ((x₁)_*⟦Λ⟧.obj M)) ≫
        (lowerStarCongr Λ hy).inv.app _ ≫ (lowerStarComp Λ y₂ y₁).inv.app _ ≫
        (y₁)_*⟦Λ⟧.map ((lowerStarComp Λ φ y₂).hom.app ((x₁)_*⟦Λ⟧.obj M) ≫
          (lowerStarCongr Λ hφ).hom.app _ ≫ (lowerStarComp Λ x₂ φ).inv.app _) ≫
        (y₁)_*⟦Λ⟧.map ((φ)_*⟦Λ⟧.map ((lowerStarComp Λ x₁ x₂).hom.app M ≫
          (lowerStarCongr Λ hx).inv.app M ≫ (lowerStarId Λ X).hom.app M)) =
      (lowerStarComp Λ x₁ φ).hom.app M ≫ (lowerStarCongr Λ hφ').hom.app M ≫
        (lowerStarComp Λ φ y₁).inv.app ((𝟭 _).obj M) := by
  exact (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) (lowerStarCongr_inv_app Λ hy _)
    (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) rfl (congrArg (lowerStar Λ y₁).map
      (congrArg (lowerStar Λ φ).map (congrArg₂ (· ≫ ·) rfl
        (congrArg₂ (· ≫ ·) (lowerStarCongr_inv_app Λ hx M) rfl)))))))).trans
    (lowerStarComp_frobeniusMate_app_aux Λ x₁ x₂ y₁ y₂ φ _ _ hφ hφ' M)

end LowerStarCoherence

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- Naturality of a whiskered natural transformation, at a morphism into an object in the
image of the whiskering functor. -/
@[reassoc]
lemma map_comp_whiskerLeft_app {F H : C ⥤ D} (α : F ⟶ H) (G : B ⥤ C) {X : C} {Q : B}
    (f : X ⟶ G.obj Q) : F.map f ≫ (whiskerLeft G α).app Q = α.app X ≫ H.map f :=
  α.naturality f

/-- `map_comp_whiskerLeft_app` for a morphism into the image of a composite functor. -/
@[reassoc]
lemma map_comp_whiskerLeft_app_comp_obj {F H : C ⥤ D} (α : F ⟶ H) (P : A ⥤ B) (G : B ⥤ C)
    {X : C} {N : A} (f : X ⟶ (P ⋙ G).obj N) :
    F.map f ≫ (whiskerLeft G α).app (P.obj N) = α.app X ≫ H.map f :=
  α.naturality f

/-- Naturality of a natural transformation `α : F ⟶ H` at a morphism `f : R (Q N) ⟶ G (P N)`,
with both components written as whiskerings. -/
@[reassoc]
lemma map_comp_whiskerLeft_app_eq_whiskerLeft_app_comp_map {E₁ E₂ : Type*} [Category* E₁]
    [Category* E₂] {F H : C ⥤ D} (α : F ⟶ H) (Q : E₁ ⥤ E₂) (R : E₂ ⥤ C) (P : E₁ ⥤ B)
    (G : B ⥤ C) {N : E₁} (f : (Q ⋙ R).obj N ⟶ (P ⋙ G).obj N) :
    F.map f ≫ (whiskerLeft G α).app (P.obj N) = (whiskerLeft R α).app (Q.obj N) ≫ H.map f :=
  α.naturality f

/-- Cancellation of a whiskered natural isomorphism against its inverse. -/
lemma whiskerRight_hom_app_comp_map_whiskerLeft_inv_app {F H : C ⥤ D} (e : F ≅ H) (P : B ⥤ C)
    (G : D ⥤ A) {N : B} {Z : D} (R : F.obj (P.obj N) ⟶ Z) :
    (whiskerRight e.hom G).app (P.obj N) ≫ G.map ((whiskerLeft P e.inv).app N ≫ R) = G.map R := by
  rw [whiskerRight_app, whiskerLeft_app, ← G.map_comp, e.hom_inv_id_app_assoc]

end CategoryTheory.Functor

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- The components of the mate of a square along two adjunctions. -/
lemma mateEquiv_natTrans_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (d : B) : (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv_apply]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section FrobeniusAdjunction

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The adjunction `(e⁻¹)_* ⊣ e_*` of the equivalence `lowerStarEquivalenceOfIso e`, for an
isomorphism of schemes `e`. -/
noncomputable def lowerStarInvAdjunction : (e.inv)_*⟦Λ⟧ ⊣ (e.hom)_*⟦Λ⟧ :=
  (lowerStarEquivalenceOfIso Λ e).symm.toAdjunction

/-- The pullback along an isomorphism `e` is the pushforward along `e⁻¹`, through the
adjunction `lowerStarInvAdjunction`. -/
lemma upperStarIsoLowerStarInv_eq_leftAdjointUniq : upperStarIsoLowerStarInv Λ e =
    (upperStarLowerStarAdjunction Λ e.hom).leftAdjointUniq (lowerStarInvAdjunction Λ e) :=
  rfl

omit [IsCommMonObj Λ] in
/-- The counit isomorphism `(e⁻¹)_* ⋙ e_* ≅ 𝟭` of the equivalence `lowerStarEquivalenceOfIso e`. -/
lemma lowerStarEquivalenceOfIso_counitIso : (lowerStarEquivalenceOfIso Λ e).counitIso =
    lowerStarComp Λ e.inv e.hom ≪≫ lowerStarCongr Λ e.inv_hom_id ≪≫ lowerStarId Λ Y :=
  rfl

omit [IsCommMonObj Λ] in
/-- On underlying sheaves, the inverse of the identity isomorphism of the pushforward of module
objects is that of the pushforward of sheaves. -/
lemma lowerStarId_inv_app_hom_eq
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarId Λ X).inv.app M).hom = (ProEtale.lowerStarId Ab.{u + 1} X).inv.app M.X :=
  rfl

omit [IsCommMonObj Λ] in
/-- The triangle identity `e_* η ≫ ε e_* = 𝟙` for the unit and counit of
`lowerStarEquivalenceOfIso e` before adjointification, from that of the pushforwards of
sheaves (`AlgebraicGeometry.ProEtale.lowerStar_map_unit_comp_counit`). -/
lemma lowerStarEquivalenceOfIso_triangle
    (S : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (e.hom)_*⟦Λ⟧.map (((lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ e.hom_inv_id.symm ≪≫
      (lowerStarComp Λ e.hom e.inv).symm).hom.app S) ≫
      (lowerStarComp Λ e.inv e.hom ≪≫ lowerStarCongr Λ e.inv_hom_id ≪≫ lowerStarId Λ Y).hom.app
        ((e.hom)_*⟦Λ⟧.obj S) = 𝟙 _ := by
  apply Mod.Hom.ext
  have := ProEtale.lowerStar_map_unit_comp_counit Ab.{u + 1} e S.X
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp] at this ⊢
  simp only [Mod.comp_hom', lowerStar_map_hom, lowerStarComp_hom_app_hom,
    lowerStarComp_inv_app_hom, lowerStarCongr_hom_app_hom,
    lowerStarId_inv_app_hom_eq, Mod.id_hom']
  exact this

omit [IsCommMonObj Λ] in
/-- The unit isomorphism `𝟭 ≅ e_* ⋙ (e⁻¹)_*` of the equivalence `lowerStarEquivalenceOfIso e`:
its unit needs no adjointification, by the triangle identity
`lowerStarEquivalenceOfIso_triangle`. -/
lemma lowerStarEquivalenceOfIso_unitIso : (lowerStarEquivalenceOfIso Λ e).unitIso =
    (lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ e.hom_inv_id.symm ≪≫
      (lowerStarComp Λ e.hom e.inv).symm := by
  have h : (lowerStarEquivalenceOfIso Λ e).unitIso = Equivalence.adjointifyη
      ((lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ e.hom_inv_id.symm ≪≫
        (lowerStarComp Λ e.hom e.inv).symm)
      (lowerStarComp Λ e.inv e.hom ≪≫ lowerStarCongr Λ e.inv_hom_id ≪≫ lowerStarId Λ Y) :=
    rfl
  exact h.trans (Equivalence.adjointifyη_eq _ _ (lowerStarEquivalenceOfIso_triangle Λ e))

omit [IsCommMonObj Λ] in
lemma lowerStarEquivalenceOfIso_symm_unit_app_eq
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (lowerStarEquivalenceOfIso Λ e).symm.toAdjunction.unit.app N =
      (lowerStarEquivalenceOfIso Λ e).counitIso.inv.app N := by
  rw [Equivalence.toAdjunction_unit, Equivalence.symm_unit]

omit [IsCommMonObj Λ] in
lemma lowerStarEquivalenceOfIso_counitIso_inv_app
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (lowerStarEquivalenceOfIso Λ e).counitIso.inv.app N =
      (lowerStarComp Λ e.inv e.hom ≪≫ lowerStarCongr Λ e.inv_hom_id ≪≫
        lowerStarId Λ Y).inv.app N := by
  rw [lowerStarEquivalenceOfIso_counitIso]

omit [IsCommMonObj Λ] in
lemma lowerStarComp_trans_lowerStarCongr_trans_lowerStarId_inv_app
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (lowerStarComp Λ e.inv e.hom ≪≫ lowerStarCongr Λ e.inv_hom_id ≪≫
        lowerStarId Λ Y).inv.app N =
      (lowerStarId Λ Y).inv.app N ≫ (lowerStarCongr Λ e.inv_hom_id).inv.app N ≫
        (lowerStarComp Λ e.inv e.hom).inv.app N := by
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app, Category.assoc]

omit [IsCommMonObj Λ] in
/-- The unit of the adjunction `(e⁻¹)_* ⊣ e_*`. -/
lemma lowerStarInvAdjunction_unit_app
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (lowerStarInvAdjunction Λ e).unit.app N =
      (lowerStarId Λ Y).inv.app N ≫ (lowerStarCongr Λ e.inv_hom_id).inv.app N ≫
        (lowerStarComp Λ e.inv e.hom).inv.app N :=
  (lowerStarEquivalenceOfIso_symm_unit_app_eq Λ e N).trans
    ((lowerStarEquivalenceOfIso_counitIso_inv_app Λ e N).trans
      (lowerStarComp_trans_lowerStarCongr_trans_lowerStarId_inv_app Λ e N))

omit [IsCommMonObj Λ] in
lemma lowerStarEquivalenceOfIso_symm_counit_app_eq
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarEquivalenceOfIso Λ e).symm.toAdjunction.counit.app M =
      (lowerStarEquivalenceOfIso Λ e).unitIso.inv.app M := by
  rw [Equivalence.toAdjunction_counit, Equivalence.symm_counit]

omit [IsCommMonObj Λ] in
lemma lowerStarEquivalenceOfIso_unitIso_inv_app
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarEquivalenceOfIso Λ e).unitIso.inv.app M =
      ((lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ e.hom_inv_id.symm ≪≫
        (lowerStarComp Λ e.hom e.inv).symm).inv.app M := by
  rw [lowerStarEquivalenceOfIso_unitIso]

omit [IsCommMonObj Λ] in
lemma lowerStarId_symm_trans_lowerStarCongr_trans_lowerStarComp_symm_inv_app
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ e.hom_inv_id.symm ≪≫
        (lowerStarComp Λ e.hom e.inv).symm).inv.app M =
      (lowerStarComp Λ e.hom e.inv).hom.app M ≫
        (lowerStarCongr Λ e.hom_inv_id.symm).inv.app M ≫ (lowerStarId Λ X).hom.app M := by
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app, Category.assoc,
    Iso.symm_inv, Iso.symm_inv]

omit [IsCommMonObj Λ] in
/-- The counit of the adjunction `(e⁻¹)_* ⊣ e_*`. -/
lemma lowerStarInvAdjunction_counit_app
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarInvAdjunction Λ e).counit.app M =
      (lowerStarComp Λ e.hom e.inv).hom.app M ≫
        (lowerStarCongr Λ e.hom_inv_id.symm).inv.app M ≫ (lowerStarId Λ X).hom.app M :=
  (lowerStarEquivalenceOfIso_symm_counit_app_eq Λ e M).trans
    ((lowerStarEquivalenceOfIso_unitIso_inv_app Λ e M).trans
      (lowerStarId_symm_trans_lowerStarCongr_trans_lowerStarComp_symm_inv_app Λ e M))

end FrobeniusAdjunction

omit [IsCommMonObj Λ] in
/-- The components of the exchange isomorphism `a_* ⋙ b_* ≅ (a ≫ b)_* = (c ≫ d)_* ≅ c_* ⋙ d_*`. -/
lemma lowerStarComp_trans_lowerStarCongr_trans_symm_hom_app {X Y Z Z' : Scheme.{u}} {a : X ⟶ Z}
    {b : Z ⟶ Y} {c : X ⟶ Z'} {d : Z' ⟶ Y} (e : a ≫ b = c ≫ d)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarComp Λ a b ≪≫ lowerStarCongr Λ e ≪≫ (lowerStarComp Λ c d).symm).hom.app P =
      (lowerStarComp Λ a b).hom.app P ≫ (lowerStarCongr Λ e).hom.app P ≫
        (lowerStarComp Λ c d).inv.app P := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.comp_app]


omit [IsCommMonObj Λ] in
/-- `lowerStarComp_frobeniusMate_app` for automorphisms `F_X`, `F_Y` intertwined by `φ`. -/
lemma lowerStarFrobeniusMate_app_eq {X Y : Scheme.{u}}
    (FX : X ≅ X) (FY : Y ≅ Y) (φ : X ⟶ Y) (hφ : φ ≫ FY.inv = FX.inv ≫ φ)
    (hφ' : FX.hom ≫ φ = φ ≫ FY.hom)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarId Λ Y).inv.app ((φ)_*⟦Λ⟧.obj ((FX.hom)_*⟦Λ⟧.obj M)) ≫
        (lowerStarCongr Λ FY.inv_hom_id).inv.app _ ≫ (lowerStarComp Λ FY.inv FY.hom).inv.app _ ≫
        (FY.hom)_*⟦Λ⟧.map ((lowerStarComp Λ φ FY.inv).hom.app ((FX.hom)_*⟦Λ⟧.obj M) ≫
          (lowerStarCongr Λ hφ).hom.app _ ≫ (lowerStarComp Λ FX.inv φ).inv.app _) ≫
        (FY.hom)_*⟦Λ⟧.map ((φ)_*⟦Λ⟧.map ((lowerStarComp Λ FX.hom FX.inv).hom.app M ≫
          (lowerStarCongr Λ FX.hom_inv_id.symm).inv.app M ≫ (lowerStarId Λ X).hom.app M)) =
      (lowerStarComp Λ FX.hom φ).hom.app M ≫ (lowerStarCongr Λ hφ').hom.app M ≫
        (lowerStarComp Λ φ FY.hom).inv.app ((𝟭 _).obj M) :=
  lowerStarComp_frobeniusMate_app Λ FX.hom FX.inv FY.hom FY.inv φ FX.hom_inv_id.symm
    FY.inv_hom_id hφ hφ' M

omit [IsCommMonObj Λ] in
/-- The unit and counit of the adjunctions `(F⁻¹)_* ⊣ F_*`, written through the composition and
identity isomorphisms of the pushforwards. -/
lemma lowerStarInvAdjunction_unit_comp_map_counit_app {X Y : Scheme.{u}}
    (FX : X ≅ X) (FY : Y ≅ Y) (φ : X ⟶ Y) (hφ : φ ≫ FY.inv = FX.inv ≫ φ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarInvAdjunction Λ FY).unit.app ((φ)_*⟦Λ⟧.obj ((FX.hom)_*⟦Λ⟧.obj M)) ≫
        (FY.hom)_*⟦Λ⟧.map ((lowerStarComp Λ φ FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫
          (lowerStarComp Λ FX.inv φ).symm).hom.app ((FX.hom)_*⟦Λ⟧.obj M)) ≫
        (FY.hom)_*⟦Λ⟧.map ((φ)_*⟦Λ⟧.map ((lowerStarInvAdjunction Λ FX).counit.app M)) =
    (lowerStarId Λ Y).inv.app ((φ)_*⟦Λ⟧.obj ((FX.hom)_*⟦Λ⟧.obj M)) ≫
        (lowerStarCongr Λ FY.inv_hom_id).inv.app _ ≫ (lowerStarComp Λ FY.inv FY.hom).inv.app _ ≫
        (FY.hom)_*⟦Λ⟧.map ((lowerStarComp Λ φ FY.inv).hom.app ((FX.hom)_*⟦Λ⟧.obj M) ≫
          (lowerStarCongr Λ hφ).hom.app _ ≫ (lowerStarComp Λ FX.inv φ).inv.app _) ≫
        (FY.hom)_*⟦Λ⟧.map ((φ)_*⟦Λ⟧.map ((lowerStarComp Λ FX.hom FX.inv).hom.app M ≫
          (lowerStarCongr Λ FX.hom_inv_id.symm).inv.app M ≫ (lowerStarId Λ X).hom.app M)) := by
  rw [lowerStarInvAdjunction_unit_app, lowerStarInvAdjunction_counit_app,
    lowerStarComp_trans_lowerStarCongr_trans_symm_hom_app, Category.assoc, Category.assoc]

omit [IsCommMonObj Λ] in
/-- The mate of the Frobenius exchange of `φ_*` along the adjunctions `(F⁻¹)_* ⊣ F_*` is the
exchange `F_{X*} φ_* ≅ φ_* F_{Y*}` built from the composition isomorphisms. -/
lemma lowerStarInvAdjunction_unit_comp_map_exchange_comp_counit_app {X Y : Scheme.{u}}
    (FX : X ≅ X) (FY : Y ≅ Y) (φ : X ⟶ Y) (hφ : φ ≫ FY.inv = FX.inv ≫ φ)
    (hφ' : FX.hom ≫ φ = φ ≫ FY.hom)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStarInvAdjunction Λ FY).unit.app ((φ)_*⟦Λ⟧.obj ((FX.hom)_*⟦Λ⟧.obj M)) ≫
        (FY.hom)_*⟦Λ⟧.map ((lowerStarComp Λ φ FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫
          (lowerStarComp Λ FX.inv φ).symm).hom.app ((FX.hom)_*⟦Λ⟧.obj M)) ≫
        (FY.hom)_*⟦Λ⟧.map ((φ)_*⟦Λ⟧.map ((lowerStarInvAdjunction Λ FX).counit.app M)) =
      (lowerStarComp Λ FX.hom φ).hom.app M ≫ (lowerStarCongr Λ hφ').hom.app M ≫
        (lowerStarComp Λ φ FY.hom).inv.app ((𝟭 _).obj M) :=
  (lowerStarInvAdjunction_unit_comp_map_counit_app Λ FX FY φ hφ M).trans
    (lowerStarFrobeniusMate_app_eq Λ FX FY φ hφ hφ' M)

omit [IsCommMonObj Λ] in
lemma mateEquiv_lowerStarFrobeniusExchange {X Y : Scheme.{u}} (FX : X ≅ X) (FY : Y ≅ Y)
    (φ : X ⟶ Y) (hφ : φ ≫ FY.inv = FX.inv ≫ φ) (hφ' : FX.hom ≫ φ = φ ≫ FY.hom) :
    (mateEquiv (lowerStarInvAdjunction Λ FX) (lowerStarInvAdjunction Λ FY)
      (TwoSquare.mk _ _ _ _ (lowerStarComp Λ φ FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫
        (lowerStarComp Λ FX.inv φ).symm).hom)) =
      (lowerStarComp Λ FX.hom φ).hom ≫ (lowerStarCongr Λ hφ').hom ≫
        (lowerStarComp Λ φ FY.hom).inv :=
  NatTrans.ext (funext fun M ↦ (mateEquiv_natTrans_app _ _ _ M).trans
    (lowerStarInvAdjunction_unit_comp_map_exchange_comp_counit_app Λ FX FY φ hφ hφ' M))
set_option hygiene false in
/-- The exchange isomorphism `φ^* ⋙ (F_X⁻¹)_* ≅ (F_Y⁻¹)_* ⋙ φ^*` of the pullbacks along a
commutative square `F_X ≫ φ = φ ≫ F_Y` of automorphisms. -/
local notation "upperStarFrobeniusExchange[" FX ", " FY ", " φ ", " h "]" =>
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv Λ FX).symm ≪≫
    (upperStarComp Λ FX.hom φ).symm ≪≫ upperStarCongr Λ h ≪≫ upperStarComp Λ φ FY.hom ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv Λ FY) _

section FrobeniusExchange

variable {X Y : Scheme.{u}} (FX : X ≅ X) (FY : Y ≅ Y) (φ : X ⟶ Y)

/-- The pullback along an isomorphism is conjugate to the identity of the pushforward. -/
lemma conjugateIsoEquiv_upperStarIsoLowerStarInv {X' : Scheme.{u}} (e : X ≅ X') :
    conjugateIsoEquiv (lowerStarInvAdjunction Λ e) (upperStarLowerStarAdjunction Λ e.hom)
      (upperStarIsoLowerStarInv Λ e) = Iso.refl _ := by
  ext : 1
  rw [conjugateIsoEquiv_apply_hom, upperStarIsoLowerStarInv_eq_leftAdjointUniq,
    conjugateEquiv_leftAdjointUniq_hom]
  rfl

/-- The conjugate of `upperStarFrobeniusExchange` is the exchange isomorphism
`φ_* ⋙ F_Y* ≅ (φ ≫ F_Y)_* = (F_X ≫ φ)_* ≅ F_X* ⋙ φ_*` of the pushforwards. -/
lemma conjugateIsoEquiv_upperStarFrobeniusExchange (hφ' : FX.hom ≫ φ = φ ≫ FY.hom) :
    conjugateIsoEquiv ((lowerStarInvAdjunction Λ FY).comp (upperStarLowerStarAdjunction Λ φ))
      ((upperStarLowerStarAdjunction Λ φ).comp (lowerStarInvAdjunction Λ FX))
      (upperStarFrobeniusExchange[FX, FY, φ, hφ']) =
    (((Functor.isoWhiskerLeft (φ)_*⟦Λ⟧ (Iso.refl _) ≪≫ lowerStarComp Λ φ FY.hom) ≪≫
      (lowerStarCongr Λ hφ').symm) ≪≫ (lowerStarComp Λ FX.hom φ).symm) ≪≫
      Functor.isoWhiskerRight (Iso.refl _).symm (φ)_*⟦Λ⟧ := by
  rw [
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction Λ φ).comp
      (upperStarLowerStarAdjunction Λ FX.hom)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ (FX.hom ≫ φ)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ (φ ≫ FY.hom)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction Λ FY.hom).comp
      (upperStarLowerStarAdjunction Λ φ)) _,
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_upperStarIsoLowerStarInv,
    conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarComp,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_upperStarIsoLowerStarInv]

/-- The conjugate of the inverse of `upperStarFrobeniusExchange`. -/
lemma conjugateEquiv_upperStarFrobeniusExchange_inv (hφ' : FX.hom ≫ φ = φ ≫ FY.hom) :
    conjugateEquiv ((upperStarLowerStarAdjunction Λ φ).comp (lowerStarInvAdjunction Λ FX))
      ((lowerStarInvAdjunction Λ FY).comp (upperStarLowerStarAdjunction Λ φ))
      (upperStarFrobeniusExchange[FX, FY, φ, hφ']).inv =
    (lowerStarComp Λ FX.hom φ).hom ≫ (lowerStarCongr Λ hφ').hom ≫
      (lowerStarComp Λ φ FY.hom).inv := by
  rw [← Iso.symm_hom (upperStarFrobeniusExchange[FX, FY, φ, hφ']),
    ← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_iso_symm, Iso.symm_hom,
    conjugateIsoEquiv_upperStarFrobeniusExchange]
  rw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Iso.refl_hom, Functor.whiskerRight_id', Iso.symm_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Iso.refl_inv, Functor.whiskerLeft_id', Category.comp_id,
    Category.id_comp]

/-- **The Frobenius structure of the pullback along the base change `φ̄` is the pullback form of
the exchange isomorphism**: the mate `CategoryTheory.Endofunctor.IsoAlgebra.leftMateIso` of the
exchange isomorphism `φ_* ⋙ (F_Y⁻¹)_* ≅ (F_X⁻¹)_* ⋙ φ_*` of the pushforwards is
`upperStarFrobeniusExchange`. -/
theorem leftMateIso_lowerStarFrobeniusExchange (hφ : φ ≫ FY.inv = FX.inv ≫ φ)
    (hφ' : FX.hom ≫ φ = φ ≫ FY.hom) :
    Endofunctor.IsoAlgebra.leftMateIso (upperStarLowerStarAdjunction Λ φ)
      (lowerStarComp Λ φ FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫ (lowerStarComp Λ FX.inv φ).symm) =
    (upperStarFrobeniusExchange[FX, FY, φ, hφ']) := by
  have key : mateEquiv (upperStarLowerStarAdjunction Λ φ) (upperStarLowerStarAdjunction Λ φ)
      (TwoSquare.mk _ _ _ _ (upperStarFrobeniusExchange[FX, FY, φ, hφ']).inv) =
      TwoSquare.mk _ _ _ _ (lowerStarComp Λ φ FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫
        (lowerStarComp Λ FX.inv φ).symm).hom :=
    (mateEquiv (lowerStarInvAdjunction Λ FX) (lowerStarInvAdjunction Λ FY)).injective
      ((iterated_mateEquiv_conjugateEquiv _ _ _ _ _).trans
        ((conjugateEquiv_upperStarFrobeniusExchange_inv Λ FX FY φ hφ').trans
          (mateEquiv_lowerStarFrobeniusExchange Λ FX FY φ hφ hφ').symm))
  refine Iso.ext ((Iso.inv_eq_inv (Endofunctor.IsoAlgebra.leftMateIso
    (upperStarLowerStarAdjunction Λ φ)
    (lowerStarComp Λ φ FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫ (lowerStarComp Λ FX.inv φ).symm))
    (upperStarFrobeniusExchange[FX, FY, φ, hφ'])).1 ?_)
  rw [Endofunctor.IsoAlgebra.leftMateIso, Iso.symm_inv, asIso_hom, ← key, Equiv.symm_apply_apply]

end FrobeniusExchange

section UpperStarCoherence

variable {X₀ Y₀ X Y S T U V : Scheme.{u}}

/-- Transports of the pullback along two proofs of the same equality agree. -/
lemma upperStarCongr_hom_app_proof_irrel' {a b : S ⟶ T} (e e' : a = b)
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStarCongr Λ e).hom.app N = (upperStarCongr Λ e').hom.app N := by
  obtain rfl : e = e' := rfl
  rfl

/-- The inverse of the composition isomorphism `(a ≫ t)^* ≅ t^* ⋙ a^*` is compatible with the
transport along an equality `a = b`. -/
@[reassoc]
lemma upperStarCongr_hom_app_comp_upperStarComp_inv_app {a b : S ⟶ T} (e : a = b) (t : T ⟶ U)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarCongr Λ e).hom.app ((t)^*⟦Λ⟧.obj N) ≫ (upperStarComp Λ b t).inv.app N =
      (upperStarComp Λ a t).inv.app N ≫ (upperStarCongr Λ (congrArg (· ≫ t) e)).hom.app N := by
  subst e
  simp [upperStarCongr_self]

/-- The inverse of the composition isomorphism `(t ≫ a)^* ≅ a^* ⋙ t^*` is compatible with the
transport along an equality `a = b`. -/
@[reassoc]
lemma map_upperStarCongr_hom_app_comp_upperStarComp_inv_app (t : S ⟶ T) {a b : T ⟶ U}
    (e : a = b) (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (t)^*⟦Λ⟧.map ((upperStarCongr Λ e).hom.app N) ≫ (upperStarComp Λ t b).inv.app N =
      (upperStarComp Λ t a).inv.app N ≫ (upperStarCongr Λ (congrArg (t ≫ ·) e)).hom.app N := by
  subst e
  simp [upperStarCongr_self]

/-- The associativity law of the composition isomorphisms of the pullbacks, for the inverse
isomorphisms. -/
@[reassoc]
lemma upperStarComp_inv_app_comp_upperStarComp_inv_app (a : S ⟶ T) (b : T ⟶ U) (c : U ⟶ V)
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (upperStarComp Λ a b).inv.app ((c)^*⟦Λ⟧.obj M) ≫ (upperStarComp Λ (a ≫ b) c).inv.app M =
      (a)^*⟦Λ⟧.map ((upperStarComp Λ b c).inv.app M) ≫ (upperStarComp Λ a (b ≫ c)).inv.app M ≫
        (upperStarCongr Λ (Category.assoc a b c).symm).hom.app M := by
  have := congrArg Iso.inv
    (Iso.ext (upperStarComp_hom_app_comp_map_upperStarComp_hom_app Λ a b c M) :
    (upperStarComp Λ a (b ≫ c)).app M ≪≫ (a)^*⟦Λ⟧.mapIso ((upperStarComp Λ b c).app M) =
      (upperStarCongr Λ (Category.assoc a b c).symm).app M ≪≫
        (upperStarComp Λ (a ≫ b) c).app M ≪≫ (upperStarComp Λ a b).app ((c)^*⟦Λ⟧.obj M))
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at this
  rw [reassoc_of% this, Iso.inv_hom_id_app, Category.comp_id]

/-- The associativity law of the composition isomorphisms of the pullbacks, solved for
`a^* (b, c) ≫ (a, b)⁻¹`. -/
@[reassoc]
lemma upperStar_map_upperStarComp_hom_app_comp_upperStarComp_inv_app (a : S ⟶ T) (b : T ⟶ U)
    (c : U ⟶ V) (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (a)^*⟦Λ⟧.map ((upperStarComp Λ b c).hom.app M) ≫
        (upperStarComp Λ a b).inv.app ((c)^*⟦Λ⟧.obj M) =
      (upperStarComp Λ a (b ≫ c)).inv.app M ≫
        (upperStarCongr Λ (Category.assoc a b c).symm).hom.app M ≫
          (upperStarComp Λ (a ≫ b) c).hom.app M := by
  refine (Iso.eq_inv_comp ((upperStarComp Λ a (b ≫ c)).app M)).2 ?_
  rw [Iso.app_hom, upperStarComp_hom_app_comp_map_upperStarComp_hom_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- **Frobenius compatibility of the pullback comparison, pullback form.** Let
`pX ≫ φ = φ' ≫ pY` be a commutative square, and `fX`, `fY` endomorphisms of `X`, `Y` with
`fX ≫ pX = pX`, `fY ≫ pY = pY` and `fX ≫ φ' = φ' ≫ fY`. Then the comparison
`C : φ^* pX^* ≅ pY^* φ'^*` of the square intertwines the invariance isomorphisms
`fX^* pX^* ≅ pX^*` and `fY^* pY^* ≅ pY^*` through the exchange isomorphism
`fX^* φ'^* ≅ (fX ≫ φ')^* = (φ' ≫ fY)^* ≅ φ'^* fY^*`. -/
lemma upperStarSquareComparison_frobenius (pX : X ⟶ X₀) (pY : Y ⟶ Y₀) (φ : X₀ ⟶ Y₀)
    (φ' : X ⟶ Y) (fX : X ⟶ X) (fY : Y ⟶ Y) (hpX : fX ≫ pX = pX) (hpY : fY ≫ pY = pY)
    (hsq : pX ≫ φ = φ' ≫ pY) (hφ' : fX ≫ φ' = φ' ≫ fY)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y₀) Ab.{u + 1}) (condensedRingObj Λ Y₀)) :
    (fX)^*⟦Λ⟧.map ((upperStarComp Λ pX φ).inv.app N ≫ (upperStarCongr Λ hsq).hom.app N ≫
        (upperStarComp Λ φ' pY).hom.app N) ≫
      (upperStarComp Λ fX φ').inv.app ((pY)^*⟦Λ⟧.obj N) ≫
      (upperStarCongr Λ hφ').hom.app ((pY)^*⟦Λ⟧.obj N) ≫
      (upperStarComp Λ φ' fY).hom.app ((pY)^*⟦Λ⟧.obj N) ≫
      (φ')^*⟦Λ⟧.map ((upperStarComp Λ fY pY).inv.app N ≫ (upperStarCongr Λ hpY).hom.app N) =
    (upperStarComp Λ fX pX).inv.app ((φ)^*⟦Λ⟧.obj N) ≫
      (upperStarCongr Λ hpX).hom.app ((φ)^*⟦Λ⟧.obj N) ≫
      ((upperStarComp Λ pX φ).inv.app N ≫ (upperStarCongr Λ hsq).hom.app N ≫
        (upperStarComp Λ φ' pY).hom.app N) := by
  rewrite [Functor.map_comp_assoc, Functor.map_comp_assoc,
    upperStar_map_upperStarComp_hom_app_comp_upperStarComp_inv_app_assoc,
    map_upperStarCongr_hom_app_comp_upperStarComp_inv_app_assoc,
    upperStarComp_hom_app_upperStarCongr_hom_app_assoc,
    upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc, upperStarComp_hom_app_map_upperStarCongr_hom_app,
    upperStarCongr_hom_app_trans_assoc, upperStarCongr_hom_app_trans_assoc,
    upperStarCongr_hom_app_trans_assoc, upperStarCongr_hom_app_trans_assoc,
    upperStarCongr_hom_app_comp_upperStarComp_inv_app_assoc,
    upperStarComp_inv_app_comp_upperStarComp_inv_app_assoc,
    upperStarCongr_hom_app_trans_assoc, upperStarCongr_hom_app_trans_assoc]
  exact congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) rfl
    (congrArg₂ (· ≫ ·) (upperStarCongr_hom_app_proof_irrel' Λ _ _ N) rfl))

end UpperStarCoherence

section WeilCompatible

variable {X₀ Y₀ X Y : Scheme.{u}}

/-- The inverse of the transport of the pullback along `a = b` is the transport along `b = a`. -/
lemma upperStarCongr_inv_app_eq {S T : Scheme.{u}} {a b : S ⟶ T} (e : a = b) (e' : b = a)
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStarCongr Λ e).inv.app N = (upperStarCongr Λ e').hom.app N := by
  subst e
  rfl

/-- The components of the inverse of the comparison of the pullbacks along a commutative
square. -/
lemma upperStarSquareComparison_inv_app {f : X₀ ⟶ Y₀} {g : Y ⟶ Y₀} {f' : X ⟶ Y} {g' : X ⟶ X₀}
    (sq : CommSq g' f' f g)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y₀) Ab.{u + 1}) (condensedRingObj Λ Y₀)) :
    (upperStarSquareComparison Λ sq).inv.app N =
      (upperStarComp Λ g' f).inv.app N ≫ (upperStarCongr Λ sq.w).hom.app N ≫
        (upperStarComp Λ f' g).hom.app N := by
  rw [upperStarSquareComparison_eq, Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app,
    NatTrans.comp_app, Iso.symm_inv, upperStarCongr_inv_app_eq Λ sq.w.symm sq.w, Category.assoc]

/-- The components of `upperStarFrobeniusExchange`. -/
lemma upperStarFrobeniusExchange_hom_app (FX : X ≅ X) (FY : Y ≅ Y) (φ : X ⟶ Y)
    (hφ' : FX.hom ≫ φ = φ ≫ FY.hom)
    (Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarFrobeniusExchange[FX, FY, φ, hφ']).hom.app Q =
      (Functor.whiskerLeft (φ)^*⟦Λ⟧ (upperStarIsoLowerStarInv Λ FX).inv).app Q ≫
        (upperStarComp Λ FX.hom φ).inv.app Q ≫ (upperStarCongr Λ hφ').hom.app Q ≫
        (upperStarComp Λ φ FY.hom).hom.app Q ≫
        (Functor.whiskerRight (upperStarIsoLowerStarInv Λ FY).hom (φ)^*⟦Λ⟧).app Q := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]

/-- The components of the invariance isomorphism `(F⁻¹)_* p^* ≅ F^* p^* ≅ (F ≫ p)^* = p^*`. -/
lemma upperStarInvariance_hom_app {S : Scheme.{u}} (p : X ⟶ S) (F : X ≅ X) (hp : F.hom ≫ p = p)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (Functor.isoWhiskerLeft (p)^*⟦Λ⟧ (upperStarIsoLowerStarInv Λ F).symm ≪≫
        (upperStarComp Λ F.hom p).symm ≪≫ upperStarCongr Λ hp).hom.app N =
      (Functor.whiskerLeft (p)^*⟦Λ⟧ (upperStarIsoLowerStarInv Λ F).inv).app N ≫
        (upperStarComp Λ F.hom p).inv.app N ≫ (upperStarCongr Λ hp).hom.app N := by
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Iso.symm_hom]

/-- **Frobenius compatibility of the pullback comparison, abstract form.** Let
`pX ≫ φ = φ' ≫ pY` be a commutative square of schemes and `F_X`, `F_Y` automorphisms of `X`,
`Y` with `F_X ≫ pX = pX`, `F_Y ≫ pY = pY` and `φ' ≫ F_Y⁻¹ = F_X⁻¹ ≫ φ'`. Then the comparison
`C : φ^* pX^* ≅ pY^* φ'^*` intertwines the invariance isomorphism `(F_X⁻¹)_* pX^* ≅ pX^*` with
the transport, along the mate of the exchange isomorphism `φ'_* (F_Y⁻¹)_* ≅ (F_X⁻¹)_* φ'_*`,
of the invariance isomorphism `(F_Y⁻¹)_* pY^* ≅ pY^*`. -/
theorem upperStarSquareComparison_inv_app_frobenius (pX : X ⟶ X₀) (pY : Y ⟶ Y₀) (φ : X₀ ⟶ Y₀)
    (φ' : X ⟶ Y) (FX : X ≅ X) (FY : Y ≅ Y) (hpX : FX.hom ≫ pX = pX) (hpY : FY.hom ≫ pY = pY)
    (sq : CommSq pX φ' φ pY) (hφ : φ' ≫ FY.inv = FX.inv ≫ φ')
    (hφ' : FX.hom ≫ φ' = φ' ≫ FY.hom)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y₀) Ab.{u + 1}) (condensedRingObj Λ Y₀)) :
    (FX.inv)_*⟦Λ⟧.map ((upperStarSquareComparison Λ sq).inv.app N) ≫
        ((Endofunctor.IsoAlgebra.leftMateIso (upperStarLowerStarAdjunction Λ φ')
          (lowerStarComp Λ φ' FY.inv ≪≫ lowerStarCongr Λ hφ ≪≫
            (lowerStarComp Λ FX.inv φ').symm)).hom.app ((pY)^*⟦Λ⟧.obj N) ≫
        (φ')^*⟦Λ⟧.map ((Functor.isoWhiskerLeft (pY)^*⟦Λ⟧ (upperStarIsoLowerStarInv Λ FY).symm ≪≫
          (upperStarComp Λ FY.hom pY).symm ≪≫ upperStarCongr Λ hpY).hom.app N)) =
      (Functor.isoWhiskerLeft (pX)^*⟦Λ⟧ (upperStarIsoLowerStarInv Λ FX).symm ≪≫
          (upperStarComp Λ FX.hom pX).symm ≪≫ upperStarCongr Λ hpX).hom.app ((φ)^*⟦Λ⟧.obj N) ≫
        (upperStarSquareComparison Λ sq).inv.app N := by
  rw [leftMateIso_lowerStarFrobeniusExchange Λ FX FY φ' hφ hφ', upperStarFrobeniusExchange_hom_app,
    upperStarInvariance_hom_app, upperStarInvariance_hom_app]
  simp only [Category.assoc]
  rw [CategoryTheory.Functor.map_comp_whiskerLeft_app_eq_whiskerLeft_app_comp_map_assoc,
    CategoryTheory.Functor.whiskerRight_hom_app_comp_map_whiskerLeft_inv_app,
    upperStarSquareComparison_inv_app,
    upperStarSquareComparison_frobenius Λ pX pY φ φ' FX.hom FY.hom hpX hpY sq.w hφ' N]

end WeilCompatible

end AlgebraicGeometry.ProEtale.CondensedRing
