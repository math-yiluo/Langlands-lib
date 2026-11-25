/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Coherence of the pushforwards and pullbacks of module objects over `Λ`

The composition isomorphisms `f_* ⋙ g_* ≅ (f ≫ g)_*`
(`ProEtale.CondensedRing.lowerStarComp`) and `(f ≫ g)^* ≅ g^* ⋙ f^*`
(`ProEtale.CondensedRing.upperStarComp`) of the pushforwards and pullbacks of module objects over
a commutative condensed ring `Λ` satisfy, together with the identity isomorphisms
`(𝟙 X)_* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭` (`ProEtale.CondensedRing.lowerStarId`,
`ProEtale.CondensedRing.upperStarId`), the associativity and unit laws.

On underlying sheaves, the composition and identity isomorphisms of the pushforwards are those of
the pushforwards of sheaves (`ProEtale.lowerStarComp`, `ProEtale.lowerStarId`), so that their
laws are those of `ProEtale.legacy_lowerStarComp_assoc`, `ProEtale.lowerStarComp_id_right` and
`ProEtale.legacy_lowerStarComp_id_left`. The isomorphisms of the pullbacks are conjugate to those
of the pushforwards, and their laws follow by conjugation.

## Main definitions

- `ProEtale.CondensedRing.lowerStarCongr`, `ProEtale.CondensedRing.upperStarCongr`: transport
  along an equality of morphisms.

## Main statements

- `ProEtale.CondensedRing.lowerStarComp_assoc`, `ProEtale.CondensedRing.lowerStarComp_id_left`,
  `ProEtale.CondensedRing.lowerStarComp_id_right`: the laws of the pushforwards.
- `ProEtale.CondensedRing.upperStarComp_assoc`, `ProEtale.CondensedRing.upperStarComp_id_left`,
  `ProEtale.CondensedRing.upperStarComp_id_right`: the laws of the pullbacks.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-! ### The pushforwards -/

section LowerStar

variable (X : Scheme.{u})

/-- On underlying sheaves, the identity isomorphism of the pushforward of module objects is that
of the pushforward of sheaves. -/
@[simp]
lemma lowerStarId_hom_app_hom [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarId Λ X).hom.app M).hom = (ProEtale.lowerStarId Ab.{u + 1} X).hom.app M.X :=
  rfl

variable {X} {Y Z V : Scheme.{u}}

/-- Transport of the pushforward of module objects along an equality of morphisms. -/
noncomputable def lowerStarCongr {f g : X ⟶ Y} (h : f = g) : (f)_*⟦Λ⟧ ≅ (g)_*⟦Λ⟧ :=
  eqToIso (by rw [h])

@[simp]
lemma lowerStarCongr_hom_app_hom {f g : X ⟶ Y} (h : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarCongr Λ h).hom.app M).hom =
      (ProEtale.lowerStarCongr Ab.{u + 1} h).hom.app M.X := by
  subst h
  rfl

/-- The inverse of the transport along `f = g` is the transport along `g = f`. -/
lemma lowerStarCongr_symm {f g : X ⟶ Y} (h : f = g) :
    (lowerStarCongr Λ h).symm = lowerStarCongr Λ h.symm := by
  subst h
  rfl

@[simp]
lemma lowerStar_map_hom {f : X ⟶ Y}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (φ : M ⟶ N) : ((f)_*⟦Λ⟧.map φ).hom = (f)_*[Ab.{u + 1}].map φ.hom :=
  rfl

/-- On underlying sheaves, the composition isomorphism of the pushforwards of module objects is
that of the pushforwards of sheaves. -/
@[simp]
lemma lowerStarComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarComp Λ f g).hom.app M).hom =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app M.X := by
  simp [lowerStarComp, comapCondensedPushforwardHomComp]
  rfl

/-- The associativity law for the composition isomorphisms of the pushforwards of module
objects. -/
lemma lowerStarComp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    (f)_*⟦Λ⟧.associator (g)_*⟦Λ⟧ (h)_*⟦Λ⟧ ≪≫
        Functor.isoWhiskerLeft (f)_*⟦Λ⟧ (lowerStarComp Λ g h) ≪≫ lowerStarComp Λ f (g ≫ h) =
      Functor.isoWhiskerRight (lowerStarComp Λ f g) (h)_*⟦Λ⟧ ≪≫ lowerStarComp Λ (f ≫ g) h ≪≫
        lowerStarCongr Λ (Category.assoc f g h) := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_))
  have := congrArg (fun e ↦ e.hom.app M.X) (ProEtale.legacy_lowerStarComp_assoc Ab.{u + 1} f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Mod.comp_hom', Functor.associator_hom_app,
    Mod.id_hom', Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, lowerStarComp_hom_app_hom, lowerStar_map_hom,
    lowerStarCongr_hom_app_hom] at this ⊢
  exact this

/-- The left unit law for the composition isomorphisms of the pushforwards of module objects. -/
lemma lowerStarComp_id_left (t : X ⟶ Y) :
    lowerStarComp Λ (𝟙 X) t = Functor.isoWhiskerRight (lowerStarId Λ X) (t)_*⟦Λ⟧ ≪≫
      (t)_*⟦Λ⟧.leftUnitor ≪≫ (lowerStarCongr Λ (Category.id_comp t)).symm := by
  rw [lowerStarCongr_symm]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_))
  have := congrArg (fun e ↦ e.hom.app M.X) (ProEtale.legacy_lowerStarComp_id_left Ab.{u + 1} t)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, lowerStarComp_hom_app_hom,
    lowerStar_map_hom, lowerStarCongr_hom_app_hom,
    Functor.leftUnitor_hom_app, Mod.id_hom'] at this ⊢
  exact this

/-- The right unit law for the composition isomorphisms of the pushforwards of module objects. -/
lemma lowerStarComp_id_right (t : X ⟶ Y) :
    lowerStarComp Λ t (𝟙 Y) = Functor.isoWhiskerLeft (t)_*⟦Λ⟧ (lowerStarId Λ Y) ≪≫
      (t)_*⟦Λ⟧.rightUnitor ≪≫ (lowerStarCongr Λ (Category.comp_id t)).symm := by
  rw [lowerStarCongr_symm]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_))
  have := congrArg (fun e ↦ e.hom.app M.X) (ProEtale.lowerStarComp_id_right Ab.{u + 1} t)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, lowerStarComp_hom_app_hom,
    lowerStarCongr_hom_app_hom, Functor.rightUnitor_hom_app,
    Mod.id_hom'] at this ⊢
  exact this

end LowerStar

/-! ### The pullbacks -/

section UpperStar

variable [IsCommMonObj Λ] (X : Scheme.{u})

/-- The identity isomorphism of the pullback is conjugate to the inverse of that of the
pushforward. -/
lemma conjugateIsoEquiv_upperStarId :
    conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction Λ (𝟙 X)) (upperStarId Λ X) =
      (lowerStarId Λ X).symm :=
  Iso.ext (Equiv.apply_symm_apply _ _)

variable {X} {Y Z V : Scheme.{u}}

/-- Transport of the pullback of module objects along an equality of morphisms. -/
noncomputable def upperStarCongr {f g : X ⟶ Y} (h : f = g) : (f)^*⟦Λ⟧ ≅ (g)^*⟦Λ⟧ :=
  eqToIso (by rw [h])

/-- The transport of the pullback along an equation `f = f` is the identity. -/
lemma upperStarCongr_self {f : X ⟶ Y} (e : f = f) : upperStarCongr Λ e = Iso.refl _ :=
  rfl

/-- Transport of the pullback along `f = g` and then along `g = h` is transport along `f = h`. -/
@[reassoc (attr := simp)]
lemma upperStarCongr_hom_app_trans {f g h : X ⟶ Y} (e₁ : f = g) (e₂ : g = h)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarCongr Λ e₁).hom.app M ≫ (upperStarCongr Λ e₂).hom.app M =
      (upperStarCongr Λ (e₁.trans e₂)).hom.app M := by
  subst e₁ e₂
  exact Category.comp_id _

/-- The congruence isomorphism of the pullbacks is conjugate to the inverse of that of the
pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {f g : X ⟶ Y} (h : f = g) :
    conjugateIsoEquiv (upperStarLowerStarAdjunction Λ g) (upperStarLowerStarAdjunction Λ f)
      (upperStarCongr Λ h) = (lowerStarCongr Λ h).symm := by
  subst h
  ext : 1
  simp [upperStarCongr, lowerStarCongr]

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction Λ g).comp
        (upperStarLowerStarAdjunction Λ f)) (upperStarLowerStarAdjunction Λ (f ≫ g))
      (upperStarComp Λ f g) = lowerStarComp Λ f g := by
  rw [upperStarComp, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply, Iso.symm_symm_eq]

/-- The associativity law for the composition isomorphisms of the pullbacks of module objects,
obtained from `ProEtale.CondensedRing.lowerStarComp_assoc` by conjugation. -/
lemma upperStarComp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    upperStarComp Λ f (g ≫ h) ≪≫ Functor.isoWhiskerRight (upperStarComp Λ g h) (f)^*⟦Λ⟧ ≪≫
        (h)^*⟦Λ⟧.associator (g)^*⟦Λ⟧ (f)^*⟦Λ⟧ =
      upperStarCongr Λ (Category.assoc f g h).symm ≪≫ upperStarComp Λ (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (h)^*⟦Λ⟧ (upperStarComp Λ f g) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction Λ h).comp
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f)))
    (upperStarLowerStarAdjunction Λ (f ≫ g ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction Λ (g ≫ h)).comp
      (upperStarLowerStarAdjunction Λ f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction Λ h).comp
      (upperStarLowerStarAdjunction Λ g)).comp (upperStarLowerStarAdjunction Λ f)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ ((f ≫ g) ≫ h)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction Λ h).comp
      (upperStarLowerStarAdjunction Λ (f ≫ g))) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_upperStarCongr, Iso.trans_assoc]
  rw [lowerStarComp_assoc, lowerStarCongr_symm]

/-- The associativity law for the composition isomorphisms of the pullbacks of module objects,
evaluated at a module object. -/
@[reassoc]
lemma upperStarComp_hom_app_comp_upperStarComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (upperStarComp Λ (f ≫ g) h).hom.app M ≫ (upperStarComp Λ f g).hom.app ((h)^*⟦Λ⟧.obj M) =
      (upperStarCongr Λ (Category.assoc f g h)).hom.app M ≫
        (upperStarComp Λ f (g ≫ h)).hom.app M ≫
          (f)^*⟦Λ⟧.map ((upperStarComp Λ g h).hom.app M) := by
  have := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc Λ f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id] at this
  rw [this, upperStarCongr_hom_app_trans_assoc, upperStarCongr_self, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]

/-- The left unit law for the composition isomorphisms of the pullbacks of module objects,
obtained from `ProEtale.CondensedRing.lowerStarComp_id_left` by conjugation. -/
lemma upperStarComp_id_left (t : X ⟶ Y) :
    upperStarComp Λ (𝟙 X) t = upperStarCongr Λ (Category.id_comp t) ≪≫
      (t)^*⟦Λ⟧.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft (t)^*⟦Λ⟧ (upperStarId Λ X).symm := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction Λ t).comp
    (upperStarLowerStarAdjunction Λ (𝟙 X))) (upperStarLowerStarAdjunction Λ (𝟙 X ≫ t))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ t) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction Λ t).comp Adjunction.id) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor, lowerStarComp_id_left]
  rfl

/-- The right unit law for the composition isomorphisms of the pullbacks of module objects,
obtained from `ProEtale.CondensedRing.lowerStarComp_id_right` by conjugation. -/
lemma upperStarComp_id_right (t : X ⟶ Y) :
    upperStarComp Λ t (𝟙 Y) = upperStarCongr Λ (Category.comp_id t) ≪≫
      (t)^*⟦Λ⟧.leftUnitor.symm ≪≫ Functor.isoWhiskerRight (upperStarId Λ Y).symm (t)^*⟦Λ⟧ := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction Λ (𝟙 Y)).comp
    (upperStarLowerStarAdjunction Λ t)) (upperStarLowerStarAdjunction Λ (t ≫ 𝟙 Y))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ t) _,
    conjugateIsoEquiv_trans _ (Adjunction.id.comp (upperStarLowerStarAdjunction Λ t)) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_leftUnitor, lowerStarComp_id_right]
  rfl

end UpperStar

end ProEtale.CondensedRing

end AlgebraicGeometry
