/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Coherence of the pushforwards and pullbacks on the small pro-étale sites

The composition isomorphisms `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*`
(`AlgebraicGeometry.ProEtale.lowerStarComp`) and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`
(`AlgebraicGeometry.ProEtale.upperStarComp`) satisfy the associativity law: the two ways of
identifying the pushforward (resp. pullback) along `f ≫ g ≫ h` with the composite of the three
pushforwards (resp. pullbacks) agree, up to the identification `(f ≫ g) ≫ h = f ≫ (g ≫ h)`.
For the pushforwards this is the associativity of base change
(`CategoryTheory.MorphismProperty.Over.pullbackComp_assoc`); it passes to the pullbacks by
conjugation along the adjunctions `g^* ⊣ g_*`.

This is the pro-étale counterpart of `CategoryTheory.GrothendieckTopology.upperStarComp_assoc`.

## Main results

- `AlgebraicGeometry.ProEtale.legacy_lowerStarComp_assoc` and
  `AlgebraicGeometry.ProEtale.upperStarComp_assoc`: the associativity laws.
- `AlgebraicGeometry.ProEtale.upperStarComp_hom_app_assoc`: the associativity law for the
  pullbacks, evaluated at a sheaf.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Conjugate

variable {R S T : Scheme.{u}}

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (upperStarComp A h₁ h₂) = lowerStarComp A h₁ h₂ := by
  ext : 1
  exact conjugateEquiv_upperStarComp_hom A h₁ h₂

/-- The congruence isomorphism of the pullbacks is conjugate to the inverse of that of the
pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {g g' : S ⟶ R} (h : g = g') :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A g') (upperStarLowerStarAdjunction A g)
      (upperStarCongr A h) = (lowerStarCongr A h).symm := by
  subst h
  ext : 1
  simp [upperStarCongr, lowerStarCongr]

end Conjugate

section Components

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction maps of `g_* G` are those of `G` along the base changes. -/
lemma lowerStar_obj_obj_map' {Z W : Scheme.{u}} (g : Z ⟶ W) (G : Sheaf (ProEt.topology Z) A)
    {V V' : W.ProEtᵒᵖ} (φ : V ⟶ V') :
    ((g)_*[A].obj G).obj.map φ =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map φ.unop).op :=
  rfl

end Components

section Assoc

variable {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)

set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for the composition isomorphisms of the pushforwards. -/
lemma legacy_lowerStarComp_assoc :
    (f)_*[A].associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) =
      Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
        lowerStarCongr A (Category.assoc f g h) := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [Quiver.Hom.unop_op]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
    · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]

/-- The associativity law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.legacy_lowerStarComp_assoc` by conjugation. -/
lemma upperStarComp_assoc :
    upperStarComp A f (g ≫ h) ≪≫ Functor.isoWhiskerRight (upperStarComp A g h) (f)^*[A] ≪≫
        (h)^*[A].associator (g)^*[A] (f)^*[A] =
      upperStarCongr A (Category.assoc f g h).symm ≪≫ upperStarComp A (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (h)^*[A] (upperStarComp A f g) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A h).comp
    ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f)))
    (upperStarLowerStarAdjunction A (f ≫ g ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A (g ≫ h)).comp
      (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A g)).comp (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A ((f ≫ g) ≫ h)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A (f ≫ g))) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_upperStarCongr, Iso.trans_assoc]
  rw [legacy_lowerStarComp_assoc]
  congr 2

/-- The associativity law for the composition isomorphisms of the pullbacks, evaluated at a
sheaf. -/
lemma upperStarComp_hom_app_comp_upperStarComp_hom_app (M : Sheaf (ProEt.topology V) A) :
    (upperStarComp A (f ≫ g) h).hom.app M ≫ (upperStarComp A f g).hom.app ((h)^*[A].obj M) =
      (upperStarCongr A (Category.assoc f g h)).hom.app M ≫
        (upperStarComp A f (g ≫ h)).hom.app M ≫ (f)^*[A].map ((upperStarComp A g h).hom.app M) := by
  have := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc A f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id] at this
  rw [this, ← Category.assoc, ← NatTrans.comp_app, ← Iso.trans_hom]
  simp [upperStarCongr]

end Assoc


section Paste

variable {P P' P'' Y Y' Y'' Z : Scheme.{u}}

/-- The composition isomorphism `a^* ≅ c^* ⋙ b^*` of pullbacks along a factorisation
`b ≫ c = a`. -/
noncomputable def upperStarFactor {a : P ⟶ Y} {b : P ⟶ Z} {c : Z ⟶ Y} (e : b ≫ c = a) :
    (a)^*[A] ≅ (c)^*[A] ⋙ (b)^*[A] :=
  upperStarCongr A e.symm ≪≫ upperStarComp A b c

/-- The factorisation isomorphism of the trivial factorisation is the composition isomorphism. -/
lemma upperStarFactor_rfl (b : P ⟶ Z) (c : Z ⟶ Y) :
    upperStarFactor A (rfl : b ≫ c = b ≫ c) = upperStarComp A b c := by
  simp only [upperStarFactor, upperStarCongr, eqToIso_refl, Iso.refl_trans]

/-- The isomorphism of a commutative square `a ≫ b = c ≫ d` in terms of factorisations of a
common composite `k`. -/
lemma upperStarCompIso_eq_upperStarFactor {Z₁ Z₂ : Scheme.{u}} {a : P ⟶ Z₁} {b : Z₁ ⟶ Y}
    {c : P ⟶ Z₂} {d : Z₂ ⟶ Y} (h : a ≫ b = c ≫ d) {k : P ⟶ Y} (e₁ : a ≫ b = k)
    (e₂ : c ≫ d = k) :
    upperStarCompIso A h = (upperStarFactor A e₁).symm ≪≫ upperStarFactor A e₂ := by
  subst e₁
  rw [upperStarFactor_rfl]
  rfl

/-- The associativity law for the factorisation isomorphisms. -/
lemma upperStarFactor_hom_app_assoc {a : P'' ⟶ Y} {x : P'' ⟶ P'} {y : P' ⟶ Z} {z : Z ⟶ Y}
    {b : P' ⟶ Y} {c : P'' ⟶ Z} (e_b : y ≫ z = b) (e_a : x ≫ b = a) (e_c : x ≫ y = c)
    (e_a' : c ≫ z = a) (M : Sheaf (ProEt.topology Y) A) :
    (upperStarFactor A e_a).hom.app M ≫ (x)^*[A].map ((upperStarFactor A e_b).hom.app M) =
      (upperStarFactor A e_a').hom.app M ≫ (upperStarFactor A e_c).hom.app ((z)^*[A].obj M) := by
  subst e_b e_c e_a
  simp only [upperStarFactor, upperStarCongr, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.id_comp]
  rw [upperStarComp_hom_app_comp_upperStarComp_hom_app]
  simp only [upperStarCongr, eqToIso.hom, eqToHom_refl, NatTrans.id_app, Category.id_comp]

/-- Factorisations through equal morphisms give the same isomorphism. -/
lemma upperStarFactor_hom_app_comp_congr {a : P'' ⟶ Y} {g : Y' ⟶ Y} {c₁ c₂ : P'' ⟶ Y'}
    {t'' : P'' ⟶ Y''} {g' : Y'' ⟶ Y'} (p : c₁ = c₂) (e₁ : c₁ ≫ g = a) (e₂ : c₂ ≫ g = a)
    (f₁ : t'' ≫ g' = c₁) (f₂ : t'' ≫ g' = c₂) (M : Sheaf (ProEt.topology Y) A) :
    (upperStarFactor A e₁).hom.app M ≫ (upperStarFactor A f₁).hom.app ((g)^*[A].obj M) =
      (upperStarFactor A e₂).hom.app M ≫ (upperStarFactor A f₂).hom.app ((g)^*[A].obj M) := by
  subst p
  have : e₁ = e₂ := rfl
  have : f₁ = f₂ := rfl
  subst_vars
  rfl

/-- The pasting law for the isomorphisms `b^* ⋙ a^* ≅ d^* ⋙ c^*` attached to commutative
squares: the isomorphisms of two squares `τ ≫ t = t' ≫ g` and `τ' ≫ t' = t'' ≫ g'` paste to the
isomorphism of the composite square `(τ' ≫ τ) ≫ t = t'' ≫ (g' ≫ g)`. -/
lemma upperStarCompIso_hom_app_paste {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {t : P ⟶ Y} {t' : P' ⟶ Y'}
    {t'' : P'' ⟶ Y''} {g : Y' ⟶ Y} {g' : Y'' ⟶ Y'}
    (h : τ ≫ t = t' ≫ g) (h' : τ' ≫ t' = t'' ≫ g') (h'' : (τ' ≫ τ) ≫ t = t'' ≫ (g' ≫ g))
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarComp A τ' τ).hom.app ((t)^*[A].obj M) ≫
        (τ')^*[A].map ((upperStarCompIso A h).hom.app M) ≫
        (upperStarCompIso A h').hom.app ((g)^*[A].obj M) =
      (upperStarCompIso A h'').hom.app M ≫ (t'')^*[A].map ((upperStarComp A g' g).hom.app M) := by
  have ea : (τ' ≫ t') ≫ g = (τ' ≫ τ) ≫ t := by simp only [Category.assoc, h]
  have ea' : (t'' ≫ g') ≫ g = (τ' ≫ τ) ≫ t := by simp only [Category.assoc, h'']
  have e₁ := upperStarFactor_hom_app_assoc A (rfl : τ ≫ t = τ ≫ t)
    (Category.assoc τ' τ t).symm (rfl : τ' ≫ τ = τ' ≫ τ) (rfl : (τ' ≫ τ) ≫ t = (τ' ≫ τ) ≫ t) M
  have e₂ := upperStarFactor_hom_app_assoc A h.symm (Category.assoc τ' τ t).symm
    (rfl : τ' ≫ t' = τ' ≫ t') ea M
  have e₃ := upperStarFactor_hom_app_assoc A (rfl : g' ≫ g = g' ≫ g) h''.symm
    (rfl : t'' ≫ g' = t'' ≫ g') ea' M
  have e₄ := upperStarFactor_hom_app_comp_congr A h' ea ea' h'.symm rfl M
  rw [upperStarCompIso_eq_upperStarFactor A h rfl h.symm,
    upperStarCompIso_eq_upperStarFactor A h' rfl h'.symm,
    upperStarCompIso_eq_upperStarFactor A h'' rfl h''.symm,
    ← upperStarFactor_rfl A τ' τ, ← upperStarFactor_rfl A g' g,
    ← cancel_epi ((upperStarFactor A (rfl : (τ' ≫ τ) ≫ t = (τ' ≫ τ) ≫ t)).hom.app M)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [reassoc_of% e₁.symm]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% e₂, e₃]
  simp only [Iso.hom_inv_id_app_assoc]
  exact e₄

end Paste


section Factor

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `b_* ⋙ c_* ≅ a_*` of pushforwards along a factorisation
`b ≫ c = a`. -/
noncomputable def lowerStarFactor {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (e : b ≫ c = a) :
    (b)_*[A] ⋙ (c)_*[A] ≅ (a)_*[A] :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b c a e.symm).symm) A
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarFactor_hom_app_hom_app {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (e : b ≫ c = a)
    (G : Sheaf (ProEt.topology Z) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarFactor A e).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp b c a e.symm).hom.app V.unop).op := by
  simp only [lowerStarFactor, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarFactor_inv_app_hom_app {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (e : b ≫ c = a)
    (G : Sheaf (ProEt.topology Z) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarFactor A e).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp b c a e.symm).inv.app V.unop).op := by
  simp only [lowerStarFactor, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism followed by a congruence is a factorisation isomorphism. -/
lemma lowerStarComp_trans_lowerStarCongr {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X}
    (e : b ≫ c = a) : lowerStarComp A b c ≪≫ lowerStarCongr A e = lowerStarFactor A e := by
  subst e
  rw [lowerStarCongr_rfl, Iso.trans_refl]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option backward.isDefEq.respectTransparency.types false in
lemma lowerStarId_hom_app_hom_app (G : Sheaf (ProEt.topology X) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op := by
  simp [lowerStarId]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option backward.isDefEq.respectTransparency.types false in
lemma lowerStarId_inv_app_hom_app (G : Sheaf (ProEt.topology X) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op := by
  simp [lowerStarId]

/-- The unit `M ⟶ f_* i_* M` of pushforwards along morphisms with `i ≫ f = 𝟙`. -/
noncomputable def lowerStarUnit {i : X ⟶ Y} {f : Y ⟶ X} (h : i ≫ f = 𝟙 X) :
    𝟭 (Sheaf (ProEt.topology X) A) ⟶ (i)_*[A] ⋙ (f)_*[A] :=
  (lowerStarFactor A h ≪≫ lowerStarId A X).inv

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The units of pushforwards along inverse morphisms are compatible with composition. -/
lemma lowerStarUnit_app_comp_map_lowerStarFactor_inv {W : Scheme.{u}} {a : X ⟶ Y} {ai : Y ⟶ X}
    {b : Y ⟶ W} {bi : W ⟶ Y} {ab : X ⟶ W} {abi : W ⟶ X} (ha : ai ≫ a = 𝟙 Y)
    (hb : bi ≫ b = 𝟙 W) (hab : abi ≫ ab = 𝟙 W) (e₁ : a ≫ b = ab) (e₂ : bi ≫ ai = abi)
    (M : Sheaf (ProEt.topology W) A) :
    (lowerStarUnit A hab).app M ≫ (ab)_*[A].map ((lowerStarFactor A e₂).inv.app M) =
      (lowerStarUnit A hb).app M ≫ (b)_*[A].map ((lowerStarUnit A ha).app ((bi)_*[A].obj M)) ≫
        (lowerStarFactor A e₁).hom.app _ := by
  ext V
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_hom_app_hom_app,
    lowerStarFactor_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]


omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The units of the pushforwards along inverse automorphisms `e_U` of `U` and `e_X` of `X`
are compatible with the pushforward along `j : U ⟶ X` when `j ≫ e_X = e_U ≫ j`. -/
lemma lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor_hom_app {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (ProEt.topology U) A) :
    (j)_*[A].map ((lowerStarUnit A eU.inv_hom_id).app M) ≫
        (lowerStarFactor A (rfl : eU.hom ≫ j = eU.hom ≫ j)).hom.app ((eU.inv)_*[A].obj M) =
      (lowerStarUnit A eX.inv_hom_id).app ((j)_*[A].obj M) ≫
        (eX.hom)_*[A].map ((lowerStarFactor A e').hom.app M ≫
          (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M) ≫
        (lowerStarFactor A e).hom.app ((eU.inv)_*[A].obj M) := by
  ext V
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_hom_app_hom_app,
    lowerStarFactor_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId,
      pullback.condition_assoc]

end Factor


section IsoTrans

variable {P X Y Z W : Scheme.{u}}

/-- The adjoint transpose of the identification `e^* ≅ (e⁻¹)_*` is the unit of the
pushforwards along `e⁻¹` and `e`. -/
lemma upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv (e : X ≅ Y)
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarLowerStarAdjunction A e.hom).unit.app M ≫
        (e.hom)_*[A].map ((upperStarIsoLowerStarInv A e).hom.app M) =
      (lowerStarUnit A e.inv_hom_id).app M := by
  rw [upperStarIsoLowerStarInv, Adjunction.unit_leftAdjointUniq_hom_app, lowerStarUnit,
    ← lowerStarComp_trans_lowerStarCongr, Iso.trans_assoc]
  rfl

/-- The adjoint transpose of a factorisation isomorphism of pullbacks is the corresponding
factorisation isomorphism of pushforwards, applied to the composite of the units. -/
lemma upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor {a : P ⟶ Y} {b : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) (M : Sheaf (ProEt.topology Y) A) :
    (upperStarLowerStarAdjunction A a).unit.app M ≫
        (a)_*[A].map ((upperStarFactor A e).hom.app M) =
      (upperStarLowerStarAdjunction A c).unit.app M ≫
        (c)_*[A].map ((upperStarLowerStarAdjunction A b).unit.app ((c)^*[A].obj M)) ≫
        (lowerStarFactor A e).hom.app ((b)^*[A].obj ((c)^*[A].obj M)) := by
  subst e
  have h := unit_conjugateEquiv ((upperStarLowerStarAdjunction A c).comp
    (upperStarLowerStarAdjunction A b)) (upperStarLowerStarAdjunction A (b ≫ c))
    (upperStarComp A b c).hom M
  rw [conjugateEquiv_upperStarComp_hom, Adjunction.comp_unit_app] at h
  rw [upperStarFactor_rfl, ← h, ← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl,
    Iso.trans_refl, Category.assoc]
  rfl

/-- The identifications `e^* ≅ (e⁻¹)_*` are compatible with composition of isomorphisms. -/
lemma upperStarIsoLowerStarInv_hom_app_trans (e₁ : X ≅ Y) (e₂ : Y ≅ W) (E : X ≅ W)
    (hE : e₁.hom ≫ e₂.hom = E.hom) (hEi : e₂.inv ≫ e₁.inv = E.inv)
    (M : Sheaf (ProEt.topology W) A) :
    (upperStarIsoLowerStarInv A E).hom.app M ≫ (lowerStarFactor A hEi).inv.app M =
      (upperStarFactor A hE).hom.app M ≫
        (e₁.hom)^*[A].map ((upperStarIsoLowerStarInv A e₂).hom.app M) ≫
        (upperStarIsoLowerStarInv A e₁).hom.app ((e₂.inv)_*[A].obj M) := by
  apply ((upperStarLowerStarAdjunction A E.hom).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor,
    lowerStarUnit_app_comp_map_lowerStarFactor_inv A e₁.inv_hom_id e₂.inv_hom_id E.inv_hom_id hE
      hEi]
  have n₁ := (lowerStarFactor A hE).hom.naturality
    ((e₁.hom)^*[A].map ((upperStarIsoLowerStarInv A e₂).hom.app M) ≫
      (upperStarIsoLowerStarInv A e₁).hom.app ((e₂.inv)_*[A].obj M))
  have n₂ := (upperStarLowerStarAdjunction A e₁.hom).unit_naturality
    ((upperStarIsoLowerStarInv A e₂).hom.app M)
  simp only [Functor.comp_map] at n₁
  rw [← Functor.map_comp (E.hom)_*[A], ← n₁, ← Functor.map_comp_assoc,
    Functor.map_comp (e₁.hom)_*[A], reassoc_of% n₂,
    upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv, Functor.map_comp,
    Category.assoc,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv]


/-- The counit of `j^* ⊣ j_*` is compatible with the identifications `e^* ≅ (e⁻¹)_*` for
automorphisms `e_U` of `U` and `e_X` of `X` with `j ≫ e_X = e_U ≫ j`: the two ways of going from
`(e_U ≫ j)^* j_* M` to `(e_U⁻¹)_* M` agree, the second one through
`(e_X⁻¹)_* j_* ≅ j_* (e_U⁻¹)_*`. -/
lemma upperStarComp_hom_app_comp_map_counit_comp_upperStarIsoLowerStarInv {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (ProEt.topology U) A) :
    (upperStarComp A eU.hom j).hom.app ((j)_*[A].obj M) ≫
        (eU.hom)^*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫
        (upperStarIsoLowerStarInv A eU).hom.app M =
      (upperStarFactor A e).hom.app ((j)_*[A].obj M) ≫
        (j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M) ≫
          (lowerStarFactor A e').hom.app M ≫
          (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M) ≫
        (upperStarLowerStarAdjunction A j).counit.app ((eU.inv)_*[A].obj M) := by
  have h₁ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor A
    (rfl : eU.hom ≫ j = eU.hom ≫ j) ((j)_*[A].obj M)
  rw [upperStarFactor_rfl] at h₁
  have h₂ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor A e
    ((j)_*[A].obj M)
  have n₁ := (lowerStarFactor A (rfl : eU.hom ≫ j = eU.hom ≫ j)).hom.naturality
    ((eU.hom)^*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫
      (upperStarIsoLowerStarInv A eU).hom.app M)
  have n₂ := (lowerStarFactor A e).hom.naturality
    ((j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M) ≫
      (lowerStarFactor A e').hom.app M ≫
        (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M) ≫
      (upperStarLowerStarAdjunction A j).counit.app ((eU.inv)_*[A].obj M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp,
    Category.assoc] at n₁ n₂
  have u₁ := congrArg (j)_*[A].map
    ((upperStarLowerStarAdjunction A eU.hom).unit_naturality
      ((upperStarLowerStarAdjunction A j).counit.app M))
  have i₁ := congrArg (j)_*[A].map
    (upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv A eU M)
  have t₁ := (upperStarLowerStarAdjunction A j).right_triangle_components M
  have t₂ := congrArg (eX.hom)_*[A].map
    ((upperStarLowerStarAdjunction A j).right_triangle_components ((eU.inv)_*[A].obj M))
  have w₁ := congrArg (eX.hom)_*[A].map ((upperStarLowerStarAdjunction A j).unit_naturality
    ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M)))
  have w₂ := congrArg (eX.hom)_*[A].map ((upperStarLowerStarAdjunction A j).unit_naturality
    ((lowerStarFactor A e').hom.app M))
  have w₃ := congrArg (eX.hom)_*[A].map ((upperStarLowerStarAdjunction A j).unit_naturality
    ((lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M))
  have i₂ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv A eX
    ((j)_*[A].obj M)
  have P := lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor_hom_app A j eU eX e e' M
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
    at u₁ i₁ t₂ w₁ w₂ w₃ P
  apply ((upperStarLowerStarAdjunction A (eU.hom ≫ j)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← n₁, ← n₂, reassoc_of% u₁, reassoc_of% i₁,
    reassoc_of% t₁, reassoc_of% w₁, reassoc_of% w₂, reassoc_of% w₃, reassoc_of% t₂,
    reassoc_of% i₂]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact P
end IsoTrans


section Misc

variable {X Y Z : Scheme.{u}}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarCongr_hom_app_comp_lowerStarComp_inv_app {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X}
    (h : a = b ≫ c) (M : Sheaf (ProEt.topology Z) A) :
    (lowerStarCongr A h).hom.app M ≫ (lowerStarComp A b c).inv.app M =
      (lowerStarFactor A h.symm).inv.app M := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl, Iso.trans_refl]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Pushing forward along `i = 𝟙` and then along `f` is pushing forward along `f`. -/
lemma lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_comp_map_lowerStarId {i : Z ⟶ Z}
    {f a : Z ⟶ Y} (h₀ : i = 𝟙 Z) (h₁ : a = i ≫ f) (h : a = f)
    (M : Sheaf (ProEt.topology Z) A) :
    (lowerStarCongr A h₁).hom.app M ≫ (lowerStarComp A i f).inv.app M ≫
        (f)_*[A].map ((lowerStarCongr A h₀).hom.app M ≫ (lowerStarId A Z).hom.app M) =
      (lowerStarCongr A h).hom.app M := by
  subst h₀ h₁
  ext V
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, lowerStarComp_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStarId_hom_app_hom_app, ← Functor.map_comp, ← op_comp]
  refine (congrArg M.obj.map ?_).trans (M.obj.map_id _)
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId] <;> rfl

/-- The identifications `e^* ≅ (e⁻¹)_*` along equal isomorphisms. -/
lemma upperStarIsoLowerStarInv_hom_app_congr {e e' : X ≅ Y} (p : e = e')
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarIsoLowerStarInv A e).hom.app M ≫
        (lowerStarCongr A (congrArg Iso.inv p)).hom.app M =
      (upperStarCongr A (congrArg Iso.hom p)).hom.app M ≫
        (upperStarIsoLowerStarInv A e').hom.app M := by
  subst p
  simp [upperStarCongr]

variable {P : Scheme.{u}}

/-- A factorisation isomorphism followed by a congruence in the first factor. -/
lemma upperStarFactor_hom_app_comp_upperStarCongr_hom_app {a : P ⟶ Y} {b b' : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) (p : b = b') (e' : b' ≫ c = a)
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarFactor A e).hom.app M ≫ (upperStarCongr A p).hom.app ((c)^*[A].obj M) =
      (upperStarFactor A e').hom.app M := by
  subst p
  have : e = e' := rfl
  subst this
  simp [upperStarCongr]

end Misc


section Congr

variable {P Q R : Scheme.{u}}

/-- The congruence isomorphisms of the pullbacks compose. -/
lemma upperStarCongr_trans {g g' g'' : P ⟶ Q} (h : g = g') (h' : g' = g'') :
    upperStarCongr A h ≪≫ upperStarCongr A h' = upperStarCongr A (h.trans h') := by
  subst h h'
  simp [upperStarCongr]

/-- The composition isomorphism of the pullbacks is natural in the first morphism. -/
lemma upperStarCongr_hom_app_comp_upperStarComp_hom_app {x y : P ⟶ Q} (p : x = y) (g : Q ⟶ R)
    (M : Sheaf (ProEt.topology R) A) :
    (upperStarCongr A (congrArg (· ≫ g) p)).hom.app M ≫ (upperStarComp A y g).hom.app M =
      (upperStarComp A x g).hom.app M ≫ (upperStarCongr A p).hom.app ((g)^*[A].obj M) := by
  subst p
  simp [upperStarCongr]

/-- The composition isomorphism of the pullbacks is natural in the second morphism. -/
lemma upperStarCongr_hom_app_comp_upperStarComp_hom_app' (g : P ⟶ Q) {x y : Q ⟶ R} (p : x = y)
    (M : Sheaf (ProEt.topology R) A) :
    (upperStarCongr A (congrArg (g ≫ ·) p)).hom.app M ≫ (upperStarComp A g y).hom.app M =
      (upperStarComp A g x).hom.app M ≫ (g)^*[A].map ((upperStarCongr A p).hom.app M) := by
  subst p
  simp [upperStarCongr]

end Congr

section UnitLaws

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
lemma _root_.CategoryTheory.MorphismProperty.Over.pullbackCongr_hom_app_eq {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (h' : g = f) (V : Y.ProEt) :
    (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h).hom.app V =
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h').inv.app V := by
  subst h
  simp [MorphismProperty.Over.pullbackCongr_refl]

set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_id_right_hom_app (t : X ⟶ Y) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarComp A t (𝟙 Y)).hom.app M = (lowerStarId A Y).hom.app ((t)_*[A].obj M) ≫
      (lowerStarCongr A (Category.comp_id t).symm).hom.app M := by
  ext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStar_obj_obj_map', lowerStarId_hom_app_hom_app]
  rw [MorphismProperty.Over.pullbackComp_id_right t (t ≫ 𝟙 Y) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    MorphismProperty.Over.pullbackCongr_hom_app_eq _ (Category.comp_id t).symm]
  exact (congrArg M.obj.map op_comp).trans (M.obj.map_comp _ _)


omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The right unit law for the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_id_right (t : X ⟶ Y) :
    lowerStarComp A t (𝟙 Y) = Functor.isoWhiskerLeft (t)_*[A] (lowerStarId A Y) ≪≫
      (t)_*[A].rightUnitor ≪≫ (lowerStarCongr A (Category.comp_id t)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [lowerStarComp_id_right_hom_app, Functor.comp_obj, lowerStarCongr_rfl, Iso.refl_symm,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom, NatTrans.comp_app, Functor.id_obj,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, NatTrans.id_app, Category.id_comp]
  rfl

/-- The right unit law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_id_right` by conjugation. -/
lemma upperStarComp_id_right (t : X ⟶ Y) :
    upperStarComp A t (𝟙 Y) = upperStarCongr A (Category.comp_id t) ≪≫
      (t)^*[A].leftUnitor.symm ≪≫ Functor.isoWhiskerRight (upperStarId A Y).symm (t)^*[A] := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A (𝟙 Y)).comp
    (upperStarLowerStarAdjunction A t)) (upperStarLowerStarAdjunction A (t ≫ 𝟙 Y))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A t) _,
    conjugateIsoEquiv_trans _ (Adjunction.id.comp (upperStarLowerStarAdjunction A t)) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_leftUnitor, lowerStarComp_id_right]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp


set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_id_left_hom_app (t : X ⟶ Y) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarComp A (𝟙 X) t).hom.app M = (t)_*[A].map ((lowerStarId A X).hom.app M) ≫
      (lowerStarCongr A (Category.id_comp t).symm).hom.app M := by
  ext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStar_map_hom_app', lowerStarId_hom_app_hom_app]
  rw [MorphismProperty.Over.pullbackComp_id_left t (𝟙 X ≫ t) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
    MorphismProperty.Over.pullbackCongr_hom_app_eq _ (Category.id_comp t).symm]
  exact (congrArg M.obj.map op_comp).trans (M.obj.map_comp _ _)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The left unit law for the composition isomorphisms of the pushforwards. -/
lemma legacy_lowerStarComp_id_left (t : X ⟶ Y) :
    lowerStarComp A (𝟙 X) t = Functor.isoWhiskerRight (lowerStarId A X) (t)_*[A] ≪≫
      (t)_*[A].leftUnitor ≪≫ (lowerStarCongr A (Category.id_comp t)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [lowerStarComp_id_left_hom_app, Functor.comp_obj, lowerStarCongr_rfl, Iso.refl_symm,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, Functor.id_obj,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, NatTrans.id_app, Category.id_comp]
  rfl

/-- The left unit law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.legacy_lowerStarComp_id_left` by conjugation. -/
lemma upperStarComp_id_left (t : X ⟶ Y) :
    upperStarComp A (𝟙 X) t = upperStarCongr A (Category.id_comp t) ≪≫
      (t)^*[A].rightUnitor.symm ≪≫ Functor.isoWhiskerLeft (t)^*[A] (upperStarId A X).symm := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A t).comp
    (upperStarLowerStarAdjunction A (𝟙 X))) (upperStarLowerStarAdjunction A (𝟙 X ≫ t))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A t) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A t).comp Adjunction.id) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor, legacy_lowerStarComp_id_left]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp

end UnitLaws

end AlgebraicGeometry.ProEtale
