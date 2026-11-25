/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Pushforward and pullback of pro-étale sheaves along an isomorphism

For an isomorphism of schemes `e : X ≅ Y`, the pushforwards `(e.hom)_*` and `(e.inv)_*` on
pro-étale sheaves are mutually inverse equivalences, by the identity and composition
isomorphisms `ProEtale.lowerStarId` and `ProEtale.lowerStarComp`. Consequently the pullback
`(e.hom)^*`, the left adjoint of `(e.hom)_*`, is the pushforward `(e.inv)_*` along the inverse.

Pushforwards are given by an explicit formula, `(g_* G)(V) = G(V ×_Y Z)`, and they are lax
monoidal; pullbacks are only characterised by their universal property. This is why the
Frobenius pullbacks of Weil sheaves (`WeilConjectures.WeilSheaf.Category`) are realised as
pushforwards along the inverse Frobenius.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStarCongr`: `g_* ≅ g'_*` for `g = g'`.
- `AlgebraicGeometry.ProEtale.upperStarCompIso`: `a^* ∘ b^* ≅ c^* ∘ d^*` for `a ≫ b = c ≫ d`.
- `AlgebraicGeometry.ProEtale.lowerStarEquivalence`: the equivalence `(e.hom)_*` with inverse
  `(e.inv)_*`.
- `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`: `(e.hom)^* ≅ (e.inv)_*`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarEquivalence_symm_symm_toAdjunction`: the adjunctions
  `(e.hom)_* ⊣ (e.inv)_*` obtained from `lowerStarEquivalence e` and from
  `lowerStarEquivalence e.symm` agree. This rests on the triangle identity
  `AlgebraicGeometry.ProEtale.lowerStar_map_unit_comp_counit` for the identity and composition
  isomorphisms of pushforwards.
- `AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarComp_hom`,
  `AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarComp_inv` and
  `AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarCongr_inv`: the composition and congruence
  isomorphisms of pullbacks are conjugate to those of pushforwards.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

/-- The pushforwards along equal morphisms are isomorphic. -/
noncomputable def lowerStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)_*[A] ≅ (g')_*[A] :=
  eqToIso (by rw [h])

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarCongr_rfl {Z Y : Scheme.{u}} {g : Z ⟶ Y} :
    lowerStarCongr A (rfl : g = g) = Iso.refl _ :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along the opposite of base change; the form of
`ProEtale.lowerStar_map_hom_app` at an object of the opposite site. -/
lemma lowerStar_map_hom_app' {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {G G' : Sheaf (ProEt.topology Z) A} (φ : G ⟶ G') (V : Y.ProEtᵒᵖ) :
    ((g)_*[A].map φ).hom.app V =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` are the
restriction maps along the pullback pasting isomorphisms. -/
lemma lowerStarComp_hom_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op := by
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_inv_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).inv.app V.unop).op := by
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `g_* ≅ g'_*` for `g = g'` are the restriction maps along the canonical
isomorphisms `V ×_{Y,g'} Z ≅ V ×_{Y,g} Z`. -/
lemma lowerStarCongr_hom_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A h).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).inv.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).inv.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

/-- The pullbacks along equal morphisms are isomorphic. -/
noncomputable def upperStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)^*[A] ≅ (g')^*[A] :=
  eqToIso (by rw [h])

/-- The pullbacks along the two sides of a commutative square `a ≫ b = c ≫ d` agree:
`a^* ∘ b^* ≅ (a ≫ b)^* = (c ≫ d)^* ≅ c^* ∘ d^*`. -/
noncomputable def upperStarCompIso {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) :
    (b)^*[A] ⋙ (a)^*[A] ≅ (d)^*[A] ⋙ (c)^*[A] :=
  (upperStarComp A a b).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A c d

variable {X Y : Scheme.{u}}

/-- The pushforward along an isomorphism `e : X ≅ Y` is an equivalence of categories of
pro-étale sheaves, with inverse the pushforward along `e.inv`. -/
noncomputable def lowerStarEquivalence (e : X ≅ Y) :
    Sheaf (ProEt.topology X) A ≌ Sheaf (ProEt.topology Y) A :=
  CategoryTheory.Equivalence.mk (e.hom)_*[A] (e.inv)_*[A]
    ((lowerStarId A X).symm ≪≫ lowerStarCongr A e.hom_inv_id.symm ≪≫
      (lowerStarComp A e.hom e.inv).symm)
    (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarEquivalence_functor (e : X ≅ Y) :
    (lowerStarEquivalence A e).functor = (e.hom)_*[A] :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarEquivalence_inverse (e : X ≅ Y) :
    (lowerStarEquivalence A e).inverse = (e.inv)_*[A] :=
  rfl

/-- The pullback along an isomorphism `e` is the pushforward along its inverse: both are left
adjoint to the pushforward `(e.hom)_*`. -/
noncomputable def upperStarIsoLowerStarInv (e : X ≅ Y) : (e.hom)^*[A] ≅ (e.inv)_*[A] :=
  (upperStarLowerStarAdjunction A e.hom).leftAdjointUniq
    (lowerStarEquivalence A e).symm.toAdjunction


section Coherence

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforwards along equal morphisms are identified through the base change functors:
`lowerStarCongr` is induced by `MorphismProperty.Over.pullbackCongr`. -/
lemma lowerStarCongr_eq {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    lowerStarCongr A h = Functor.sheafPushforwardContinuousIso
      (MorphismProperty.Over.pullbackCongr h) A _ _ := by
  subst h
  ext M V
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, MorphismProperty.Over.pullbackCongr_refl,
    Functor.sheafPushforwardContinuousIso_hom, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    Functor.whiskerRight_app, NatTrans.op_app, Iso.refl_inv, op_id]
  exact (((sheafToPresheaf (ProEt.topology Z) A).obj M).map_id _).symm

/-- The triangle identity for base change along an isomorphism `e : X ≅ Y` on the small
pro-étale sites, built from `MorphismProperty.Over.pullbackId`,
`MorphismProperty.Over.pullbackCongr` and `MorphismProperty.Over.pullbackComp`. -/
lemma overPullback_triangle {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.ProEt) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).inv.app V) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).map
        ((MorphismProperty.Over.pullbackCongr e.inv_hom_id).inv.app V) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).map
        ((MorphismProperty.Over.pullbackComp e.inv e.hom).hom.app V) ≫
      (MorphismProperty.Over.pullbackComp e.hom e.inv).inv.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj V) ≫
      (MorphismProperty.Over.pullbackCongr e.hom_inv_id.symm).inv.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj V) ≫
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj V) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, pullback.condition_assoc]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The triangle identity `(e.hom)_* η ≫ ε (e.hom)_* = 𝟙` for the unit and counit of
`lowerStarEquivalence e` before adjointification. It is the image under pushforward of the
triangle identity `overPullback_triangle` on the sites. -/
lemma lowerStar_map_unit_comp_counit {X Y : Scheme.{u}} (e : X ≅ Y)
    (S : Sheaf (ProEt.topology X) A) :
    (e.hom)_*[A].map (((lowerStarId A X).symm ≪≫ lowerStarCongr A e.hom_inv_id.symm ≪≫
      (lowerStarComp A e.hom e.inv).symm).hom.app S) ≫
      (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y).hom.app
        ((e.hom)_*[A].obj S) = 𝟙 _ := by
  have := Functor.sheafPushforwardContinuous_triangle (A := A)
    (J := ProEt.topology X) (K := ProEt.topology Y)
    (MorphismProperty.Over.pullbackComp e.hom e.inv).symm
    (MorphismProperty.Over.pullbackComp e.inv e.hom).symm
    (MorphismProperty.Over.pullbackCongr e.hom_inv_id.symm)
    (MorphismProperty.Over.pullbackCongr e.inv_hom_id)
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y) (overPullback_triangle e) S
    (hP := ProEt.isContinuous_overPullback _) (hQ := ProEt.isContinuous_overPullback _)
    (hRX := ProEt.isContinuous_overPullback _) (hR'X := ProEt.isContinuous_overPullback _)
    (hRY := ProEt.isContinuous_overPullback _) (hR'Y := ProEt.isContinuous_overPullback _)
  rw [lowerStarCongr_eq, lowerStarCongr_eq]
  exact this

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The adjunctions `(e.hom)_* ⊣ (e.inv)_*` given by `lowerStarEquivalence e` and by
`lowerStarEquivalence e.symm` agree: the unit of the first is the adjointification of a unit
which already satisfies the triangle identity `lowerStar_map_unit_comp_counit`, and the unit of
the second is the inverse of the counit of `lowerStarEquivalence e.symm`, which is the same
composite of identity, congruence and composition isomorphisms. -/
lemma lowerStarEquivalence_symm_symm_toAdjunction (e : X ≅ Y) :
    (lowerStarEquivalence A e.symm).symm.toAdjunction =
      (lowerStarEquivalence A e).toAdjunction := by
  apply Adjunction.ext
  have := Equivalence.adjointifyη_eq _ _ (lowerStar_map_unit_comp_counit A e)
  change (lowerStarComp A e.hom e.inv ≪≫ lowerStarCongr A e.symm.inv_hom_id ≪≫
    lowerStarId A X).inv = (Equivalence.adjointifyη _ _).hom
  rw [this]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- The congruence isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_upperStarCongr_inv {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateEquiv (upperStarLowerStarAdjunction A g) (upperStarLowerStarAdjunction A g')
      (upperStarCongr A h).inv = (lowerStarCongr A h).hom := by
  subst h
  simp [upperStarCongr, lowerStarCongr]

/-- The composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_upperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
      (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (upperStarComp A h₁ h₂).hom =
        (lowerStarComp A h₁ h₂).hom := by
  have := conjugateEquiv_comm (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
    ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
    (α := (upperStarComp A h₁ h₂).inv) (β := (upperStarComp A h₁ h₂).hom) (by simp)
  have h : conjugateEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
      (upperStarComp A h₁ h₂).inv = (lowerStarComp A h₁ h₂).inv :=
    congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (lowerStarComp A h₁ h₂).symm)
  rw [h] at this
  rw [← cancel_epi (lowerStarComp A h₁ h₂).inv, this, Iso.inv_hom_id]

/-- The inverse composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_upperStarComp_inv {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
      (upperStarComp A h₁ h₂).inv = (lowerStarComp A h₁ h₂).inv :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (lowerStarComp A h₁ h₂).symm)

end Coherence

variable {Z W : Scheme.{u}} (g : Z ⟶ W) [IsIso g]

instance isEquivalence_lowerStar : (g)_*[A].IsEquivalence :=
  (lowerStarEquivalence A (asIso g)).isEquivalence_functor

instance isEquivalence_upperStar : (g)^*[A].IsEquivalence :=
  Functor.isEquivalence_of_iso (upperStarIsoLowerStarInv A (asIso g)).symm

end ProEtale

end AlgebraicGeometry
