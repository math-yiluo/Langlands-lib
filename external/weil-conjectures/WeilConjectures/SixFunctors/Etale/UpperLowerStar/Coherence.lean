/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs

/-!

# Identity and composition isomorphisms of `g_*` and `g^*` on small étale sites

The pushforward `g_*` and the pullback `g^*` of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` come with an identity isomorphism
`(𝟙 V)_* ≅ 𝟭` and a composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*`, and the same
for the pullbacks. This file records those identity isomorphisms and the unit and
associativity laws they satisfy, which make `V ↦ Sheaf V.smallEtaleTopology A` a
pseudofunctor in all but name, both for the pushforwards and for the pullbacks.

Everything here is the `P = Q = @Etale` case of the corresponding statement for the small
`Q`-sites of `P`-schemes in `WeilConjectures.SixFunctors.UpperLowerStar.Defs`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarId` and `AlgebraicGeometry.Etale.upperStarId`: the
  identity isomorphisms `(𝟙 V)_* ≅ 𝟭` and `(𝟙 V)^* ≅ 𝟭`, the latter obtained from the
  former by uniqueness of left adjoints.
- `AlgebraicGeometry.Etale.lowerStarEquivalenceOfIso` and
  `AlgebraicGeometry.Etale.upperStarInvIsoLowerStarHom`: for an isomorphism `e` of schemes,
  `e_*` is an equivalence and `(e⁻¹)^* ≅ e_*`.

## Main results

- `AlgebraicGeometry.Etale.lowerStarComp_id_left`,
  `AlgebraicGeometry.Etale.lowerStarComp_id_right` and
  `AlgebraicGeometry.Etale.lowerStarComp_assoc`, together with their `upperStarComp`
  counterparts: the unit and associativity laws.
- `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarId` and
  `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarComp`: the identity and composition
  isomorphisms of the pullbacks correspond to those of the pushforwards under conjugation
  along the adjunctions `g^* ⊣ g_*`, with their unit and counit forms.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Id

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable (V : Scheme.{u})

open Etale

/-- The identity isomorphism `(𝟙 V)_* ≅ 𝟭` of the pushforward on étale sheaves. -/
noncomputable def Etale.lowerStarId : (𝟙 V)_*[A] ≅ 𝟭 _ :=
  GrothendieckTopology.lowerStarId A @Etale @Etale le_rfl V

/-- The identity isomorphism `(𝟙 V)^* ≅ 𝟭` of the pullback on étale sheaves. -/
noncomputable def Etale.upperStarId : (𝟙 V)^*[A] ≅ 𝟭 _ :=
  GrothendieckTopology.upperStarId A @Etale @Etale le_rfl V

/-- Under the conjugation bijection between `𝟭 ⊣ 𝟭` and `(𝟙 V)^* ⊣ (𝟙 V)_*`, the identity
isomorphism of the pullback corresponds to the identity isomorphism of the pushforward. -/
lemma Etale.conjugateIsoEquiv_upperStarId :
    conjugateIsoEquiv Adjunction.id (Etale.upperStarLowerStarAdjunction A (𝟙 V))
        (Etale.upperStarId A V) = (Etale.lowerStarId A V).symm :=
  GrothendieckTopology.conjugateIsoEquiv_upperStarId A @Etale @Etale le_rfl V

/-- The counit form of `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarId`: transposing
the identity isomorphism of the pullback along the adjunction `(𝟙 V)^* ⊣ (𝟙 V)_*` gives the
identity isomorphism of the pushforward. -/
lemma Etale.upperStarId_inv_app_counit_app (F : Sheaf V.smallEtaleTopology A) :
    (Etale.upperStarId A V).inv.app (((𝟙 V)_*[A]).obj F) ≫
        (Etale.upperStarLowerStarAdjunction A (𝟙 V)).counit.app F =
      (Etale.lowerStarId A V).hom.app F := by
  have hconj : conjugateEquiv (Etale.upperStarLowerStarAdjunction A (𝟙 V))
      (Adjunction.id (C := Sheaf V.smallEtaleTopology A))
      (Etale.upperStarId A V).inv = (Etale.lowerStarId A V).hom :=
    congrArg Iso.inv (Etale.conjugateIsoEquiv_upperStarId A V)
  have h := conjugateEquiv_counit (Etale.upperStarLowerStarAdjunction A (𝟙 V))
    (Adjunction.id (C := Sheaf V.smallEtaleTopology A)) (Etale.upperStarId A V).inv F
  rw [hconj] at h
  simpa using h.symm

/-- The unit form of `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarId`: transposing
the identity isomorphism of the pullback along the adjunction `(𝟙 V)^* ⊣ (𝟙 V)_*` gives the
identity isomorphism of the pushforward. This is the counterpart of
`AlgebraicGeometry.Etale.upperStarId_inv_app_counit_app` on the unit side. -/
lemma Etale.upperStarId_hom_app_unit_app (F : Sheaf V.smallEtaleTopology A) :
    (Etale.upperStarLowerStarAdjunction A (𝟙 V)).unit.app F ≫
        ((𝟙 V)_*[A]).map ((Etale.upperStarId A V).hom.app F) =
      (Etale.lowerStarId A V).inv.app F := by
  have hconj : conjugateEquiv (Adjunction.id (C := Sheaf V.smallEtaleTopology A))
      (Etale.upperStarLowerStarAdjunction A (𝟙 V)) (Etale.upperStarId A V).hom =
      (Etale.lowerStarId A V).inv :=
    congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarId A V)
  have h := unit_conjugateEquiv (Adjunction.id (C := Sheaf V.smallEtaleTopology A))
    (Etale.upperStarLowerStarAdjunction A (𝟙 V)) (Etale.upperStarId A V).hom F
  rw [hconj] at h
  simpa using h.symm

end Id

section Comp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

open Etale

section UpperStar

/-- Under the conjugation bijection between `(h₂)^* ⋙ (h₁)^* ⊣ (h₁)_* ⋙ (h₂)_*` and
`(h₁ ≫ h₂)^* ⊣ (h₁ ≫ h₂)_*`, the composition isomorphism of the pullbacks corresponds to
the composition isomorphism of the pushforwards. -/
lemma Etale.conjugateIsoEquiv_upperStarComp (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    conjugateIsoEquiv ((Etale.upperStarLowerStarAdjunction A h₂).comp
        (Etale.upperStarLowerStarAdjunction A h₁)) (Etale.upperStarLowerStarAdjunction A h₁₂)
      (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂) = Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂ :=
  GrothendieckTopology.conjugateIsoEquiv_upperStarComp A @Etale @Etale le_rfl h₁ h₂ h₁₂ hh₁₂

/-- The counit form of `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarComp`:
transposing the composition isomorphism of the pullbacks along the adjunctions
`h^* ⊣ h_*` gives the composition isomorphism of the pushforwards. -/
lemma Etale.upperStarComp_inv_app_counit_app (F : Sheaf T.smallEtaleTopology A)
    (h₁₂ : T ⟶ R := h₁ ≫ h₂) (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app (((h₁₂)_*[A]).obj F) ≫
        (Etale.upperStarLowerStarAdjunction A h₁₂).counit.app F =
      ((h₁)^*[A]).map (((h₂)^*[A]).map ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app F)) ≫
        ((h₁)^*[A]).map ((Etale.upperStarLowerStarAdjunction A h₂).counit.app
          (((h₁)_*[A]).obj F)) ≫
        (Etale.upperStarLowerStarAdjunction A h₁).counit.app F := by
  have hconj : conjugateEquiv (Etale.upperStarLowerStarAdjunction A h₁₂)
      ((Etale.upperStarLowerStarAdjunction A h₂).comp
        (Etale.upperStarLowerStarAdjunction A h₁))
      (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv =
      (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv :=
    congrArg Iso.inv (Etale.conjugateIsoEquiv_upperStarComp A h₁ h₂ h₁₂ hh₁₂)
  have h := conjugateEquiv_counit (Etale.upperStarLowerStarAdjunction A h₁₂)
    ((Etale.upperStarLowerStarAdjunction A h₂).comp
      (Etale.upperStarLowerStarAdjunction A h₁))
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv F
  rw [hconj] at h
  simpa using h.symm

/-- The unit form of `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarComp`: transposing
the composition isomorphism of the pullbacks along the adjunctions `h^* ⊣ h_*` gives the
composition isomorphism of the pushforwards. This is the counterpart of
`AlgebraicGeometry.Etale.upperStarComp_inv_app_counit_app` on the unit side. -/
lemma Etale.upperStarComp_hom_app_unit_app (F : Sheaf R.smallEtaleTopology A)
    (h₁₂ : T ⟶ R := h₁ ≫ h₂) (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    (Etale.upperStarLowerStarAdjunction A h₁₂).unit.app F ≫
        ((h₁₂)_*[A]).map ((Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app F) =
      ((Etale.upperStarLowerStarAdjunction A h₂).comp
          (Etale.upperStarLowerStarAdjunction A h₁)).unit.app F ≫
        (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app
          (((h₁)^*[A]).obj (((h₂)^*[A]).obj F)) := by
  have hconj : conjugateEquiv ((Etale.upperStarLowerStarAdjunction A h₂).comp
        (Etale.upperStarLowerStarAdjunction A h₁))
      (Etale.upperStarLowerStarAdjunction A h₁₂)
      (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom =
      (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom :=
    congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp A h₁ h₂ h₁₂ hh₁₂)
  have hh := unit_conjugateEquiv ((Etale.upperStarLowerStarAdjunction A h₂).comp
      (Etale.upperStarLowerStarAdjunction A h₁))
    (Etale.upperStarLowerStarAdjunction A h₁₂)
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom F
  rw [hconj] at hh
  exact hh.symm

end UpperStar

end Comp

section Coherence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {R S T : Scheme.{u}}

open Etale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The left unit law for `AlgebraicGeometry.Etale.lowerStarComp`. -/
lemma Etale.lowerStarComp_id_left (h₂ : S ⟶ R) :
    Etale.lowerStarComp A (𝟙 S) h₂ h₂ (Category.id_comp h₂).symm =
      Functor.isoWhiskerRight (Etale.lowerStarId A S) (h₂)_*[A] ≪≫ ((h₂)_*[A]).leftUnitor :=
  GrothendieckTopology.lowerStarComp_id_left A @Etale @Etale le_rfl h₂

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The right unit law for `AlgebraicGeometry.Etale.lowerStarComp`. -/
lemma Etale.lowerStarComp_id_right (h₁ : T ⟶ S) :
    Etale.lowerStarComp A h₁ (𝟙 S) h₁ (Category.comp_id h₁).symm =
      Functor.isoWhiskerLeft (h₁)_*[A] (Etale.lowerStarId A S) ≪≫ ((h₁)_*[A]).rightUnitor :=
  GrothendieckTopology.lowerStarComp_id_right A @Etale @Etale le_rfl h₁

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The associativity law for `AlgebraicGeometry.Etale.lowerStarComp`. -/
lemma Etale.lowerStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fgh : X ⟶ V := f ≫ g ≫ h) (hfgh : fgh = f ≫ g ≫ h := by cat_disch) :
    ((f)_*[A]).associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (Etale.lowerStarComp A g h) ≪≫
          Etale.lowerStarComp A f (g ≫ h) fgh hfgh =
      Functor.isoWhiskerRight (Etale.lowerStarComp A f g) (h)_*[A] ≪≫
        Etale.lowerStarComp A (f ≫ g) h fgh (by rw [hfgh, Category.assoc]) :=
  GrothendieckTopology.lowerStarComp_assoc A @Etale @Etale le_rfl f g h fgh hfgh

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- Absorbing the transport along an equality `h₁ ≫ h₂ = h₁₂` of morphisms into the
composition isomorphism `AlgebraicGeometry.Etale.lowerStarComp` at `h₁₂`. -/
lemma Etale.lowerStarComp_trans_eqToIso {W X' Y' : Scheme.{u}} (k₁ : W ⟶ X') (k₂ : X' ⟶ Y')
    (k₁₂ : W ⟶ Y') (hk : k₁ ≫ k₂ = k₁₂) :
    Etale.lowerStarComp A k₁ k₂ ≪≫ eqToIso (congrArg (fun g => (g)_*[A]) hk) =
      Etale.lowerStarComp A k₁ k₂ k₁₂ hk.symm := by
  subst hk
  simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The associativity law for `AlgebraicGeometry.Etale.lowerStarComp` in the form of an
equality of natural transformations, with all three composites of the morphisms named. -/
lemma Etale.lowerStarComp_assoc' {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    Functor.whiskerRight (Etale.lowerStarComp A f g fg hfg).hom ((h)_*[A]) ≫
        (Etale.lowerStarComp A fg h fgh hfgh).hom =
      Functor.whiskerLeft ((f)_*[A]) (Etale.lowerStarComp A g h gh hgh).hom ≫
        (Etale.lowerStarComp A f gh fgh
          (by rw [hfgh, hfg, hgh, Category.assoc])).hom := by
  subst hfg
  subst hgh
  subst hfgh
  have key := congrArg Iso.hom
    (Etale.lowerStarComp_assoc A f g h ((f ≫ g) ≫ h) (Category.assoc f g h))
  refine NatTrans.ext (funext fun G => ?_)
  simpa using (NatTrans.congr_app key G).symm

/-- The left unit law for `AlgebraicGeometry.Etale.upperStarComp`. -/
lemma Etale.upperStarComp_id_left (h₂ : S ⟶ R) :
    Etale.upperStarComp A (𝟙 S) h₂ h₂ (Category.id_comp h₂).symm =
      ((h₂)^*[A]).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (h₂)^*[A] (Etale.upperStarId A S).symm :=
  GrothendieckTopology.upperStarComp_id_left A @Etale @Etale le_rfl h₂

/-- The right unit law for `AlgebraicGeometry.Etale.upperStarComp`. -/
lemma Etale.upperStarComp_id_right (h₁ : T ⟶ S) :
    Etale.upperStarComp A h₁ (𝟙 S) h₁ (Category.comp_id h₁).symm =
      ((h₁)^*[A]).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (Etale.upperStarId A S).symm (h₁)^*[A] :=
  GrothendieckTopology.upperStarComp_id_right A @Etale @Etale le_rfl h₁

/-- The associativity law for `AlgebraicGeometry.Etale.upperStarComp`. -/
lemma Etale.upperStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fgh : X ⟶ V := f ≫ g ≫ h) (hfgh : fgh = f ≫ g ≫ h := by cat_disch) :
    Etale.upperStarComp A f (g ≫ h) fgh hfgh ≪≫
        Functor.isoWhiskerRight (Etale.upperStarComp A g h) (f)^*[A] ≪≫
          ((h)^*[A]).associator (g)^*[A] (f)^*[A] =
      Etale.upperStarComp A (f ≫ g) h fgh (by rw [hfgh, Category.assoc]) ≪≫
        Functor.isoWhiskerLeft (h)^*[A] (Etale.upperStarComp A f g) :=
  GrothendieckTopology.upperStarComp_assoc A @Etale @Etale le_rfl f g h fgh hfgh

end Coherence

section IsIso

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {S T : Scheme.{u}} (f : T ⟶ S) [IsIso f]

open Etale

/-- The pullback `f^*` along an isomorphism `f` is an equivalence of categories of étale
sheaves, with inverse the pullback `(f⁻¹)^*`. -/
noncomputable def Etale.upperStarEquivalenceOfIsIso :
    Sheaf S.smallEtaleTopology A ≌ Sheaf T.smallEtaleTopology A :=
  .mk (f)^*[A] (inv f)^*[A]
    ((Etale.upperStarId A S).symm ≪≫ Etale.upperStarComp A (inv f) f (𝟙 S) (by simp))
    ((Etale.upperStarComp A f (inv f) (𝟙 T) (by simp)).symm ≪≫ Etale.upperStarId A T)

/-- The pullback along an isomorphism is an equivalence. Unlike
`AlgebraicGeometry.Etale.isEquivalence_upperStar` for universal homeomorphisms, this needs
only the composition and identity isomorphisms of the pullbacks. -/
instance Etale.isEquivalence_upperStar_of_isIso : ((f)^*[A]).IsEquivalence :=
  (Etale.upperStarEquivalenceOfIsIso A f).isEquivalence_functor

/-- The pushforward along an isomorphism is an equivalence, being right adjoint to the
equivalence `f^*`. -/
instance Etale.isEquivalence_lowerStar_of_isIso : ((f)_*[A]).IsEquivalence :=
  (Etale.upperStarLowerStarAdjunction A f).isEquivalence_right_of_isEquivalence_left

end IsIso

section Iso

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {U U' : Scheme.{u}} (e : U ≅ U')

open Etale

/-- The pushforwards along an isomorphism `e` of schemes and along its inverse form an
equivalence of the categories of étale sheaves. -/
noncomputable def Etale.lowerStarEquivalenceOfIso :
    Sheaf U.smallEtaleTopology A ≌ Sheaf U'.smallEtaleTopology A :=
  CategoryTheory.Equivalence.mk (e.hom)_*[A] (e.inv)_*[A]
    ((Etale.lowerStarId A U).symm ≪≫ (Etale.lowerStarComp A e.hom e.inv (𝟙 U) (by simp)).symm)
    (Etale.lowerStarComp A e.inv e.hom (𝟙 U') (by simp) ≪≫ Etale.lowerStarId A U')

/-- The pullback along the inverse of an isomorphism `e` of schemes is the pushforward along
`e`: `(e⁻¹)^* ≅ e_*`. -/
noncomputable def Etale.upperStarInvIsoLowerStarHom : (e.inv)^*[A] ≅ (e.hom)_*[A] :=
  -- both are left adjoint to `(e⁻¹)_*`
  (Etale.upperStarLowerStarAdjunction A e.inv).leftAdjointUniq
    (Etale.lowerStarEquivalenceOfIso A e).toAdjunction

end Iso

end AlgebraicGeometry
