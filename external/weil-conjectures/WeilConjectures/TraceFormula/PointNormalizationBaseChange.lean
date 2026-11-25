/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp
public import WeilConjectures.TraceFormula.PointNormalizationKunneth
public import WeilConjectures.TraceFormula.PointNormalizationTau
public import WeilConjectures.TraceFormula.LocalTerm

/-!

# Point normalization of the trace class: the base change part

Over the base point, the comparison `ζ : LΔ^* ⟶ Rp₁_!` of `CategoryTheory.Verdier.transportζ`
at `Lp₁^* y` is `LΔ^* Lp₁^* y ≅ y` followed by the unit of `Lp₁^* ⊣ Rp₁_!`
(`ProEtale.CondensedRing.Correspondence.transportζ_upperStar_fst`). This rests on the
compatibility of the units of the adjunctions `Lf^* ⊣ Rf_!` of proper morphisms with the
composition isomorphisms (`ProEtale.CondensedRing.upperStarLowerShriekAdjunction_comp_unit_app`),
which is the compatibility of `Rf_! ≅ Rf_*` with composition (blueprint
`prop-functor-package`, clause (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

lemma iso_inv_app_comp_map_comp_hom_app {C : Type*} [Category C] {aS : C ⥤ C} (i : aS ≅ 𝟭 C)
    {x z : C} (m : x ⟶ z) : i.inv.app x ≫ aS.map m ≫ i.hom.app z = m := by
  simp

variable {C P : Type*} [Category C] [Category P] {aS aL : C ⥤ C} {fS sS : C ⥤ P} {fL : P ⥤ C}

/-- The isomorphism `F ≅ F ∘ A ≅ S ∘ A ≅ S` induced by `θ : A ⋙ F ≅ A ⋙ S` and `A ≅ 𝟭`. -/
noncomputable def isoOfWhiskerLeftIso (i : aS ≅ 𝟭 C) (θ : aS ⋙ fS ≅ aS ⋙ sS) : fS ≅ sS :=
  (Functor.leftUnitor fS).symm ≪≫ Functor.isoWhiskerRight i.symm fS ≪≫ θ ≪≫
    Functor.isoWhiskerRight i sS ≪≫ Functor.leftUnitor sS

lemma isoOfWhiskerLeftIso_hom_app (i : aS ≅ 𝟭 C) (θ : aS ⋙ fS ≅ aS ⋙ sS) (y : C) :
    (isoOfWhiskerLeftIso i θ).hom.app y =
      fS.map (i.inv.app y) ≫ θ.hom.app y ≫ sS.map (i.hom.app y) := by
  simp [isoOfWhiskerLeftIso]

/-- A rearrangement of units and base change maps, used for compact-support base change in the
product square over the base point. -/
lemma unit_map_comp_eq_of_baseChange_aux (η : 𝟭 C ⟶ fS ⋙ fL) (ηa : 𝟭 C ⟶ aS ⋙ aL)
    (ex : aL ⋙ aS ⟶ sS ⋙ fL) (θ : aS ⋙ fS ≅ aS ⋙ sS) (i : aS ≅ 𝟭 C) (j : aL ≅ 𝟭 C) (y : C)
    (hmu : aS.map (ηa.app y) ≫ ex.app (aS.obj y) = η.app (aS.obj y) ≫ fL.map (θ.hom.app y))
    (hG : ηa.app y ≫ aL.map (i.hom.app y) = j.inv.app y) :
    η.app y ≫ fL.map ((isoOfWhiskerLeftIso i θ).hom.app y) =
      i.inv.app y ≫ aS.map (j.inv.app y) ≫ ex.app y := by
  have hExn := ex.naturality (i.hom.app y)
  have hηn := η.naturality (i.inv.app y)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hExn hηn
  rw [isoOfWhiskerLeftIso_hom_app, Functor.map_comp, Functor.map_comp, ← reassoc_of% hηn,
    ← reassoc_of% hmu, ← hExn, ← Functor.map_comp_assoc, hG]

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section General

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **The units of `Lf^* ⊣ Rf_!` are compatible with composition**: for proper `f` and `g`,
the unit of `L(f ≫ g)^* ⊣ R(f ≫ g)_!` read through the composition isomorphisms is the unit of
the composite adjunction `Lg^* ⋙ Lf^* ⊣ Rf_! ⋙ Rg_!`. -/
lemma upperStarLowerShriekAdjunction_comp_unit_app (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left]
    [IsProper g.left] [IsProper (f ≫ g).left] (c : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (f ≫ g)).unit.app c ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
          ((boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj c) ≫
        (boundedConstructibleLowerShriek ℓ g).map ((boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarComp _ ℓ f g).hom.app c)) =
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g).unit.app c ≫
        (boundedConstructibleLowerShriek ℓ g).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app
            ((boundedConstructibleUpperStar _ ℓ g).obj c)) :=
  Adjunction.ofNatIsoRight_comp_unit_app
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g))
    (boundedConstructibleUpperStarComp _ ℓ f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (fun K ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g K) c

variable (X) in
/-- The counit of `R(𝟙)_! ⊣ R(𝟙)^!` is `R(𝟙)_! R(𝟙)^! ≅ R(𝟙)^! ≅ 𝟭`. -/
lemma upperShriekAdjunction_id_counit_app (d : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X)).counit.app d =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
          ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj d) ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app d := by
  have h := conjugateEquiv_counit (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).inv d
  simp only [Functor.id_map, Adjunction.id_counit, NatTrans.id_app] at h
  erw [Category.comp_id] at h
  change (boundedConstructibleUpperShriekId ℓ X).hom.app d = _ at h
  rw [h, Iso.hom_inv_id_app_assoc]

/-- The unit of `Lr^* ⊣ Rr_!` for a morphism `r` equal to the identity, read through an
isomorphism `c : Lr^* y ≅ X'`: it is `X' ≅ R(𝟙)_! X' = Rr_! X'`. -/
lemma unit_map_comp_of_eq_id {r : X ⟶ X} (hr : r = 𝟙 X) [IsProper r.left]
    {y X' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (c : (boundedConstructibleUpperStar _ ℓ r).obj y ≅ X') :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ r).unit.app X' ≫
        (boundedConstructibleLowerShriek ℓ r).map ((boundedConstructibleUpperStar _ ℓ r).map
          (c.inv ≫ eqToHom (congrArg (fun r : X ⟶ X ↦
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj y) hr) ≫
            (boundedConstructibleUpperStarId _ ℓ X).hom.app y) ≫ c.hom) =
      (boundedConstructibleLowerShriekId ℓ X).inv.app X' ≫
        eqToHom (congrArg (fun r : X ⟶ X ↦
          (boundedConstructibleLowerShriek ℓ r).obj X')
            hr.symm) := by
  subst hr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hn := (boundedConstructibleUpperStarId _ ℓ X).hom.naturality
    (c.inv ≫ (boundedConstructibleUpperStarId _ ℓ X).hom.app y)
  simp only [Functor.id_map] at hn
  have key : (boundedConstructibleUpperStar _ ℓ (𝟙 X)).map
      (c.inv ≫ (boundedConstructibleUpperStarId _ ℓ X).hom.app y) ≫ c.hom =
      (boundedConstructibleUpperStarId _ ℓ X).hom.app X' := by
    rw [← cancel_mono c.inv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← cancel_mono ((boundedConstructibleUpperStarId _ ℓ X).hom.app y)]
    erw [hn]
    rw [Category.assoc]
  have h₁ := upperStarLowerShriekAdjunction_id_unit_app ℓ X X'
  have hn' := (boundedConstructibleLowerShriekId ℓ X).hom.naturality
    ((boundedConstructibleUpperStarId _ ℓ X).hom.app X')
  simp only [Functor.id_map] at hn'
  rw [key, ← cancel_mono ((boundedConstructibleLowerShriekId ℓ X).hom.app X'), Category.assoc]
  erw [hn', reassoc_of% h₁]
  simp

end General

section IdOfEq

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

lemma lowerShriek_map_comp_eqToHom_of_eq {f g : Y ⟶ Y} (h : f = g)
    {L L' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L') :
    (boundedConstructibleLowerShriek ℓ f).map b ≫ eqToHom (congrArg (fun f : Y ⟶ Y ↦
      (boundedConstructibleLowerShriek ℓ f).obj L') h) =
      eqToHom (congrArg (fun f : Y ⟶ Y ↦
        (boundedConstructibleLowerShriek ℓ f).obj L) h) ≫
        (boundedConstructibleLowerShriek ℓ g).map b := by
  subst h
  simp

lemma upperShriek_map_comp_eqToHom_of_eq {f g : Y ⟶ Y} (h : f = g)
    {L L' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L') :
    (boundedConstructibleUpperShriek ℓ f).map b ≫ eqToHom (congrArg (fun f : Y ⟶ Y ↦
      (boundedConstructibleUpperShriek ℓ f).obj L') h) =
      eqToHom (congrArg (fun f : Y ⟶ Y ↦
        (boundedConstructibleUpperShriek ℓ f).obj L) h) ≫
        (boundedConstructibleUpperShriek ℓ g).map b := by
  subst h
  simp

/-- `La^* ≅ L(𝟙)^* ≅ 𝟭` for a morphism `a` equal to the identity. -/
noncomputable def upperStarIdOfEq {a : Y ⟶ Y} (ha : a = 𝟙 Y) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a ≅ 𝟭 _ :=
  NatIso.ofComponents (fun y ↦ eqToIso (congrArg (fun a : Y ⟶ Y ↦
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a).obj y) ha) ≪≫
      (boundedConstructibleUpperStarId _ ℓ Y).app y)
    (fun {y y'} b ↦ by
      simp only [Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc]
      rw [reassoc_of% (upperStar_map_comp_eqToHom_of_eq (ℓ := ℓ) ha b)]
      have h := (boundedConstructibleUpperStarId _ ℓ Y).hom.naturality b
      simp only [Functor.id_map] at h
      rw [h, Functor.id_map])

/-- `Ra_! ≅ R(𝟙)_! ≅ 𝟭` for a morphism `a` equal to the identity. -/
noncomputable def lowerShriekIdOfEq {a : Y ⟶ Y} (ha : a = 𝟙 Y) :
    boundedConstructibleLowerShriek ℓ a ≅ 𝟭 _ :=
  NatIso.ofComponents (fun y ↦ eqToIso (congrArg (fun a : Y ⟶ Y ↦
      (boundedConstructibleLowerShriek ℓ a).obj y) ha) ≪≫
      (boundedConstructibleLowerShriekId ℓ Y).app y)
    (fun {y y'} b ↦ by
      simp only [Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc]
      rw [reassoc_of% (lowerShriek_map_comp_eqToHom_of_eq ℓ ha b)]
      have h := (boundedConstructibleLowerShriekId ℓ Y).hom.naturality b
      simp only [Functor.id_map] at h
      rw [h, Functor.id_map])

/-- `Ra^! ≅ R(𝟙)^! ≅ 𝟭` for a morphism `a` equal to the identity. -/
noncomputable def upperShriekIdOfEq {a : Y ⟶ Y} (ha : a = 𝟙 Y) :
    boundedConstructibleUpperShriek ℓ a ≅ 𝟭 _ :=
  NatIso.ofComponents (fun y ↦ eqToIso (congrArg (fun a : Y ⟶ Y ↦
      (boundedConstructibleUpperShriek ℓ a).obj y) ha) ≪≫
      (boundedConstructibleUpperShriekId ℓ Y).app y)
    (fun {y y'} b ↦ by
      simp only [Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc]
      rw [reassoc_of% (upperShriek_map_comp_eqToHom_of_eq ℓ ha b)]
      have h := (boundedConstructibleUpperShriekId ℓ Y).hom.naturality b
      simp only [Functor.id_map] at h
      rw [h, Functor.id_map])

/-- The unit of `La^* ⊣ Ra_!` for `a = 𝟙`, followed by `Ra_!` of `La^* ≅ 𝟭`, is the inverse of
`Ra_! ≅ 𝟭`. -/
lemma unit_map_upperStarIdOfEq {a : Y ⟶ Y} (ha : a = 𝟙 Y) [IsProper a.left]
    (y : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ a).unit.app y ≫
        (boundedConstructibleLowerShriek ℓ a).map ((upperStarIdOfEq ℓ ha).hom.app y) =
      (lowerShriekIdOfEq ℓ ha).inv.app y := by
  subst ha
  simp only [upperStarIdOfEq, lowerShriekIdOfEq, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.trans_hom, Iso.trans_inv, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, Iso.app_hom, Iso.app_inv, Category.id_comp, Category.comp_id]
  have h₁ := upperStarLowerShriekAdjunction_id_unit_app ℓ Y y
  have hn := (boundedConstructibleLowerShriekId ℓ Y).inv.naturality
    ((boundedConstructibleUpperStarId _ ℓ Y).hom.app y)
  simp only [Functor.id_map] at hn
  have hη : (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 Y)).unit.app y =
      (boundedConstructibleUpperStarId _ ℓ Y).inv.app y ≫
        (boundedConstructibleLowerShriekId ℓ Y).inv.app
          ((boundedConstructibleUpperStar _ ℓ (𝟙 Y)).obj y) := by
    rw [← h₁, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  rw [hη, Category.assoc]
  erw [← hn]
  rw [Iso.inv_hom_id_app_assoc]
  rfl

/-- The counit of `Ra_! ⊣ Ra^!` for `a = 𝟙` is `Ra_! Ra^! ≅ Ra^! ≅ 𝟭`. -/
lemma upperShriekAdjunction_counit_app_of_eq {a : Y ⟶ Y} (ha : a = 𝟙 Y)
    (d : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekAdjunction ℓ a).counit.app d =
      (lowerShriekIdOfEq ℓ ha).hom.app ((boundedConstructibleUpperShriek ℓ a).obj d) ≫
        (upperShriekIdOfEq ℓ ha).hom.app d := by
  subst ha
  simp only [upperShriekIdOfEq, lowerShriekIdOfEq, NatIso.ofComponents_hom_app, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Iso.app_hom, Category.id_comp]
  exact upperShriekAdjunction_id_counit_app ℓ Y d

/-- The unit comparison of `La^*` for `a = 𝟙` is `La^* ≅ 𝟭` at the unit. -/
lemma εIso_inv_of_eq {a : Y ⟶ Y} (ha : a = 𝟙 Y) :
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      a)).inv = (upperStarIdOfEq ℓ ha).hom.app (𝟙_ _) := by
  subst ha
  simp only [upperStarIdOfEq, NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Iso.app_hom, Category.id_comp]
  exact (boundedConstructibleUpperStarId_hom_app_unit ℓ Y).symm

/-- The right unit law of the composition isomorphisms of the derived pullbacks, for a morphism
`a` equal to the identity. -/
lemma upperStarComp_hom_app_map_upperStarIdOfEq {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (f : X ⟶ Y)
    {a : Y ⟶ Y} (ha : a = 𝟙 Y) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp _ ℓ f a).hom.app K ≫
        (boundedConstructibleUpperStar _ ℓ f).map ((upperStarIdOfEq ℓ ha).hom.app K) =
      eqToHom (by rw [ha, Category.comp_id]; rfl) := by
  subst ha
  simp only [upperStarIdOfEq, NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Iso.app_hom, Category.id_comp]
  exact boundedConstructibleUpperStarComp_id_right_app _ ℓ f K

end IdOfEq

namespace Correspondence

instance : IsProper (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k)).left := by
  rw [Over.comp_left]
  infer_instance

/-- **`ζ` on a pullback along `p₁`** over the base point: `ζ_{Lp₁^* y}` is
`LΔ^* Lp₁^* y ≅ y` followed by the unit of `Lp₁^* ⊣ Rp₁_!`. -/
lemma transportζ_upperStar_fst (y : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj y) =
      (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom ≫
        (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
          (prod.fst : point k ⨯ point k ⟶ point k)).unit.app y := by
  have hCF := upperStarLowerShriekAdjunction_comp_unit_app ℓ (diag (point k))
    (prod.fst : point k ⨯ point k ⟶ point k) y
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (diag (point k))
    (prod.fst : point k ⨯ point k ⟶ point k)).hom.naturality
      ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) prod.fst).hom.app y)
  have hu := (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
    (diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k))).unit.naturality
      (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom
  have hG := unit_map_comp_of_eq_id ℓ diag_point_fst
    ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) prod.fst).app y)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn hu
  have key : (pointLowerShriekιΦ ℓ k).inv.app ((boundedConstructibleUpperStar _ ℓ
      (diag (point k))).obj ((boundedConstructibleUpperStar _ ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).obj y)) =
      (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom ≫
        (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
          (prod.fst : point k ⨯ point k ⟶ point k)).unit.app y ≫
        (boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).map
          ((pointDiagAdj ℓ k).unit.app ((boundedConstructibleUpperStar _ ℓ
            (prod.fst : point k ⨯ point k ⟶ point k)).obj y)) := by
    erw [← hCF]
    erw [← hn, reassoc_of% hu, ← Functor.map_comp_assoc]
    simp only [diagUpperStarProjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      eqToIso.hom] at hG ⊢
    rw [reassoc_of% hG]
    simp only [pointLowerShriekιΦ, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, eqToIso.inv,
      eqToHom_app, Category.assoc]
  rw [Verdier.transportζ, key]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]


omit [Fact (ringChar k).Prime] in
lemma toPoint_point_eq : toPoint (point k) = 𝟙 (point k) :=
  toPoint_ext _ _

set_option quotPrecheck false in
/-- The comparison `Lp₁^* ≅ Lp₂^*` over the base point given by the product square of `p₁` and
`p₂` over `a = 𝟙`: `Lp₁^* ≅ Lp₁^* La^* ≅ Lp₂^* La^* ≅ Lp₂^*`. -/
local notation "Θpt" => Verdier.isoOfWhiskerLeftIso
  (upperStarIdOfEq ℓ toPoint_point_eq) (boundedConstructiblePullbackSquareComparison _ ℓ
    (isPullback_prod_toPoint (point k) (point k)).toCommSq)


lemma diagUpperStarProjIso_congr {p q : point k ⨯ point k ⟶ point k} (h : p = q)
    (hp : diag (point k) ≫ p = 𝟙 _) (hq : diag (point k) ≫ q = 𝟙 _)
    (y : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (diagUpperStarProjIso ℓ p hp y).hom =
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
        (eqToHom (congrArg (fun p : point k ⨯ point k ⟶ point k ↦
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj y) h)) ≫
      (diagUpperStarProjIso ℓ q hq y).hom := by
  subst h
  simp

/-- The comparison `Lp₁^* y ≅ Lp₂^* y` is the identification `p₁ = p₂` (the base point is
terminal). -/
lemma pointProdUpperStarComparison_hom_app
    (y : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (Θpt).hom.app y = eqToHom (congrArg (fun p : point k ⨯ point k ⟶ point k ↦
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj y)
        (toPoint_ext _ _)) := by
  have h₁ := upperStarComp_hom_app_map_upperStarIdOfEq ℓ
    (prod.fst : point k ⨯ point k ⟶ point k) toPoint_point_eq y
  have h₂ := upperStarComp_hom_app_map_upperStarIdOfEq ℓ
    (prod.snd : point k ⨯ point k ⟶ point k) toPoint_point_eq y
  rw [Verdier.isoOfWhiskerLeftIso_hom_app]
  simp only [boundedConstructiblePullbackSquareComparison_hom_app, Category.assoc]
  have h₁' : (boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).map
      ((upperStarIdOfEq ℓ toPoint_point_eq).inv.app y) ≫
      (boundedConstructibleUpperStarComp _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)
        (toPoint (point k))).inv.app y =
      eqToHom (by rw [toPoint_point_eq, Category.comp_id]; rfl) := by
    rw [← cancel_mono (eqToHom (by rw [toPoint_point_eq, Category.comp_id]; rfl :
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        ((prod.fst : point k ⨯ point k ⟶ point k) ≫ toPoint (point k))).obj y =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).obj ((𝟭 _).obj y)))]
    conv_lhs => rw [← h₁]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [eqToHom_trans, eqToHom_refl]
  rw [h₂, reassoc_of% h₁', eqToHom_trans, eqToHom_trans]

/-- `LΔ^* Lp₁^* y ≅ y` is `LΔ^* Lp₂^* y ≅ y` read through `Lp₁^* y ≅ Lp₂^* y`. -/
lemma diagUpperStarProjIso_fst_eq (y : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (diagUpperStarProjIso ℓ prod.fst (by simp) y).hom =
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map ((Θpt).hom.app y) ≫
        (diagUpperStarProjIso ℓ prod.snd (by simp) y).hom := by
  rw [pointProdUpperStarComparison_hom_app]
  exact diagUpperStarProjIso_congr ℓ (toPoint_ext _ _) _ _ y

/-- **Compact-support base change in the product square over the base point**, through the
units: the unit of `Lp₁^* ⊣ Rp₁_!` read through `Lp₁^* y ≅ Lp₂^* y` is `Ex_!` at `y`, read
through `La^* ≅ 𝟭` and `Ra_! ≅ 𝟭` for `a = 𝟙`. -/
lemma unit_map_pointProdUpperStarComparison
    (y : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
        (prod.fst : point k ⨯ point k ⟶ point k)).unit.app y ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).map
        ((Θpt).hom.app y) =
    (upperStarIdOfEq ℓ toPoint_point_eq).inv.app y ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint (point k))).map
        ((lowerShriekIdOfEq ℓ toPoint_point_eq).inv.app y) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
        (isPullback_prod_toPoint (point k) (point k))).app y := by
  have hmu := map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app ℓ
    (isPullback_prod_toPoint (point k) (point k)) y
  have hG := unit_map_upperStarIdOfEq ℓ toPoint_point_eq y
  have key := Verdier.unit_map_comp_eq_of_baseChange_aux
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
      (prod.fst : point k ⨯ point k ⟶ point k)).unit
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (toPoint (point k))).unit
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_prod_toPoint (point k) (point k)))
    (boundedConstructiblePullbackSquareComparison _ ℓ
      (isPullback_prod_toPoint (point k) (point k)).toCommSq)
    (upperStarIdOfEq ℓ toPoint_point_eq) (lowerShriekIdOfEq ℓ toPoint_point_eq) y hmu hG
  exact key

/-- The conjugate of `Rp_! ≅ Rq_!` for `p = q` is `Rq^! ≅ Rp^!`. -/
lemma conjugateIsoEquiv_eqToIso_hom_app {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] {p q : X ⟶ Y} (h : p = q)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ p)
      (boundedConstructibleUpperShriekAdjunction ℓ q)
      (eqToIso (congrArg (fun p : X ⟶ Y ↦
        boundedConstructibleLowerShriek ℓ p) h)).symm).hom.app K =
      eqToHom (congrArg (fun p : X ⟶ Y ↦
        (boundedConstructibleUpperShriek ℓ p).obj K) h) := by
  subst h
  simp

/-- **Left unit law of the composition isomorphisms of the exceptional inverse image**:
`R(𝟙 ≫ a)^! ≅ Ra^! ⋙ R(𝟙)^! ≅ Ra^!` is the identity. This is conjugate to the left unit law of
the composition isomorphisms of the lower shriek. -/
lemma upperShriekComp_id_left_hom_app {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (a : X ⟶ Y) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ (𝟙 X) a).hom.app K ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app
          ((boundedConstructibleUpperShriek ℓ a).obj K) =
      eqToHom (congrArg (fun p : X ⟶ Y ↦
        (boundedConstructibleUpperShriek ℓ p).obj K)
          (Category.id_comp a)) := by
  rw [← conjugateIsoEquiv_eqToIso_hom_app ℓ (Category.id_comp a) K]
  exact conjugateIsoEquiv_comp_left_hom_app
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X ≫ a))
    (boundedConstructibleUpperShriekAdjunction ℓ a)
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) a)
    (boundedConstructibleLowerShriekId ℓ X)
    (eqToIso (congrArg (fun p : X ⟶ Y ↦
      boundedConstructibleLowerShriek ℓ p) (Category.id_comp a)))
    (fun K ↦ by
      rw [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
        eqToHom_app]
      exact boundedConstructibleLowerShriekComp_padicAlgCl_id_left ℓ a K) K

/-- The identification `ω_s ≅ R(𝟙)^! ω_s = Rd^! ω_s ≅ ω_s` for `d = 𝟙` is the identity. -/
lemma upperShriekIso_inv_comp_dualizingComplexComp {d : point k ⟶ point k} (hd : d = 𝟙 _) :
    (eqToIso (congrArg (fun d : point k ⟶ point k ↦
        boundedConstructibleUpperShriek ℓ d) hd) ≪≫
        boundedConstructibleUpperShriekId ℓ (point k)).inv.app (dualizingComplex' ℓ (point k)) ≫
      (dualizingComplexComp ℓ d).hom = 𝟙 _ := by
  subst hd
  have h := upperShriekComp_id_left_hom_app ℓ (toPoint (point k)) (𝟙_ _)
  have key : (boundedConstructibleUpperShriekComp_padicAlgCl ℓ (𝟙 _) (toPoint (point k))).inv.app
      (𝟙_ _) ≫ eqToHom (congrArg (fun p : point k ⟶ point k ↦
        (boundedConstructibleUpperShriek ℓ p).obj (𝟙_ _))
          (Category.id_comp (toPoint (point k)))) =
      (boundedConstructibleUpperShriekId ℓ (point k)).hom.app (dualizingComplex' ℓ (point k)) := by
    rw [← cancel_epi ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (𝟙 _)
      (toPoint (point k))).hom.app _), Iso.hom_inv_id_app_assoc, h]
  rw [Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Category.comp_id, dualizingComplexComp, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, eqToIso.hom,
    key, Iso.inv_hom_id_app]

lemma baseChange_app_comp_prodBaseChangeIso_hom_app
    (M : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
        (isPullback_prod_toPoint (point k) (point k))).app M ≫
      (prodBaseChangeIso ℓ (point k) (point k)).hom.app M = 𝟙 _ := by
  simp [prodBaseChangeIso]

/-- `La^* ≅ 𝟭` for `a = 𝟙` at the unit, through `R(𝟙)^! ≅ 𝟭`, is `ω_s ≅ ℚ̄_ℓ`. -/
lemma upperShriekIdOfEq_hom_app_unit :
    (upperShriekIdOfEq ℓ toPoint_point_eq).hom.app (𝟙_ _) = (dualizingComplexPointIso ℓ k).hom := by
  simp only [upperShriekIdOfEq, NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom,
    Iso.app_hom, dualizingComplexPointIso, upperShriekUnitIsoOfEqId]

/-- **The base change part of the transport of the exceptional Künneth map** over the base
point: `ζ` at `Lp₂^* ω_s`, followed by the inverse of compact-support base change in the product
square, the counit at the unit and `La^* ℚ̄_ℓ ≅ ℚ̄_ℓ`, is `LΔ^* Lp₂^* ω_s ≅ ω_s ≅ ℚ̄_ℓ`. -/
lemma pointKunneth_baseChange {φ : dualizingComplex' ℓ (point k) ⟶ 𝟙_ _}
    (hφ : φ = (dualizingComplexPointIso ℓ k).hom) :
    Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj
          (dualizingComplex' ℓ (point k))) ≫
        (prodBaseChangeIso ℓ (point k) (point k)).hom.app (dualizingComplex' ℓ (point k)) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint (point k))).map
          ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint (point k))).counit.app
            (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint (point k)))).inv =
      (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom ≫ φ := by
  subst hφ
  have hζ := Verdier.transportζ_naturality (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
    ((Θpt).hom.app (dualizingComplex' ℓ (point k)))
  have hζ' : Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : point k ⨯ point k ⟶ point k)).obj
        (dualizingComplex' ℓ (point k))) =
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
          ((Θpt).inv.app (dualizingComplex' ℓ (point k))) ≫
        Verdier.transportζ (pointDiagAdj ℓ k) (pointLowerShriekιΦ ℓ k)
          ((boundedConstructibleUpperStar _ ℓ (prod.fst : point k ⨯ point k ⟶ point k)).obj
            (dualizingComplex' ℓ (point k))) ≫
        (boundedConstructibleLowerShriek ℓ (prod.fst : point k ⨯ point k ⟶ point k)).map
          ((Θpt).hom.app (dualizingComplex' ℓ (point k))) := by
    rw [← hζ, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hB := diagUpperStarProjIso_fst_eq ℓ (dualizingComplex' ℓ (point k))
  have hU := unit_map_pointProdUpperStarComparison ℓ (dualizingComplex' ℓ (point k))
  have hE := baseChange_app_comp_prodBaseChangeIso_hom_app ℓ (dualizingComplex' ℓ (point k))
  have h₂ := transportζ_upperStar_fst ℓ (dualizingComplex' ℓ (point k))
  rw [hB] at h₂
  rw [hζ', h₂]
  simp only [Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have hε := εIso_inv_of_eq ℓ (toPoint_point_eq (k := k))
  have hc := upperShriekAdjunction_counit_app_of_eq ℓ (toPoint_point_eq (k := k)) (𝟙_ _)
  have hu := upperShriekIdOfEq_hom_app_unit ℓ (k := k)
  have hi := Verdier.iso_inv_app_comp_map_comp_hom_app
    (upperStarIdOfEq ℓ (toPoint_point_eq (k := k))) (dualizingComplexPointIso ℓ k).hom
  simp only [reassoc_of% hU, reassoc_of% hE, hε, ← Functor.map_comp_assoc, hc,
    Iso.inv_hom_id_app_assoc, hu]
  exact congrArg ((diagUpperStarProjIso ℓ prod.snd (by simp) _).hom ≫ ·) hi

/-- The pairing over the base point is the evaluation followed by `ω_s ≅ ℚ̄_ℓ`. -/
lemma pointPairing_eq {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (v : K ⟶ K) :
    pointPairing v = (ihom.ev K).app (dualizingComplex' ℓ (point k)) ≫
      (dualizingComplexPointIso ℓ k).hom := by
  have hφ := upperShriekIso_inv_comp_dualizingComplexComp ℓ (fixedLocusOfEnd_d v)
  simp only [pointPairing, fixedLocusOfEndUpperShriekIso, reassoc_of% hφ]

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
