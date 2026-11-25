/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStarCounit
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence

/-!
# Coherence of the commutation of derived scalar extension with `Lg^*`

The isomorphisms `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S` of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso` are compatible with the
identity isomorphisms `L(𝟙 Y)^* ≅ 𝟭`, with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` and with the transport along equalities of morphisms
(blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).

The coherence arguments are first proved for arbitrary additive functors, localization functors
and left derived functors (the `_aux` lemmas below) and then instantiated: at the concrete
pro-étale sheaf categories, the kernel would otherwise unfold the concrete derived categories and
the instances of the homotopy categories while checking the rewriting steps.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Generic

variable {ι : Type*} {c : ComplexShape ι}

/-- The natural transformations induced on homotopy categories by an isomorphism are inverse to
each other, componentwise. -/
private lemma mapHomotopyCategory_hom_app_inv_app_aux {V W : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : HomotopyCategory V c) :
    (NatTrans.mapHomotopyCategory e.hom c).app K ≫
      (NatTrans.mapHomotopyCategory e.inv c).app K = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]

/-- Generic form of `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_id`: a
transformation `E ⋙ q ⟶ p ⋙ E` compatible with `p ⟶ 𝟭` and `q ⟶ 𝟭` induces one on homotopy
categories with the same property. -/
private lemma mapHomotopyCategory_hom_app_id_aux {V W : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] {E : V ⥤ W} {p : V ⥤ V} {q : W ⥤ W}
    [E.Additive] [p.Additive] [q.Additive] (e : E ⋙ q ⟶ p ⋙ E)
    (e' : E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c)
    (he' : ∀ C, e'.app ((HomotopyCategory.quotient V c).obj C) =
      (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex e c).app C))
    (α : p ⟶ 𝟭 V) (β : q ⟶ 𝟭 W) (h : ∀ F, e.app F ≫ E.map (α.app F) = β.app (E.obj F))
    (K : HomotopyCategory V c) :
    e'.app K ≫ (E.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory α c).app K) =
      (NatTrans.mapHomotopyCategory β c).app ((E.mapHomotopyCategory c).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [he']
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_obj_as, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (C.X n)

/-- Generic form of `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_comp`:
transformations `E ⋙ q ⟶ p ⋙ E'` compatible with `p₁₂ ⟶ p ⋙ p₁` and `q₁₂ ⟶ q ⋙ q₁` induce
transformations on homotopy categories with the same property. -/
private lemma mapHomotopyCategory_hom_app_comp_aux {VY VZ VT WY WZ WT : Type*} [Category VY]
    [Category VZ] [Category VT] [Category WY] [Category WZ] [Category WT] [Preadditive VY]
    [Preadditive VZ] [Preadditive VT] [Preadditive WY] [Preadditive WZ] [Preadditive WT]
    {EY : VY ⥤ WY} {EZ : VZ ⥤ WZ} {ET : VT ⥤ WT} {p : VY ⥤ VZ} {p₁ : VZ ⥤ VT}
    {p₁₂ : VY ⥤ VT} {q : WY ⥤ WZ} {q₁ : WZ ⥤ WT} {q₁₂ : WY ⥤ WT}
    [EY.Additive] [EZ.Additive] [ET.Additive] [p.Additive] [p₁.Additive] [p₁₂.Additive]
    [q.Additive] [q₁.Additive] [q₁₂.Additive]
    (e : EY ⋙ q ⟶ p ⋙ EZ) (e₁ : EZ ⋙ q₁ ⟶ p₁ ⋙ ET) (e₁₂ : EY ⋙ q₁₂ ⟶ p₁₂ ⋙ ET)
    (e' : EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c)
    (e₁' : EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⟶
      p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (e₁₂' : EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⟶
      p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (he' : ∀ C, e'.app ((HomotopyCategory.quotient VY c).obj C) =
      (HomotopyCategory.quotient WZ c).map ((NatTrans.mapHomologicalComplex e c).app C))
    (he₁' : ∀ C, e₁'.app ((HomotopyCategory.quotient VZ c).obj C) =
      (HomotopyCategory.quotient WT c).map ((NatTrans.mapHomologicalComplex e₁ c).app C))
    (he₁₂' : ∀ C, e₁₂'.app ((HomotopyCategory.quotient VY c).obj C) =
      (HomotopyCategory.quotient WT c).map ((NatTrans.mapHomologicalComplex e₁₂ c).app C))
    (γR : p₁₂ ⟶ p ⋙ p₁) (γS : q₁₂ ⟶ q ⋙ q₁)
    (h : ∀ F, e₁₂.app F ≫ ET.map (γR.app F) =
      γS.app (EY.obj F) ≫ q₁.map (e.app F) ≫ e₁.app (p.obj F))
    (K : HomotopyCategory VY c) :
    e₁₂'.app K ≫ (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR c).app K) =
      (NatTrans.mapHomotopyCategory γS c).app ((EY.mapHomotopyCategory c).obj K) ≫
        (q₁.mapHomotopyCategory c).map (e'.app K) ≫
        e₁'.app ((p.mapHomotopyCategory c).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [he₁₂', he']
  erw [he₁' ((p.mapHomologicalComplex c).obj C)]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_obj_as, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (C.X n)

/-- Generic form of `leftDerivedUpperStarExtendScalarsIso_hom_app_id`, over arbitrary
localization functors `Qv`, `Qw` and left derived functors. The two composite counits are taken
as arguments `γ₁`, `γ₂` (with their defining equations), and the composites are ascribed the
right-associated functor types, so that the concrete instance matches the concrete counits
syntactically. -/
private lemma leftDerived_hom_app_id_aux {V W DV DW : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] [Category DV] [Category DW]
    {Qv : HomotopyCategory V c ⥤ DV} {Qw : HomotopyCategory W c ⥤ DW}
    (Wv : MorphismProperty (HomotopyCategory V c)) [Qv.IsLocalization Wv]
    {E : V ⥤ W} {p : V ⥤ V} {q : W ⥤ W} [E.Additive] [p.Additive] [q.Additive]
    {LE : DV ⥤ DW} (αE : Qv ⋙ LE ⟶ E.mapHomotopyCategory c ⋙ Qw)
    [LE.IsLeftDerivedFunctor αE Wv]
    {Lp : DV ⥤ DV} (αp : Qv ⋙ Lp ⟶ p.mapHomotopyCategory c ⋙ Qv)
    {Lq : DW ⥤ DW} (αq : Qw ⋙ Lq ⟶ q.mapHomotopyCategory c ⋙ Qw)
    (Φ : LE ⋙ Lq ⟶ Lp ⋙ LE)
    (eH : E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c)
    (γ₁ : Qv ⋙ LE ⋙ Lq ⟶ E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⋙ Qw)
    (hγ₁ : γ₁ = (Functor.whiskerRight αE Lq ≫ Functor.whiskerLeft (E.mapHomotopyCategory c) αq :
      Qv ⋙ LE ⋙ Lq ⟶ E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⋙ Qw))
    (γ₂ : Qv ⋙ Lp ⋙ LE ⟶ p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c ⋙ Qw)
    (hγ₂ : γ₂ = (Functor.whiskerRight αp LE ≫ Functor.whiskerLeft (p.mapHomotopyCategory c) αE :
      Qv ⋙ Lp ⋙ LE ⟶ p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c ⋙ Qw))
    (hΦ : ∀ K, Φ.app (Qv.obj K) ≫ γ₂.app K = γ₁.app K ≫
      Qw.map (X := (E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c).obj K) (eH.app K))
    (ιR : Lp ⟶ 𝟭 DV) (βR : p ⟶ 𝟭 V)
    (hR : ∀ K, ιR.app (Qv.obj K) =
      αp.app K ≫ Qv.map ((NatTrans.mapHomotopyCategory βR c).app K))
    (ιS : Lq ⟶ 𝟭 DW) (βS : q ⟶ 𝟭 W)
    (hS : ∀ K, ιS.app (Qw.obj K) =
      αq.app K ≫ Qw.map ((NatTrans.mapHomotopyCategory βS c).app K))
    (e : E ⋙ q ⟶ p ⋙ E) (h : ∀ F, e.app F ≫ E.map (βR.app F) = βS.app (E.obj F))
    (heH : ∀ C, eH.app ((HomotopyCategory.quotient V c).obj C) =
      (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex e c).app C))
    (K : DV) :
    Φ.app K ≫ LE.map (ιR.app K) = ιS.app (LE.obj K) := by
  subst hγ₁ hγ₂
  have he := mapHomotopyCategory_hom_app_id_aux e eH heH βR βS h
  have key : Φ ≫ Functor.whiskerRight ιR LE ≫ (Functor.leftUnitor _).hom =
      Functor.whiskerLeft LE ιS ≫ (Functor.rightUnitor _).hom := by
    apply Functor.leftDerived_ext (LF := LE) (α := αE) (W := Wv)
    ext K
    have h := hΦ K
    have hn := αE.naturality ((NatTrans.mapHomotopyCategory βR c).app K)
    have hn' := ιS.naturality (αE.app K)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, Functor.comp_map, Functor.id_map] at h hn hn' ⊢
    simp only [Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, hR, Functor.map_comp,
      Category.assoc]
    erw [Category.id_comp, hn, reassoc_of% h, ← Qw.map_comp, he, ← hS, hn']
    rfl
  simpa using NatTrans.congr_app key K

/-- Generic form of `leftDerivedUpperStarExtendScalarsIso_hom_app_comp`, over arbitrary
localization functors and left derived functors (see `leftDerived_hom_app_id_aux`). -/
private lemma leftDerived_hom_app_comp_aux {VY VZ VT WY WZ WT DY DZ DT D'Y D'Z D'T : Type*}
    [Category VY] [Category VZ] [Category VT] [Category WY] [Category WZ] [Category WT]
    [Preadditive VY] [Preadditive VZ] [Preadditive VT] [Preadditive WY] [Preadditive WZ]
    [Preadditive WT]
    [Category DY] [Category DZ] [Category DT] [Category D'Y] [Category D'Z] [Category D'T]
    {QY : HomotopyCategory VY c ⥤ DY} {QZ : HomotopyCategory VZ c ⥤ DZ}
    {QT : HomotopyCategory VT c ⥤ DT} {Q'Y : HomotopyCategory WY c ⥤ D'Y}
    {Q'Z : HomotopyCategory WZ c ⥤ D'Z} {Q'T : HomotopyCategory WT c ⥤ D'T}
    (Wq : MorphismProperty (HomotopyCategory VY c)) [QY.IsLocalization Wq]
    {EY : VY ⥤ WY} {EZ : VZ ⥤ WZ} {ET : VT ⥤ WT} {p : VY ⥤ VZ} {p₁ : VZ ⥤ VT}
    {p₁₂ : VY ⥤ VT} {q : WY ⥤ WZ} {q₁ : WZ ⥤ WT} {q₁₂ : WY ⥤ WT}
    [EY.Additive] [EZ.Additive] [ET.Additive] [p.Additive] [p₁.Additive] [p₁₂.Additive]
    [q.Additive] [q₁.Additive] [q₁₂.Additive]
    {LEY : DY ⥤ D'Y} (αEY : QY ⋙ LEY ⟶ EY.mapHomotopyCategory c ⋙ Q'Y)
    {LEZ : DZ ⥤ D'Z} (αEZ : QZ ⋙ LEZ ⟶ EZ.mapHomotopyCategory c ⋙ Q'Z)
    {LET : DT ⥤ D'T} (αET : QT ⋙ LET ⟶ ET.mapHomotopyCategory c ⋙ Q'T)
    {Lp : DY ⥤ DZ} (αp : QY ⋙ Lp ⟶ p.mapHomotopyCategory c ⋙ QZ)
    {Lp₁ : DZ ⥤ DT} (αp₁ : QZ ⋙ Lp₁ ⟶ p₁.mapHomotopyCategory c ⋙ QT)
    {Lp₁₂ : DY ⥤ DT} (αp₁₂ : QY ⋙ Lp₁₂ ⟶ p₁₂.mapHomotopyCategory c ⋙ QT)
    {Lq : D'Y ⥤ D'Z} (αq : Q'Y ⋙ Lq ⟶ q.mapHomotopyCategory c ⋙ Q'Z)
    {Lq₁ : D'Z ⥤ D'T} (αq₁ : Q'Z ⋙ Lq₁ ⟶ q₁.mapHomotopyCategory c ⋙ Q'T)
    {Lq₁₂ : D'Y ⥤ D'T} (αq₁₂ : Q'Y ⋙ Lq₁₂ ⟶ q₁₂.mapHomotopyCategory c ⋙ Q'T)
    (Φ : LEY ⋙ Lq ⟶ Lp ⋙ LEZ)
    (eH : EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c)
    (γ₁ : QY ⋙ LEY ⋙ Lq ⟶ EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⋙ Q'Z)
    (hγ₁ : γ₁ = (Functor.whiskerRight αEY Lq ≫ Functor.whiskerLeft (EY.mapHomotopyCategory c) αq :
      QY ⋙ LEY ⋙ Lq ⟶ EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⋙ Q'Z))
    (γ₂ : QY ⋙ Lp ⋙ LEZ ⟶ p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c ⋙ Q'Z)
    (hγ₂ : γ₂ = (Functor.whiskerRight αp LEZ ≫ Functor.whiskerLeft (p.mapHomotopyCategory c) αEZ :
      QY ⋙ Lp ⋙ LEZ ⟶ p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c ⋙ Q'Z))
    (hΦ : ∀ K, Φ.app (QY.obj K) ≫ γ₂.app K = γ₁.app K ≫
      Q'Z.map (X := (EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c).obj K) (eH.app K))
    (Φ₁ : LEZ ⋙ Lq₁ ⟶ Lp₁ ⋙ LET)
    (e₁H : EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⟶
      p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (γ₁' : QZ ⋙ LEZ ⋙ Lq₁ ⟶ EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⋙ Q'T)
    (hγ₁' : γ₁' =
      (Functor.whiskerRight αEZ Lq₁ ≫ Functor.whiskerLeft (EZ.mapHomotopyCategory c) αq₁ :
        QZ ⋙ LEZ ⋙ Lq₁ ⟶ EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⋙ Q'T))
    (γ₂' : QZ ⋙ Lp₁ ⋙ LET ⟶ p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T)
    (hγ₂' : γ₂' =
      (Functor.whiskerRight αp₁ LET ≫ Functor.whiskerLeft (p₁.mapHomotopyCategory c) αET :
        QZ ⋙ Lp₁ ⋙ LET ⟶ p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T))
    (hΦ₁ : ∀ K, Φ₁.app (QZ.obj K) ≫ γ₂'.app K = γ₁'.app K ≫
      Q'T.map (X := (EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c).obj K) (e₁H.app K))
    (Φ₁₂ : LEY ⋙ Lq₁₂ ⟶ Lp₁₂ ⋙ LET)
    (e₁₂H : EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⟶
      p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (γ₁'' : QY ⋙ LEY ⋙ Lq₁₂ ⟶ EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⋙ Q'T)
    (hγ₁'' : γ₁'' =
      (Functor.whiskerRight αEY Lq₁₂ ≫ Functor.whiskerLeft (EY.mapHomotopyCategory c) αq₁₂ :
        QY ⋙ LEY ⋙ Lq₁₂ ⟶ EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⋙ Q'T))
    (γ₂'' : QY ⋙ Lp₁₂ ⋙ LET ⟶ p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T)
    (hγ₂'' : γ₂'' =
      (Functor.whiskerRight αp₁₂ LET ≫ Functor.whiskerLeft (p₁₂.mapHomotopyCategory c) αET :
        QY ⋙ Lp₁₂ ⋙ LET ⟶ p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T))
    [(Lp₁₂ ⋙ LET).IsLeftDerivedFunctor γ₂'' Wq]
    (hΦ₁₂ : ∀ K, Φ₁₂.app (QY.obj K) ≫ γ₂''.app K = γ₁''.app K ≫
      Q'T.map (X := (EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c).obj K)
        (e₁₂H.app K))
    (cR : Lp₁₂ ≅ Lp ⋙ Lp₁) (γR : p₁₂ ≅ p ⋙ p₁)
    (hcR : ∀ K, cR.inv.app (QY.obj K) ≫ αp₁₂.app K =
      Lp₁.map (αp.app K) ≫ αp₁.app ((p.mapHomotopyCategory c).obj K) ≫
        QT.map (X := ((p ⋙ p₁).mapHomotopyCategory c).obj K)
          ((NatTrans.mapHomotopyCategory γR.inv c).app K))
    (cS : Lq₁₂ ⟶ Lq ⋙ Lq₁) (γS : q₁₂ ⟶ q ⋙ q₁)
    (hcS : ∀ K, cS.app (Q'Y.obj K) ≫ Lq₁.map (αq.app K) ≫
        αq₁.app ((q.mapHomotopyCategory c).obj K) =
      αq₁₂.app K ≫ Q'T.map ((NatTrans.mapHomotopyCategory γS c).app K))
    (e : EY ⋙ q ⟶ p ⋙ EZ) (e₁ : EZ ⋙ q₁ ⟶ p₁ ⋙ ET) (e₁₂ : EY ⋙ q₁₂ ⟶ p₁₂ ⋙ ET)
    (h : ∀ F, e₁₂.app F ≫ ET.map (γR.hom.app F) =
      γS.app (EY.obj F) ≫ q₁.map (e.app F) ≫ e₁.app (p.obj F))
    (heH : ∀ C, eH.app ((HomotopyCategory.quotient VY c).obj C) =
      (HomotopyCategory.quotient WZ c).map ((NatTrans.mapHomologicalComplex e c).app C))
    (he₁H : ∀ C, e₁H.app ((HomotopyCategory.quotient VZ c).obj C) =
      (HomotopyCategory.quotient WT c).map ((NatTrans.mapHomologicalComplex e₁ c).app C))
    (he₁₂H : ∀ C, e₁₂H.app ((HomotopyCategory.quotient VY c).obj C) =
      (HomotopyCategory.quotient WT c).map ((NatTrans.mapHomologicalComplex e₁₂ c).app C))
    (K : DY) :
    Φ₁₂.app K ≫ LET.map (cR.hom.app K) =
      cS.app (LEY.obj K) ≫ Lq₁.map (Φ.app K) ≫ Φ₁.app (Lp.obj K) := by
  subst hγ₁ hγ₂ hγ₁' hγ₂' hγ₁'' hγ₂''
  have he := mapHomotopyCategory_hom_app_comp_aux e e₁ e₁₂ eH e₁H e₁₂H heH he₁H he₁₂H
    γR.hom γS h
  have hδR := mapHomotopyCategory_hom_app_inv_app_aux (c := c) γR
  have key : Φ₁₂ =
      Functor.whiskerLeft _ cS ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight Φ _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ Φ₁ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight cR.inv _ := by
    apply Functor.leftDerived_ext (LF := Lp₁₂ ⋙ LET)
      (α := Functor.whiskerRight αp₁₂ LET ≫
        Functor.whiskerLeft (p₁₂.mapHomotopyCategory c) αET) (W := Wq)
    ext K
    have h₀ := hΦ₁₂ K
    have h₁ := hcR K
    have h₂ := αET.naturality ((NatTrans.mapHomotopyCategory γR.inv c).app K)
    have h₃ := Φ₁.naturality (αp.app K)
    have h₄ := hΦ₁ ((p.mapHomotopyCategory c).obj K)
    have h₅ := hΦ K
    have h₆ := αq₁.naturality (eH.app K)
    have h₇ := cS.naturality (αEY.app K)
    have h₈ := hcS ((EY.mapHomotopyCategory c).obj K)
    have h₉ := he K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc] at h₀ h₄ h₅ ⊢
    simp only [Functor.comp_map, Functor.comp_obj] at h₂ h₆ h₇
    dsimp at h₃
    have h₅' := congrArg Lq₁.map h₅
    simp only [Functor.map_comp] at h₅'
    have hinv : (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR.hom c).app K) ≫
        (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR.inv c).app K) =
          𝟙 _ := by
      rw [← Functor.map_comp, hδR K, CategoryTheory.Functor.map_id]
    simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    rw [h₀, ← LET.map_comp_assoc, h₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [h₂, ← reassoc_of% h₃]
    erw [reassoc_of% h₄]
    rw [reassoc_of% h₅', reassoc_of% h₆, ← reassoc_of% h₇,
      reassoc_of% h₈, ← Q'T.map_comp, ← Q'T.map_comp,
      ← Q'T.map_comp, ← reassoc_of% h₉, hinv, Category.comp_id]
  have := NatTrans.congr_app key K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at this
  rw [this]
  simp [← Functor.map_comp]

end Generic

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section HomotopyCategory

/-- On the image of a complex, `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is induced
by `sheafExtendScalarsCompUpperStarIso` degreewise. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (C : HomologicalComplex (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app
        ((HomotopyCategory.quotient _ _).obj C) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom (.up ℤ)).app C) :=
  -- definitional; a `simp`/`erw` proof makes the kernel unfold the concrete functors
  rfl

/-- `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is compatible with the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭`. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_id (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (𝟙 X)).hom.app K ≫
        ((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (ProEtale.upperStarId (ModuleCat.{u + 1} R) X).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (ProEtale.upperStarId (ModuleCat.{u + 1} S) X).hom
        (.up ℤ)).app
          (((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).obj K) :=
  mapHomotopyCategory_hom_app_id_aux _ _
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S (𝟙 X)) _ _
    (sheafExtendScalarsCompUpperStarIso_hom_app_id (algebraMap R S) X) K

/-- `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is compatible with the composition
isomorphisms `(g₁ ≫ g)^* ≅ g^* ⋙ g₁^*`. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_comp {T Z Y : Scheme.{u}}
    (g₁ : T ⟶ Z) (g : Z ⟶ Y)
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (g₁ ≫ g)).hom.app K ≫
        ((sheafExtendScalars (algebraMap R S) T).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom
          (.up ℤ)).app
            (((sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).obj K) ≫
        ((g₁)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K) ≫
        (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g₁).hom.app
          (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) :=
  mapHomotopyCategory_hom_app_comp_aux _ _ _ _ _ _
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S g)
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S g₁)
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S (g₁ ≫ g)) _ _
    (sheafExtendScalarsCompUpperStarIso_hom_app_comp (algebraMap R S) g₁ g) K

end HomotopyCategory

variable [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the identifications
`L(𝟙 Y)^* ≅ 𝟭`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_id
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Y).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom.app K) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom.app
        (L(sheafExtendScalars (algebraMap R S) Y).obj K) :=
  leftDerived_hom_app_id_aux (HomotopyCategory.quasiIso _ (.up ℤ))
    (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit
    ((𝟙 Y)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit
    ((𝟙 Y)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit
    (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (𝟙 Y)).hom
    (leftDerivedSheafExtendScalarsUpperStarCounit R S (𝟙 Y)) rfl
    (leftDerivedUpperStarSheafExtendScalarsCounit R S (𝟙 Y)) rfl
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S (𝟙 Y))
    (leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom
    (ProEtale.upperStarId (ModuleCat.{u + 1} R) Y).hom
    (leftDerivedUpperStarId_hom_app_Qh (ModuleCat.{u + 1} R) Y)
    (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom
    (ProEtale.upperStarId (ModuleCat.{u + 1} S) Y).hom
    (leftDerivedUpperStarId_hom_app_Qh (ModuleCat.{u + 1} S) Y)
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) (𝟙 Y)).hom
    (sheafExtendScalarsCompUpperStarIso_hom_app_id (algebraMap R S) Y) (fun _ ↦ rfl) K

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_comp {T : Scheme.{u}} (g₁ : T ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (g₁ ≫ g)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) T).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) g₁ g).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        L((g₁)^*[ModuleCat.{u + 1} S]).map
          ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g₁).hom.app
          (L((g)^*[ModuleCat.{u + 1} R]).obj K) :=
  leftDerived_hom_app_comp_aux (HomotopyCategory.quasiIso _ (.up ℤ))
    (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R S) T).leftDerivedFunctorCounit
    ((g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit
    ((g₁)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit
    ((g₁ ≫ g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit
    ((g)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit
    ((g₁)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit
    ((g₁ ≫ g)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit
    (leftDerivedUpperStarExtendScalarsIso R S g).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom
    (leftDerivedSheafExtendScalarsUpperStarCounit R S g) rfl
    (leftDerivedUpperStarSheafExtendScalarsCounit R S g) rfl
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g)
    (leftDerivedUpperStarExtendScalarsIso R S g₁).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g₁).hom
    (leftDerivedSheafExtendScalarsUpperStarCounit R S g₁) rfl
    (leftDerivedUpperStarSheafExtendScalarsCounit R S g₁) rfl
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g₁)
    (leftDerivedUpperStarExtendScalarsIso R S (g₁ ≫ g)).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (g₁ ≫ g)).hom
    (leftDerivedSheafExtendScalarsUpperStarCounit R S (g₁ ≫ g)) rfl
    (leftDerivedUpperStarSheafExtendScalarsCounit R S (g₁ ≫ g)) rfl
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S (g₁ ≫ g))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) g₁ g)
    (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g)
    (leftDerivedUpperStarComp_inv_app_Qh (ModuleCat.{u + 1} R) g₁ g)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom
    (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom
    (leftDerivedUpperStarComp_hom_app_Qh (ModuleCat.{u + 1} S) g₁ g)
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g₁).hom
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) (g₁ ≫ g)).hom
    (sheafExtendScalarsCompUpperStarIso_hom_app_comp (algebraMap R S) g₁ g)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) K

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the transport
`leftDerivedUpperStarCongr` along an equality of morphisms. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_congr {g' : Z ⟶ Y} (h : g = g')
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Z).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} R) h).hom.app K) =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} S) h).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g').hom.app K := by
  subst h
  simp

/-- The inverse form of `leftDerivedUpperStarExtendScalarsIso_hom_app_congr`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_congr_inv {g' : Z ⟶ Y} (h : g = g')
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g').hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Z).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} R) h).inv.app K) =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} S) h).inv.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g).hom.app K := by
  subst h
  simp

end AlgebraicGeometry.ProEtale
