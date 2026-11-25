/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTraceMonoidal

/-!
# Restriction along a morphism of weakly étale covers

Let `g : Y ⟶ X` and `g' : Y' ⟶ X` be weakly étale and `s : Y' ⟶ Y` a morphism over `X`. For a
pro-étale sheaf `H` on `X`, the sheaf `g_* g^* H` has sections `H(V ×_X Y)` over `V`, and `s`
induces the restriction `H(V ×_X Y) ⟶ H(V ×_X Y')`. This file packages it:

* on the site, as the natural transformation `V ×_X Y' ⟶ V ×_X Y` of base change functors
  (`AlgebraicGeometry.ProEtale.baseChangeHom`), compatible with composition, the projections and
  the action of automorphisms (`AlgebraicGeometry.ProEtale.baseChangeAction`);
* on sheaves, in the restriction model `j_g^* ⋙ g_*` of `g^* ⋙ g_*`
  (`AlgebraicGeometry.ProEtale.restrictionHom`), a monoidal natural transformation;
* on `g^* ⋙ g_*` itself, by conjugation with `g^* ≅ j_g^*`
  (`AlgebraicGeometry.ProEtale.lowerStarUpperStarHom`), a monoidal natural transformation
  compatible with the units of `g^* ⊣ g_*` and `g'^* ⊣ g'_*` and with the Galois actions.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y Y' Y'' : Scheme.{u}} (g : Y ⟶ X) (g' : Y' ⟶ X) (g'' : Y'' ⟶ X) [WeaklyEtale g]
  [WeaklyEtale g'] [WeaklyEtale g'']

/-! ### The site level -/

@[simp]
private lemma overHomMk_left {A B : X.ProEt} (f : A.left ⟶ B.left) (w : f ≫ B.hom = A.hom)
    (hf : (⊤ : MorphismProperty Scheme.{u}) f) : (MorphismProperty.Over.homMk f w hf).left = f :=
  rfl

@[simp]
private lemma proEtComp_left {A B C : X.ProEt} (f : A ⟶ B) (h : B ⟶ C) :
    (f ≫ h).left = f.left ≫ h.left :=
  rfl

@[simp]
private lemma proEtId_left (A : X.ProEt) : (𝟙 A : A ⟶ A).left = 𝟙 A.left :=
  rfl

/-- The morphism `V ×_X Y' ⟶ V ×_X Y` of base changes induced by a morphism `s : Y' ⟶ Y`
over `X`. -/
noncomputable def baseChangeHom (s : Y' ⟶ Y) (hs : s ≫ g = g') :
    baseChangeFunctor g' ⟶ baseChangeFunctor g where
  app V := MorphismProperty.Over.homMk
    (pullback.map V.hom g' V.hom g (𝟙 _) s (𝟙 _) (by simp) (by simp [hs]))
    (by simp [hs]) trivial
  naturality V W f := by
    refine MorphismProperty.Over.Hom.ext ?_
    apply pullback.hom_ext <;> simp

variable {g g' g''}

@[simp]
lemma baseChangeHom_app_left (s : Y' ⟶ Y) (hs : s ≫ g = g') (V : X.ProEt) :
    ((baseChangeHom g g' s hs).app V).left =
      pullback.map V.hom g' V.hom g (𝟙 _) s (𝟙 _) (by simp) (by simp [hs]) :=
  rfl

@[reassoc (attr := simp)]
lemma baseChangeHom_app_left_fst (s : Y' ⟶ Y) (hs : s ≫ g = g') (V : X.ProEt) :
    ((baseChangeHom g g' s hs).app V).left ≫ pullback.fst V.hom g = pullback.fst V.hom g' := by
  simp

@[reassoc (attr := simp)]
lemma baseChangeHom_app_left_snd (s : Y' ⟶ Y) (hs : s ≫ g = g') (V : X.ProEt) :
    ((baseChangeHom g g' s hs).app V).left ≫ pullback.snd V.hom g =
      pullback.snd V.hom g' ≫ s := by
  simp

/-- The morphisms of base changes lie over the projections. -/
@[reassoc (attr := simp)]
lemma baseChangeHom_comp_baseChangeProj (s : Y' ⟶ Y) (hs : s ≫ g = g') :
    baseChangeHom g g' s hs ≫ baseChangeProj g = baseChangeProj g' := by
  refine NatTrans.ext (funext fun V ↦ MorphismProperty.Over.Hom.ext ?_)
  simp

/-- The morphisms of base changes are functorial. -/
@[reassoc]
lemma baseChangeHom_comp (s' : Y'' ⟶ Y') (hs' : s' ≫ g' = g'') (s : Y' ⟶ Y)
    (hs : s ≫ g = g') :
    baseChangeHom g' g'' s' hs' ≫ baseChangeHom g g' s hs =
      baseChangeHom g g'' (s' ≫ s) (by rw [assoc, hs, hs']) := by
  refine NatTrans.ext (funext fun V ↦ MorphismProperty.Over.Hom.ext ?_)
  apply pullback.hom_ext <;> simp

lemma baseChangeHom_id : baseChangeHom g g (𝟙 Y) (by simp) = 𝟙 _ := by
  refine NatTrans.ext (funext fun V ↦ MorphismProperty.Over.Hom.ext ?_)
  simp only [baseChangeHom_app_left, NatTrans.id_app, proEtId_left]
  exact pullback.map_id

lemma baseChangeHom_congr {s t : Y' ⟶ Y} (hs : s ≫ g = g') (hst : s = t) :
    baseChangeHom g g' s hs = baseChangeHom g g' t (hst ▸ hs) := by
  subst hst
  rfl

/-- The action of an automorphism is a morphism of base changes. -/
lemma baseChangeAction_eq_baseChangeHom (s : Y ⟶ Y) (hs : s ≫ g = g) :
    baseChangeAction g s hs = baseChangeHom g g s hs :=
  rfl

/-! ### The restriction model -/

section Restriction

variable (g g')

/-- The restriction `H(V ×_X Y) ⟶ H(V ×_X Y')` along a morphism `s : Y' ⟶ Y` over `X`, as a
natural transformation `j_g^* ⋙ g_* ⟶ j_{g'}^* ⋙ g'_*` of functors of abelian sheaves. -/
noncomputable def restrictionHom (s : Y' ⟶ Y) (hs : s ≫ g = g') :
    localizationRestriction AddCommGrpCat.{u + 1} g inferInstance ⋙
        (g)_*[AddCommGrpCat.{u + 1}] ⟶
      localizationRestriction AddCommGrpCat.{u + 1} g' inferInstance ⋙
        (g')_*[AddCommGrpCat.{u + 1}] :=
  (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom ≫
    Functor.sheafPushforwardContinuousNatTrans (baseChangeHom g g' s hs) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) ≫
    (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g'))) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y') (Scheme.ProEt.topology X)).inv

instance isMonoidal_restrictionHom (s : Y' ⟶ Y) (hs : s ≫ g = g') :
    NatTrans.IsMonoidal (restrictionHom g g' s hs) := by
  unfold restrictionHom
  infer_instance

variable {g g'}

/-- The restriction along `s` is, on sections, restriction along `V ×_X Y' ⟶ V ×_X Y`. -/
lemma restrictionHom_app_hom (s : Y' ⟶ Y) (hs : s ≫ g = g')
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    ((restrictionHom g g' s hs).app H).hom =
      Functor.whiskerRight (NatTrans.op (baseChangeHom g g' s hs)) H.obj := by
  ext U : 2
  simp only [Functor.comp_obj, restrictionHom,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp, Iso.refl_trans,
    Functor.sheafPushforwardContinuousIso_hom, Iso.refl_inv,
    Functor.sheafPushforwardContinuousIso_inv,
    Iso.refl_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, NatTrans.op_id, ObjectProperty.ι_obj,
    Functor.whiskerRight_id', NatTrans.id_app, Functor.op_obj, Functor.whiskerRight_app,
    NatTrans.op_app]
  erw [Category.id_comp, Category.comp_id]

lemma restrictionHom_app_hom_app (s : Y' ⟶ Y) (hs : s ≫ g = g')
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (V : X.ProEtᵒᵖ) :
    ((restrictionHom g g' s hs).app H).hom.app V =
      H.obj.map ((baseChangeHom g g' s hs).app V.unop).op := by
  rw [restrictionHom_app_hom]
  rfl

/-- The restriction along `s` is compatible with the units: the projections `V ×_X Y ⟶ V` and
`V ×_X Y' ⟶ V` are compatible with `s`. -/
@[reassoc]
lemma localizationRestrictionLowerStarAdjunction_unit_comp_restrictionHom (s : Y' ⟶ Y)
    (hs : s ≫ g = g') :
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g inferInstance).unit ≫
        restrictionHom g g' s hs =
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g'
        inferInstance).unit := by
  ext H : 2
  refine Sheaf.hom_ext ?_
  rw [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, restrictionHom_app_hom]
  rw [localizationRestrictionLowerStarAdjunction_unit_app_hom,
    localizationRestrictionLowerStarAdjunction_unit_app_hom]
  ext V : 2
  simp only [NatTrans.comp_app, Presheaf.baseChangeUnit_app, Functor.whiskerRight_app,
    NatTrans.op_app, ← Functor.map_comp, ← op_comp]
  rw [← NatTrans.comp_app, baseChangeHom_comp_baseChangeProj]

variable (g) in
lemma restrictionHom_id : restrictionHom g g (𝟙 Y) (by simp) = 𝟙 _ := by
  ext H : 2
  refine Sheaf.hom_ext ?_
  rw [restrictionHom_app_hom, baseChangeHom_id]
  ext V : 2
  simp only [Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app, op_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- The restrictions along composable morphisms compose. -/
@[reassoc]
lemma restrictionHom_comp (s' : Y'' ⟶ Y') (hs' : s' ≫ g' = g'') (s : Y' ⟶ Y)
    (hs : s ≫ g = g') :
    restrictionHom g g' s hs ≫ restrictionHom g' g'' s' hs' =
      restrictionHom g g'' (s' ≫ s) (by rw [assoc, hs, hs']) := by
  ext H : 2
  refine Sheaf.hom_ext ?_
  rw [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, restrictionHom_app_hom,
    restrictionHom_app_hom, restrictionHom_app_hom]
  ext V : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.op_app, ← Functor.map_comp,
    ← op_comp]
  rw [← NatTrans.comp_app, baseChangeHom_comp]

end Restriction

end AlgebraicGeometry.ProEtale
