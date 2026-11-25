/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-! # Sectionwise module direct-image and open-restriction pasting

Source: blueprint `proposition-composition-base-change-rf-shriek--1`, Composition isomorphism and
Canonicity and associativity; Stacks Project, proetale.tex, Tag 09A5, section-morphism;
sites.tex, Tag 00XZ, section-localize; sites-modules.tex, Tags 03D3, 03D6, 03DH
(blueprint: lem-sfb-module-direct-image-open-pasting).

The helpers spell out the clauses of this single statement. Cartesian squares may use
any representative of the fibre product, so the two pasting laws have literally matching
vertices. The open-slice coordinates are the distinguished section coprojections of the
specified module adjunctions, including extension along the canonical coefficient map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Families of module open-slice comparisons, on cartesian squares with their actual maps.
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Comparisons :=
  ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (_sq : IsPullback i fU f j),
    lowerStar Λ f ⋙ upperStar Λ j ≅ upperStar Λ i ⋙ lowerStar Λ fU

/-- The specified module inverse image is sheaf inverse image with its action transported
along alpha inverse. This is the existing scalar-extension/comap-inverse isomorphism,
whiskered by the existing internal sheaf inverse image; no coefficient map is chosen.
Source: Stacks 03D3 and 03DH (blueprint: lem-sfb-module-direct-image-open-pasting). -/
noncomputable def inverseImageActionIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar Λ f ≅
      (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
        Mod.comap (inv (condensedPullbackHom Λ f)) :=
  Functor.isoWhiskerLeft
    ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

/-- The distinguished section coprojection for open pullback. It first uses the module
adjunction unit (hence the scalar-extension unit), then restriction along the graph of the
site object. Thus it includes the specified coefficient action, rather than a freely
chosen identification. Source: Stacks 03D3 and 00XZ
(blueprint: lem-sfb-module-direct-image-open-pasting). -/
noncomputable def coprojection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (E : X.ProEt)
    (s : M.X.obj.obj (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E))) :
    ((upperStar Λ j).obj M).X.obj.obj (op E) :=
  ((upperStar Λ j).obj M).X.obj.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial).unit.app E).op
      (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
        (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)) s)

/-- The projection-preserving fibre-product arrow for an open cartesian square. Its
restriction on sections is the comparison required in clause (a).
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
noncomputable def sectionArrow {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y)
    [IsOpenImmersion j] (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (sq : IsPullback i fU f j) (E : U.ProEt) :
    (Scheme.ProEtaleOpenRestriction.objectComposition i).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU).obj E) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.map E.hom fU (E.hom ≫ j) f (𝟙 E.left) i j
      (Category.id_comp _).symm sq.w.symm)
    (pullback.lift_snd _ _ _)

/-- Clause (a), with the canonical open-slice coordinates explicitly normalized. All maps
are module maps for the existing scalar-extension functors. Bijectivity identifies the
open pullback with sheaf inverse image carrying the action transported by alpha inverse.
Source: Stacks 03D3, 03D6, 03DH (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Sectionwise (β : Comparisons Λ) : Prop :=
  (∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (E : X.ProEt), Function.Bijective (coprojection Λ j M E)) ∧
  ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (E : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))),
    ((β f j fU i sq).hom.app M).hom.hom.app (op E)
        (coprojection Λ j ((lowerStar Λ f).obj M) E s) =
      coprojection Λ i M ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU).obj E)
        (M.X.obj.map (sectionArrow f j fU i sq E).op s)

attribute [local irreducible] lowerStarComp
  upperStarComp lowerStarId upperStarId lowerStarCongr upperStarLowerStarAdjunction

/-- The underlying composition map and clause (b), with the associator and geometric
transport written out. The direction is c = lowerStarComp inverse.
Source: Stacks 09A5 (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Composition : Prop :=
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Z.ProEt),
    ((lowerStarComp Λ f g).inv.app M).hom.hom.app (op V) =
      M.X.obj.map ((MorphismProperty.Over.pullbackComp f g).inv.app V).op) ∧
  ∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    (lowerStarComp Λ f (g ≫ h)).inv ≫
        Functor.whiskerLeft (lowerStar Λ f) (lowerStarComp Λ g h).inv ≫
        (Functor.associator (lowerStar Λ f) (lowerStar Λ g) (lowerStar Λ h)).inv =
      (lowerStarCongr Λ (Category.assoc f g h)).inv ≫
        (lowerStarComp Λ (f ≫ g) h).inv ≫
        Functor.whiskerRight (lowerStarComp Λ f g).inv (lowerStar Λ h)

/-- Clause (c): successive open restrictions, with both specified pullback compositors.
Source: Stacks 00XZ and 03DH (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def SuccessiveOpens (β : Comparisons Λ) : Prop :=
  ∀ {S T U SU W SW : Scheme.{u}} (f : S ⟶ T) (j : U ⟶ T) [IsOpenImmersion j]
    (fU : SU ⟶ U) (i : SU ⟶ S) [IsOpenImmersion i] (sq : IsPullback i fU f j)
    (v : W ⟶ U) [IsOpenImmersion v] (fW : SW ⟶ W) (k : SW ⟶ SU)
    [IsOpenImmersion k] (sqW : IsPullback k fW fU v),
    (β f (v ≫ j) fW (k ≫ i) (sqW.paste_horiz sq)).hom =
      Functor.whiskerLeft (lowerStar Λ f) (upperStarComp Λ v j).hom ≫
        (Functor.associator (lowerStar Λ f) (upperStar Λ j) (upperStar Λ v)).inv ≫
        Functor.whiskerRight (β f j fU i sq).hom (upperStar Λ v) ≫
        (Functor.associator (upperStar Λ i) (lowerStar Λ fU) (upperStar Λ v)).hom ≫
        Functor.whiskerLeft (upperStar Λ i) (β fU v fW k sqW).hom ≫
        (Functor.associator (upperStar Λ i) (upperStar Λ k) (lowerStar Λ fW)).inv ≫
        Functor.whiskerRight (upperStarComp Λ k i).inv (lowerStar Λ fW)

/-- Clause (d): mixed composition/open pasting, with its source and target compositors.
Cartesian-square representatives keep all fibre-product identifications explicit.
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def MixedPasting (β : Comparisons Λ) : Prop :=
  ∀ {X Y T U YU XU : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T)
    (j : U ⟶ T) [IsOpenImmersion j] (gU : YU ⟶ U) (jY : YU ⟶ Y)
    [IsOpenImmersion jY] (sqG : IsPullback jY gU g j)
    (fU : XU ⟶ YU) (jX : XU ⟶ X) [IsOpenImmersion jX]
    (sqF : IsPullback jX fU f jY),
    Functor.whiskerRight (lowerStarComp Λ f g).inv (upperStar Λ j) ≫
        (Functor.associator (lowerStar Λ f) (lowerStar Λ g) (upperStar Λ j)).hom ≫
        Functor.whiskerLeft (lowerStar Λ f) (β g j gU jY sqG).hom ≫
        (Functor.associator (lowerStar Λ f) (upperStar Λ jY) (lowerStar Λ gU)).inv ≫
        Functor.whiskerRight (β f jY fU jX sqF).hom (lowerStar Λ gU) ≫
        (Functor.associator (upperStar Λ jX) (lowerStar Λ fU) (lowerStar Λ gU)).hom =
      (β (f ≫ g) j (fU ≫ gU) jX (sqF.paste_vert sqG)).hom ≫
        Functor.whiskerLeft (upperStar Λ jX) (lowerStarComp Λ fU gU).inv

/-- Identity-open, identity-morphism, and composition unit normalizations.
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Units (β : Comparisons Λ) : Prop :=
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (sq : IsPullback (𝟙 X) f f (𝟙 Y)),
    (β f (𝟙 Y) f (𝟙 X) sq).hom ≫
        Functor.whiskerRight (upperStarId Λ X).hom (lowerStar Λ f) ≫
        (Functor.leftUnitor (lowerStar Λ f)).hom =
      Functor.whiskerLeft (lowerStar Λ f) (upperStarId Λ Y).hom ≫
        (Functor.rightUnitor (lowerStar Λ f)).hom) ∧
  (∀ {Y U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (sq : IsPullback j (𝟙 U) (𝟙 Y) j),
    (β (𝟙 Y) j (𝟙 U) j sq).hom ≫
        Functor.whiskerLeft (upperStar Λ j) (lowerStarId Λ U).hom ≫
        (Functor.rightUnitor (upperStar Λ j)).hom =
      Functor.whiskerRight (lowerStarId Λ Y).hom (upperStar Λ j) ≫
        (Functor.leftUnitor (upperStar Λ j)).hom) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStarComp Λ (𝟙 X) f =
      Functor.isoWhiskerRight (lowerStarId Λ X) (lowerStar Λ f) ≪≫
        Functor.leftUnitor (lowerStar Λ f) ≪≫
        (lowerStarCongr Λ (Category.id_comp f)).symm) ∧
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStarComp Λ f (𝟙 Y) =
      Functor.isoWhiskerLeft (lowerStar Λ f) (lowerStarId Λ Y) ≪≫
        Functor.rightUnitor (lowerStar Λ f) ≪≫
        (lowerStarCongr Λ (Category.comp_id f)).symm

/-- The comparisons commute with every differential of every cochain complex. Since the
preceding equations quantify over every module, they also hold in every degree.
Source: blueprint Canonicity and associativity
(blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Degreewise (β : Comparisons Λ) : Prop :=
  (∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j)
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (n m : ℤ),
    (lowerStar Λ f ⋙ upperStar Λ j).map (K.d n m) ≫
        (β f j fU i sq).hom.app (K.X m) =
      (β f j fU i sq).hom.app (K.X n) ≫
        (upperStar Λ i ⋙ lowerStar Λ fU).map (K.d n m)) ∧
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (n m : ℤ),
    (lowerStar Λ (f ≫ g)).map (K.d n m) ≫ (lowerStarComp Λ f g).inv.app (K.X m) =
      (lowerStarComp Λ f g).inv.app (K.X n) ≫
        (lowerStar Λ f ⋙ lowerStar Λ g).map (K.d n m)

omit [IsCommMonObj Λ] in
private theorem composition_laws : Composition Λ := by
  constructor
  · intro X Y Z f g M V
    have e : (Mod.forget (condensedRingObj Λ Z)).mapIso ((lowerStarComp Λ f g).app M) =
        (ProEtale.lowerStarComp Ab.{u + 1} f g).app M.X := by
      apply Iso.ext
      exact lowerStarComp_hom_app_hom Λ f g M
    have hi := congrArg (fun z ↦ z.inv.hom.app (op V)) e
    exact hi.trans (ProEtale.lowerStarComp_inv_app_hom_app Ab.{u + 1} f g M.X (op V))
  · intro X Y Z T f g h
    have e := congrArg Iso.inv (lowerStarComp_assoc Λ f g h)
    simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Category.assoc] using e

private noncomputable def underlyingPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar Λ f ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ ProEtale.upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight (inverseImageActionIso Λ f) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem underlyingPullbackIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((upperStarLowerStarAdjunction Λ f).unit.app M).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map ((underlyingPullbackIso Λ f).hom.app M) =
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X := by
  have h := upperStarLowerStarAdjunction_homEquiv_hom Λ f M
    ((upperStar Λ f).obj M) (𝟙 _)
  rw [Adjunction.homEquiv_id] at h
  simp only [Mod.id_hom'] at h
  erw [Category.comp_id] at h
  have he : Mod.extendUnitHom (condensedPullbackHom Λ f)
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M) ≫
      (underlyingPullbackIso Λ f).hom.app M = 𝟙 _ :=
    extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f _
  rw [h, Category.assoc, ← Functor.map_comp, he]
  change (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
    (ProEtale.lowerStar Ab.{u + 1} f).map
      (𝟙 ((ProEtale.upperStar Ab.{u + 1} f).obj M.X)) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private noncomputable def localizationIso {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : upperStar Λ j ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙
        ProEtale.localizationRestriction Ab.{u + 1} j inferInstance :=
  underlyingPullbackIso Λ j ≪≫ Functor.isoWhiskerLeft _
    (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} j inferInstance)

private theorem localizationIso_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((upperStarLowerStarAdjunction Λ j).unit.app M).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} j).map ((localizationIso Λ j).hom.app M) =
        (ProEtale.localizationRestrictionLowerStarAdjunction
          Ab.{u + 1} j inferInstance).unit.app M.X := by
  dsimp only [localizationIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [Functor.map_comp, ← Category.assoc, underlyingPullbackIso_unit]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _

private theorem section_naturality {C : Type*} [Category C] {F G : C ⥤ Ab.{u + 1}}
    (φ : F ⟶ G) {V W : C} (t : V ⟶ W) (s : F.obj V) :
    φ.app W (F.map t s) = G.map t (φ.app V s) :=
  congrArg (fun z ↦ z s) (φ.naturality t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem coprojection_bijective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (E : X.ProEt) : Function.Bijective (coprojection Λ j M E) := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial
  let d := (localizationIso Λ j).app M
  have he (s) : d.hom.hom.app (op E) (coprojection Λ j M E s) = s := by
    dsimp only [coprojection]
    refine (section_naturality d.hom.hom (a.unit.app E).op
      (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
        (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)) s)).trans ?_
    have hu := congrArg (fun z ↦ z.hom.app (op
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))
      (localizationIso_unit Λ j M)
    change (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app _ ≫
      d.hom.hom.app _) = _ at hu
    have hu' := hu.trans
      (ProEtale.localizationRestrictionLowerStarAdjunction_unit_app_hom_app
        Ab.{u + 1} j inferInstance M.X
        (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))
    have huse := congrArg (fun z ↦ M.X.obj.map
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).map (a.unit.app E)).op
        (z s)) hu'
    refine huse.trans ?_
    change (M.X.obj.map (a.counit.app _).op ≫ M.X.obj.map
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).map (a.unit.app E)).op) s = s
    have ht : (Scheme.ProEtaleOpenRestriction.objectComposition j).map (a.unit.app E) ≫
        a.counit.app ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E) = 𝟙 _ :=
      a.left_triangle_components E
    have hmap := (M.X.obj.map_comp (a.counit.app _).op
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).map (a.unit.app E)).op).symm
    exact (congrArg (fun z ↦ z s) hmap).trans
      ((congrArg (fun z ↦ M.X.obj.map z.op s) ht).trans
        (congrArg (fun z ↦ z s) (M.X.obj.map_id _)))
  have hd := ConcreteCategory.bijective_of_isIso (d.hom.hom.app (op E))
  constructor
  · intro x y h
    exact (he x).symm.trans ((congrArg (fun z ↦ d.hom.hom.app (op E) z) h).trans (he y))
  · intro y
    exact ⟨d.hom.hom.app (op E) y, hd.1 (he _)⟩

private noncomputable abbrev formalism : CompactSupportFormalism where
  obj X := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  category _ := inferInstance
  pb := upperStar Λ
  pbId := upperStarId Λ
  pbComp f g := upperStarComp Λ f g
  pbComp_assoc f g h M := by
    simpa only [upperStarCongr, eqToIso.hom, eqToHom_app] using
      upperStarComp_hom_app_comp_upperStarComp_hom_app Λ f g h M
  pbId_comp f M := by
    change (upperStarComp Λ (𝟙 _) f).hom.app M ≫ _ = _
    rw [upperStarComp_id_left]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.id_comp, Category.assoc]
    change (upperStarCongr Λ (Category.id_comp f)).hom.app M ≫
      (upperStarId Λ _).inv.app ((upperStar Λ f).obj M) ≫
        (upperStarId Λ _).hom.app ((upperStar Λ f).obj M) = _
    rw [Iso.inv_hom_id_app]
    change (upperStarCongr Λ (Category.id_comp f)).hom.app M ≫
      𝟙 ((upperStar Λ f).obj M) = _
    rw [Category.comp_id]
    simp only [upperStarCongr, eqToIso.hom, eqToHom_app]
  pbComp_id f M := by
    change (upperStarComp Λ f (𝟙 _)).hom.app M ≫ _ = _
    rw [upperStarComp_id_right]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.id_comp, Category.assoc]
    change (upperStarCongr Λ (Category.comp_id f)).hom.app M ≫
      (upperStar Λ f).map ((upperStarId Λ _).inv.app M) ≫
        (upperStar Λ f).map ((upperStarId Λ _).hom.app M) = _
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    change (upperStarCongr Λ (Category.comp_id f)).hom.app M ≫
      (upperStar Λ f).map (𝟙 M) = _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    simp only [upperStarCongr, eqToIso.hom, eqToHom_app]
  pf := lowerStar Λ
  adj := upperStarLowerStarAdjunction Λ
  sh j h := haveI := h.out; openImmersionLowerShriek Λ j
  shAdj j h := haveI := h.out; openImmersionLowerShriekUpperStarAdjunction Λ j

private noncomputable def squarePushIso {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) : lowerStar Λ i ⋙ lowerStar Λ f ≅
      lowerStar Λ fU ⋙ lowerStar Λ j :=
  lowerStarComp Λ i f ≪≫ lowerStarCongr Λ w ≪≫ (lowerStarComp Λ fU j).symm

private noncomputable def betaMap {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) : lowerStar Λ f ⋙ upperStar Λ j ⟶
      upperStar Λ i ⋙ lowerStar Λ fU :=
  ((mateEquiv (upperStarLowerStarAdjunction Λ i)
    (upperStarLowerStarAdjunction Λ j)).symm
      (TwoSquare.mk _ _ _ _ (squarePushIso Λ f j fU i w).hom))

private noncomputable def squareSiteIso {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ⋙
        MorphismProperty.Over.pullback @WeaklyEtale ⊤ i ≅
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ j ⋙
        MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU :=
  (MorphismProperty.Over.pullbackComp i f).symm ≪≫
    MorphismProperty.Over.pullbackCongr w ≪≫ MorphismProperty.Over.pullbackComp fU j

omit [IsCommMonObj Λ] in
private theorem squarePushIso_def {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) :
    squarePushIso Λ f j fU i w = lowerStarComp Λ i f ≪≫ lowerStarCongr Λ w ≪≫
      (lowerStarComp Λ fU j).symm := rfl

private theorem iso_symm_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ≅ G) (M : C) : α.symm.app M = (α.app M).symm := rfl

private theorem squareSheafIso_def {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) :
    ProEtale.squareLowerStarIso Ab.{u + 1} (CommSq.mk w.symm) =
      ProEtale.lowerStarComp Ab.{u + 1} i f ≪≫
      ProEtale.lowerStarCongr Ab.{u + 1} w ≪≫
      (ProEtale.lowerStarComp Ab.{u + 1} fU j).symm := rfl

private theorem squareSheafIso_app {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) (M : Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) :
    (ProEtale.squareLowerStarIso Ab.{u + 1} (CommSq.mk w.symm)).app M =
      (ProEtale.lowerStarComp Ab.{u + 1} i f).app M ≪≫
      (ProEtale.lowerStarCongr Ab.{u + 1} w).app M ≪≫
      ((ProEtale.lowerStarComp Ab.{u + 1} fU j).app M).symm := by
  rw [squareSheafIso_def, NatIso.trans_app, NatIso.trans_app, iso_symm_app]

omit [IsCommMonObj Λ] in
private theorem forget_compositor {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)).mapIso ((lowerStarComp Λ f g).app M) =
    (ProEtale.lowerStarComp Ab.{u + 1} f g).app M.X :=
  Iso.ext (lowerStarComp_hom_app_hom Λ f g M)

omit [IsCommMonObj Λ] in
private theorem forget_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)).mapIso ((lowerStarCongr Λ w).app M) =
    (ProEtale.lowerStarCongr Ab.{u + 1} w).app M.X :=
  Iso.ext (lowerStarCongr_hom_app_hom Λ w M)

private theorem forget_square_formula {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : D ⥤ E) {G₁ G₂ G₃ G₄ : C ⥤ D}
    (a : G₁ ≅ G₂) (b : G₂ ≅ G₃) (c : G₄ ≅ G₃)
    (d : G₁ ≅ G₄) (hd : d = a ≪≫ b ≪≫ c.symm) (M : C)
    (a' : F.obj (G₁.obj M) ≅ F.obj (G₂.obj M))
    (b' : F.obj (G₂.obj M) ≅ F.obj (G₃.obj M))
    (c' : F.obj (G₄.obj M) ≅ F.obj (G₃.obj M))
    (ha : F.mapIso (a.app M) = a') (hb : F.mapIso (b.app M) = b')
    (hc : F.mapIso (c.app M) = c') :
    F.map (d.hom.app M) = (a' ≪≫ b' ≪≫ c'.symm).hom := by
  have h : F.mapIso (d.app M) = a' ≪≫ b' ≪≫ c'.symm := by
    rw [hd, NatIso.trans_app, NatIso.trans_app, iso_symm_app,
      Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm, ha, hb, hc]
  exact congrArg Iso.hom h

omit [IsCommMonObj Λ] in
private theorem squarePushIso_hom {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j)
    (M : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P)) :
    ((squarePushIso Λ f j fU i w).hom.app M).hom =
      (ProEtale.squareLowerStarIso Ab.{u + 1} (CommSq.mk w.symm)).hom.app M.X := by
  have h := forget_square_formula
    (Mod.forget (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (lowerStarComp Λ i f) (lowerStarCongr Λ w) (lowerStarComp Λ fU j)
    (squarePushIso Λ f j fU i w) (squarePushIso_def Λ f j fU i w) M
    ((ProEtale.lowerStarComp Ab.{u + 1} i f).app M.X)
    ((ProEtale.lowerStarCongr Ab.{u + 1} w).app M.X)
    ((ProEtale.lowerStarComp Ab.{u + 1} fU j).app M.X)
    (forget_compositor Λ i f M) (forget_congr Λ w M) (forget_compositor Λ fU j M)
  exact h.trans (congrArg Iso.hom (squareSheafIso_app f j fU i w M.X).symm)

private theorem squareSheafIso_section {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) (M : Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
    (V : Y.ProEt) :
    ((ProEtale.squareLowerStarIso Ab.{u + 1} (CommSq.mk w.symm)).hom.app M).hom.app
        (op V) = M.obj.map ((squareSiteIso f j fU i w).inv.app V).op := by
  simp only [ProEtale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    ProEtale.lowerStarComp_hom_app_hom_app, ProEtale.lowerStarComp_inv_app_hom_app,
    ProEtale.lowerStarCongr_hom_app_hom_app]
  simp only [squareSiteIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    op_comp, Functor.map_comp]

omit [IsCommMonObj Λ] in
private theorem squarePushIso_section {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j)
    (M : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P))
    (V : Y.ProEt) :
    ((squarePushIso Λ f j fU i w).hom.app M).hom.hom.app (op V) =
      M.X.obj.map ((squareSiteIso f j fU i w).inv.app V).op := by
  have h := squarePushIso_hom Λ f j fU i w M
  have he := congrArg (fun z ↦ z.hom.app (op V)) h
  refine he.trans ?_
  exact squareSheafIso_section f j fU i w M.X V

private theorem betaMap_def {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) :
    betaMap Λ f j fU i w =
      ((mateEquiv (upperStarLowerStarAdjunction Λ i)
        (upperStarLowerStarAdjunction Λ j)).symm
          (TwoSquare.mk _ _ _ _ (squarePushIso Λ f j fU i w).hom)) := rfl

private theorem mate_unit_formula {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : R₁ ⋙ G ⟶ H ⋙ R₂) (M : C) :
    G.map (a.unit.app M) ≫ α.app (L₁.obj M) =
      b.unit.app (G.obj M) ≫ R₂.map
        (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ α)).app M) :=
  unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ α) M

private theorem betaMap_unit {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStar Λ f).map ((upperStarLowerStarAdjunction Λ i).unit.app M) ≫
      (squarePushIso Λ f j fU i w).hom.app ((upperStar Λ i).obj M) =
    (upperStarLowerStarAdjunction Λ j).unit.app ((lowerStar Λ f).obj M) ≫
      (lowerStar Λ j).map ((betaMap Λ f j fU i w).app M) := by
  rw [betaMap_def]
  exact mate_unit_formula (upperStarLowerStarAdjunction Λ i)
    (upperStarLowerStarAdjunction Λ j) (squarePushIso Λ f j fU i w).hom M

private theorem betaMap_on_unit {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Y.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V))) :
    ((betaMap Λ f j fU i w).app M).hom.hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V))
      (((upperStarLowerStarAdjunction Λ j).unit.app
        ((lowerStar Λ f).obj M)).hom.hom.app (op V) s) =
    ((upperStar Λ i).obj M).X.obj.map ((squareSiteIso f j fU i w).inv.app V).op
      (((upperStarLowerStarAdjunction Λ i).unit.app M).hom.hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)) s) := by
  have h := betaMap_unit Λ f j fU i w M
  have he := congrArg (fun z ↦ z.hom.hom.app (op V) s) h
  simp only [Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, lowerStar_map_hom, ProEtale.lowerStar_map_hom_app',
    squarePushIso_section] at he
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem betaMap_section {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (sq : IsPullback i fU f j)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (E : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))) :
    ((betaMap Λ f j fU i sq.w).app M).hom.hom.app (op E)
        (coprojection Λ j ((lowerStar Λ f).obj M) E s) =
      coprojection Λ i M ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU).obj E)
        (M.X.obj.map (sectionArrow f j fU i sq E).op s) := by
  let V := (Scheme.ProEtaleOpenRestriction.objectComposition j).obj E
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial
  let b := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ i inferInstance trivial
  let K := MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ i
  have hk : K.map (a.unit.app E) ≫ (squareSiteIso f j fU i sq.w).inv.app V =
      b.unit.app (K.obj E) ≫ G.map (sectionArrow f j fU i sq E) := by
    apply MorphismProperty.Over.Hom.ext
    change (K.map (a.unit.app E)).left ≫
      ((squareSiteIso f j fU i sq.w).inv.app V).left =
        (b.unit.app (K.obj E)).left ≫ (G.map (sectionArrow f j fU i sq E)).left
    simp only [squareSiteIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    dsimp [a, b, K, G, V, sectionArrow,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
      MorphismProperty.Over.isoMk, MorphismProperty.Comma.isoMk,
      MorphismProperty.Comma.homFromCommaOfIsIso, MorphismProperty.Over.pullback,
      Scheme.ProEtaleOpenRestriction.objectComposition, MorphismProperty.Over.map,
      MorphismProperty.Comma.Hom.comp, MorphismProperty.Comma.mapRight,
      MorphismProperty.Over.mk, MorphismProperty.Comma.isoFromComma,
      MorphismProperty.Over.homMk, Comma.isoMk]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [Category.assoc]
    · simp [Category.assoc]
  dsimp only [coprojection]
  refine (section_naturality ((betaMap Λ f j fU i sq.w).app M).hom.hom
    (a.unit.app E).op
    (((upperStarLowerStarAdjunction Λ j).unit.app _).hom.hom.app _ s)).trans ?_
  change ((upperStar Λ i).obj M).X.obj.map (K.map (a.unit.app E)).op
    (((betaMap Λ f j fU i sq.w).app M).hom.hom.app _
      (((upperStarLowerStarAdjunction Λ j).unit.app _).hom.hom.app _ s)) = _
  have hu := betaMap_on_unit Λ f j fU i sq.w M V s
  exact (congrArg (fun z ↦ ((upperStar Λ i).obj M).X.obj.map
    (K.map (a.unit.app E)).op z) hu).trans (by
    let F := ((upperStar Λ i).obj M).X.obj
    let t := ((upperStarLowerStarAdjunction Λ i).unit.app M).hom.hom.app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)) s
    have hmap := (F.map_comp ((squareSiteIso f j fU i sq.w).inv.app V).op
      (K.map (a.unit.app E)).op).symm
    refine (congrArg (fun z ↦ z t) hmap).trans ?_
    have heq := congrArg (fun z ↦ F.map z.op t) hk
    refine heq.trans ?_
    have hmap' := F.map_comp (G.map (sectionArrow f j fU i sq E)).op
      (b.unit.app (K.obj E)).op
    refine (congrArg (fun z ↦ z t) hmap').trans ?_
    apply congrArg (fun z ↦ F.map (b.unit.app (K.obj E)).op z)
    exact (section_naturality
      ((upperStarLowerStarAdjunction Λ i).unit.app M).hom.hom
      (sectionArrow f j fU i sq E).op s).symm)

private theorem sectionArrow_isIso {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (sq : IsPullback i fU f j) (E : U.ProEt) :
    IsIso (sectionArrow f j fU i sq E) := by
  have h := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale i) sq.flip
  have he : sectionArrow f j fU i sq E =
      (MorphismProperty.Over.pullbackMapComparison
        (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale i)
        sq.flip.toCommSq).app E := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.map E.hom fU (E.hom ≫ j) f (𝟙 E.left) i j
        (Category.id_comp _).symm sq.w.symm =
      pullback.lift (f := E.hom ≫ j) (g := f) (pullback.fst E.hom fU)
        (pullback.snd E.hom fU ≫ i) _
    apply pullback.hom_ext <;> simp [pullback.map]
  rw [he]
  infer_instance

private theorem betaMap_isIso {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (sq : IsPullback i fU f j) : IsIso (betaMap Λ f j fU i sq.w) := by
  have h (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) : IsIso ((betaMap Λ f j fU i sq.w).app M) := by
    suffices hp : ∀ E : U.ProEtᵒᵖ,
        IsIso (((betaMap Λ f j fU i sq.w).app M).hom.hom.app E) by
      have : IsIso ((betaMap Λ f j fU i sq.w).app M).hom.hom :=
        NatIso.isIso_of_isIso_app _
      have : IsIso ((sheafToPresheaf _ _).map
          ((betaMap Λ f j fU i sq.w).app M).hom) := ‹IsIso _›
      have : IsIso ((betaMap Λ f j fU i sq.w).app M).hom :=
        isIso_of_reflects_iso _ (sheafToPresheaf _ _)
      have : IsIso ((Mod.forget (condensedRingObj Λ U)).map
          ((betaMap Λ f j fU i sq.w).app M)) := ‹IsIso _›
      exact isIso_of_reflects_iso _ (Mod.forget (condensedRingObj Λ U))
    intro E
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hi := sectionArrow_isIso f j fU i sq E.unop
    have hs := ConcreteCategory.bijective_of_isIso
      (M.X.obj.map (sectionArrow f j fU i sq E.unop).op)
    have hg := coprojection_bijective Λ i M
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU).obj E.unop)
    have hh := coprojection_bijective Λ j ((lowerStar Λ f).obj M) E.unop
    have hb : Function.Bijective (fun s ↦
        ((betaMap Λ f j fU i sq.w).app M).hom.hom.app E
          (coprojection Λ j ((lowerStar Λ f).obj M) E.unop s)) := by
      change Function.Bijective (fun s ↦
        ((betaMap Λ f j fU i sq.w).app M).hom.hom.app (op E.unop)
          (coprojection Λ j ((lowerStar Λ f).obj M) E.unop s))
      simp_rw [betaMap_section Λ f j fU i sq]
      exact hg.comp hs
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hh.2 x
      obtain ⟨b, rfl⟩ := hh.2 y
      exact congrArg _ (hb.1 hxy)
    · intro y
      obtain ⟨a, ha⟩ := hb.2 y
      exact ⟨_, ha⟩
  exact NatIso.isIso_of_isIso_app _

private theorem formalism_sqIso {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) :
    (formalism Λ).sqIso i fU f j w =
      (upperStarComp Λ i f).symm ≪≫ upperStarCongr Λ w ≪≫
        upperStarComp Λ fU j := by
  dsimp only [ExchangeFormalism.sqIso]
  rw [ExchangeFormalism.pbComp'_rfl]
  rfl

private theorem betaMap_formalism {X Y U P : Scheme.{u}}
    (f : X ⟶ Y) (j : U ⟶ Y) (fU : P ⟶ U) (i : P ⟶ X)
    (w : i ≫ f = fU ≫ j) : betaMap Λ f j fU i w =
      ((formalism Λ).pfBaseChange i fU f j w) := by
  have h : mateEquiv (upperStarLowerStarAdjunction Λ i)
      (upperStarLowerStarAdjunction Λ j)
      ((formalism Λ).pfBaseChange i fU f j w) =
        TwoSquare.mk _ _ _ _ (squarePushIso Λ f j fU i w).hom := by
    change (mateEquiv (upperStarLowerStarAdjunction Λ i)
      (upperStarLowerStarAdjunction Λ j)
      (mateEquiv (upperStarLowerStarAdjunction Λ f)
        (upperStarLowerStarAdjunction Λ fU)
        ((formalism Λ).sqIso i fU f j w).inv)) = _
    rw [iterated_mateEquiv_conjugateEquiv]
    rw [formalism_sqIso]
    change (conjugateIsoEquiv
      ((upperStarLowerStarAdjunction Λ f).comp (upperStarLowerStarAdjunction Λ i))
      ((upperStarLowerStarAdjunction Λ j).comp (upperStarLowerStarAdjunction Λ fU))
      (((upperStarComp Λ i f).symm ≪≫ upperStarCongr Λ w ≪≫
        upperStarComp Λ fU j).symm)).hom = _
    simp only [Iso.trans_symm, Iso.symm_symm_eq]
    rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ (i ≫ f)) _,
      conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Λ (fU ≫ j)) _,
      conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_iso_symm,
      conjugateIsoEquiv_upperStarCongr, Iso.symm_symm_eq,
      conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarComp]
    rfl
  exact
    (((mateEquiv (upperStarLowerStarAdjunction Λ i)
      (upperStarLowerStarAdjunction Λ j)).symm_apply_eq).mpr h.symm)

private theorem formalism_pfComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (formalism Λ).pfComp' f g (f ≫ g) rfl = (lowerStarComp Λ f g).symm := by
  dsimp only [ExchangeFormalism.pfComp']
  rw [ExchangeFormalism.pbComp'_rfl]
  change conjugateIsoEquiv (upperStarLowerStarAdjunction Λ (f ≫ g))
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarComp Λ f g).symm = _
  rw [conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarComp]

private theorem successive_laws (β : Comparisons Λ)
    (hb : ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
      (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j),
      (β f j fU i sq).hom = betaMap Λ f j fU i sq.w) : SuccessiveOpens Λ β := by
  intro S T U SU W SW f j _ fU i _ sq v _ fW k _ sqW
  simp only [hb, betaMap_formalism]
  have h := ((formalism Λ).pfBaseChange_paste_horiz
    k i fW fU f v j (k ≫ i) (v ≫ j) sqW.w sq.w rfl rfl
    (sqW.paste_horiz sq).w)
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, ExchangeFormalism.pbComp'_rfl, formalism,
    Category.assoc] using h

private theorem pfBaseChange_vertical_normalized (F : CompactSupportFormalism)
    {X Y T U YU XU : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T)
    (j : U ⟶ T) (gU : YU ⟶ U) (jY : YU ⟶ Y)
    (fU : XU ⟶ YU) (jX : XU ⟶ X)
    (wF : jX ≫ f = fU ≫ jY) (wG : jY ≫ g = gU ≫ j)
    (w : jX ≫ (f ≫ g) = (fU ≫ gU) ≫ j) :
    Functor.whiskerRight (F.pfComp' f g (f ≫ g) rfl).hom (F.pb j) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.pf f) (F.pfBaseChange jY gU g j wG) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (F.pfBaseChange jX fU f jY wF) (F.pf gU) ≫
      (Functor.associator _ _ _).hom =
    (F.pfBaseChange jX (fU ≫ gU) (f ≫ g) j w) ≫
      Functor.whiskerLeft (F.pb jX) (F.pfComp' fU gU (fU ≫ gU) rfl).hom := by
  rw [F.pfBaseChange_paste_vert jX jY j fU f gU g (fU ≫ gU) (f ≫ g)
    wF wG rfl rfl w]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.comp_id]

private theorem mixed_laws (β : Comparisons Λ)
    (hb : ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
      (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j),
      (β f j fU i sq).hom = betaMap Λ f j fU i sq.w) : MixedPasting Λ β := by
  intro X Y T U YU XU f g j _ gU jY _ sqG fU jX _ sqF
  simp only [hb, betaMap_formalism]
  simpa only [formalism_pfComp, Iso.symm_hom] using
    pfBaseChange_vertical_normalized (formalism Λ) f g j gU jY fU jX sqF.w sqG.w
      (sqF.paste_vert sqG).w

private theorem pfBaseChange_identity_vertical (F : CompactSupportFormalism)
    {X Y : Scheme.{u}} (j : X ⟶ Y) (w : j ≫ 𝟙 Y = 𝟙 X ≫ j) :
    F.pfBaseChange j (𝟙 X) (𝟙 Y) j w =
      ((TwoSquare.mk (𝟭 _) (F.pb j) (F.pb j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.pfId Y).hom).whiskerBottom (F.pfId X).inv := by
  have key : (F.sqIso j (𝟙 X) (𝟙 Y) j w).inv =
      ((TwoSquare.mk (F.pb j) (𝟭 _) (𝟭 _) (F.pb j)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerLeft
          (F.pbId Y).inv).whiskerRight (F.pbId X).hom := by
    apply Iso.inv_ext
    rw [F.sqIso_id_vert_hom]
    apply NatTrans.ext
    funext M
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
      Category.id_comp, Category.assoc, NatTrans.id_app,
      Functor.comp_obj, Functor.id_obj]
    rw [Iso.inv_hom_id_app_assoc]
    change (F.pb j).map ((F.pbId Y).hom.app M) ≫
      (F.pb j).map ((F.pbId Y).inv.app M) = 𝟙 _
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact (F.pb j).map_id _
  rw [ExchangeFormalism.pfBaseChange, key,
    mateEquiv_conjugateEquiv_vcomp _ Adjunction.id,
    conjugateEquiv_mateEquiv_vcomp _ Adjunction.id, mateEquiv_id_id_unitors]
  rfl

private theorem pfBaseChange_identity_horizontal_normalized (F : CompactSupportFormalism)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : 𝟙 X ≫ f = f ≫ 𝟙 Y) :
    (F.pfBaseChange (𝟙 X) f f (𝟙 Y) w) ≫
      Functor.whiskerRight (F.pbId X).hom (F.pf f) ≫ (Functor.leftUnitor _).hom =
    Functor.whiskerLeft (F.pf f) (F.pbId Y).hom ≫ (Functor.rightUnitor _).hom := by
  rw [F.pfBaseChange_id_horiz]
  apply NatTrans.ext
  funext M
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
    Category.comp_id, Category.assoc, Functor.comp_obj, Functor.id_obj]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  change (F.pbId Y).hom.app ((F.pf f).obj M) ≫ (F.pf f).map (𝟙 M) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private theorem pfBaseChange_identity_vertical_normalized (F : CompactSupportFormalism)
    {X Y : Scheme.{u}} (j : X ⟶ Y) (w : j ≫ 𝟙 Y = 𝟙 X ≫ j) :
    (F.pfBaseChange j (𝟙 X) (𝟙 Y) j w) ≫
      Functor.whiskerLeft (F.pb j) (F.pfId X).hom ≫ (Functor.rightUnitor _).hom =
    Functor.whiskerRight (F.pfId Y).hom (F.pb j) ≫ (Functor.leftUnitor _).hom := by
  rw [pfBaseChange_identity_vertical]
  apply NatTrans.ext
  funext M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.comp_obj, Functor.id_obj]
  rw [Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem formalism_pfId (X : Scheme.{u}) :
    (formalism Λ).pfId X = lowerStarId Λ X := by
  change conjugateIsoEquiv (upperStarLowerStarAdjunction Λ (𝟙 X))
    Adjunction.id (upperStarId Λ X).symm = _
  rw [conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId, Iso.symm_symm_eq]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem units_laws (β : Comparisons Λ)
    (hb : ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
      (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j),
      (β f j fU i sq).hom = betaMap Λ f j fU i sq.w) : Units Λ β := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f sq
    rw [hb, betaMap_formalism]
    exact pfBaseChange_identity_horizontal_normalized (formalism Λ) f sq.w
  · intro Y U j _ sq
    rw [hb, betaMap_formalism]
    simpa only [formalism_pfId] using
      pfBaseChange_identity_vertical_normalized (formalism Λ) j sq.w
  · exact fun f ↦ lowerStarComp_id_left Λ f
  · exact fun f ↦ lowerStarComp_id_right Λ f

private theorem degreewise_laws (β : Comparisons Λ) : Degreewise Λ β := by
  constructor
  · intro X Y U P f j _ fU i _ sq K n m
    exact (β f j fU i sq).hom.naturality (K.d n m)
  · intro X Y Z f g K n m
    exact (lowerStarComp Λ f g).inv.naturality (K.d n m)

/-- The sectionwise pasting comparisons are the specified pullback-square mates.
Source: Stacks 09A5 and the conjugacy of the module compositors
(blueprint: lem-sfb-module-direct-image-open-pasting).

The construction in `moduleDirectImageOpenPasting` uses `betaMap`. Its iterated mate
is the conjugate of the inverse pullback compositor, by `betaMap_formalism`.
Thus the same witnesses satisfy both the section formulas and this mate equation. -/
theorem moduleDirectImageOpenPasting_canonical :
    ∃ β : Comparisons Λ, Sectionwise Λ β ∧ Composition Λ ∧ SuccessiveOpens Λ β ∧
      MixedPasting Λ β ∧ Units Λ β ∧ Degreewise Λ β ∧
      ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
        (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j),
        (β f j fU i sq).hom =
          (mateEquiv (upperStarLowerStarAdjunction Λ f)
            (upperStarLowerStarAdjunction Λ fU)
            (TwoSquare.mk _ _ _ _
              (((upperStarComp Λ i f).symm ≪≫ upperStarCongr Λ sq.w ≪≫
                upperStarComp Λ fU j).inv))) := by
  let β : Comparisons Λ := fun f j _ fU i _ sq ↦
    @asIso _ _ _ _ (betaMap Λ f j fU i sq.w) (betaMap_isIso Λ f j fU i sq)
  have hb : ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
      (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j),
      (β f j fU i sq).hom = betaMap Λ f j fU i sq.w := by
    intros
    rfl
  refine ⟨β, ⟨?_, ?_⟩, composition_laws Λ, successive_laws Λ β hb,
    mixed_laws Λ β hb, units_laws Λ β hb, degreewise_laws Λ β, ?_⟩
  · exact fun j _ M E ↦ coprojection_bijective Λ j M E
  · intro X Y U P f j _ fU i _ sq M E s
    exact betaMap_section Λ f j fU i sq M E s
  · intro X Y U P f j _ fU i _ sq
    rw [hb f j fU i sq]
    have he := congrArg (fun e ↦ e.inv) (formalism_sqIso Λ f j fU i sq.w)
    exact (betaMap_formalism Λ f j fU i sq.w).trans
      (congrArg (fun t : upperStar Λ j ⋙ upperStar Λ fU ⟶
          upperStar Λ f ⋙ upperStar Λ i ↦
        (mateEquiv (upperStarLowerStarAdjunction Λ f)
          (upperStarLowerStarAdjunction Λ fU) (TwoSquare.mk _ _ _ _ t))) he)

end AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting
