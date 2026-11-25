/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Scalar compatibility of literal open restriction

Source: Stacks Project, Tags 03D3, 03CY and 03DI.
(blueprint: lem-weil-compact-support-open-restriction-scalar).

The comparisons below involve one coefficient homomorphism and one open immersion.
There is no coefficient sequence or extension-by-zero evaluation in the statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf presheafToSheaf
namespace WeilConjectures
variable {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The section-normalized scalar square for the native direct image.
Source: Stacks Tag 03D3 (blueprint: lem-weil-compact-support-open-restriction-scalar). -/
def compactSupportScalarDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B) :
    ProEtale.StrictTower.moduleDirectImage (ULift.{u + 1, u} B) f ⋙
        proEtaleCoefficientRestrictScalars Y φ ≅
      proEtaleCoefficientRestrictScalars X φ ⋙
        ProEtale.StrictTower.moduleDirectImage (ULift.{u + 1, u} A) f :=
  Functor.isoWhiskerRight (compactSupportDirectModel f B) _ ≪≫
    proEtaleCoefficientDirectImageComparison f φ ≪≫
      Functor.isoWhiskerLeft _ (compactSupportDirectModel f A).symm

private theorem compactSupportScalarDirectImage_sections {X Y : Scheme.{u}}
    (f : X ⟶ Y) (φ : A →+* B)
    (N : ProEtale.StrictTower.Modules (ULift.{u + 1, u} B) X) (V : Y.ProEtᵒᵖ)
    (x : N.val.obj ((proEtaleBaseChange f).op.obj V)) :
    ((compactSupportScalarDirectImage f φ).hom.app N).val.app V x = x := by
  change ((proEtaleCoefficientDirectImageComparison f φ).hom.app N).val.app V x = x
  exact (proEtaleCoefficientDirectImageComparison_existsUnique f φ).choose_spec.1 N V x

/-- The inverse mate of the normalized direct-image coefficient square.
Source: Stacks Tag 03D3 (blueprint: lem-weil-compact-support-open-restriction-scalar). -/
def compactSupportScalarPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars Y φ ⋙
        ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} A) f ⟶
      ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} B) f ⋙
        proEtaleCoefficientRestrictScalars X φ :=
  ((mateEquiv (proEtaleConstantRingAdjunction B f)
    (proEtaleConstantRingAdjunction A f)).symm (compactSupportScalarDirectImage f φ).hom)

private theorem compactSupportScalarPullback_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B) :
    IsIso (compactSupportScalarPullback f φ) := by
  let aY := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom φ.ulift.{u + 1, u + 1})
  let aX := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom φ.ulift.{u + 1, u + 1})
  let comm := coefficientInverseImage_naturality f φ
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B) comm
  have hd : compactSupportScalarDirectImage f φ = d := by
    apply (proEtaleRingRestrictionDirectImage_existsUnique f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B) comm).unique
    · exact compactSupportScalarDirectImage_sections f φ
    · exact (proEtaleRingRestrictionDirectImage_existsUnique f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        comm).choose_spec.1
  have he : compactSupportScalarPullback f φ = proEtaleRingRestrictionPullbackInv f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B) aY aX
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B) comm := by
    apply (mateEquiv (proEtaleConstantRingAdjunction B f)
      (proEtaleConstantRingAdjunction A f)).injective
    change (mateEquiv _ _ ((mateEquiv _ _).symm (compactSupportScalarDirectImage f φ).hom)) = _
    exact (Equiv.apply_symm_apply _ _).trans
      ((congrArg (fun e ↦ TwoSquare.mk _ _ _ _ e.hom) hd).trans
        (congrArg (fun t ↦ TwoSquare.mk _ _ _ _ t)
          (restrictionPullback_mate f _ _ _ _ aY aX _ _ comm)).symm)
  exact (congrArg (fun t ↦ IsIso t) he).mpr
    (proEtaleRingRestrictionPullbackInv_isIso f _ _ _ _ aY aX _ _ comm)

private def upperModel (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    sfIntrinsicPullback A j ≅ sfIntrinsicOpenRestriction j A :=
  sfIntrinsicTransportIso A (ProEtale.upperStarIsoOpenImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)

/-- Tensor inverse image identified with literal restriction to an open.
Source: Stacks Tag 03CY (blueprint: lem-weil-compact-support-open-restriction-scalar). -/
def compactSupportOpenRestrictionModel (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} A) j ≅
      sfIntrinsicOpenRestriction j A :=
  openSquarePullbackModel A j ≪≫
    sfIntrinsicTransportIso A (ProEtale.upperStarIsoOpenImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)

attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction

private theorem normalizedTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J J' : A ⥤ B} {G K : B ⥤ A} (a : J ⊣ G) (a' : J' ⊣ K)
    {H H' : C ⥤ D} {I L : D ⥤ C} (b : H ⊣ I) (b' : H' ⊣ L)
    (x : J ≅ J') (y : H ≅ H') (e : G ≅ K) (f : I ≅ L)
    (p : C ⥤ A) (q : D ⥤ B) (d : q ⋙ G ⟶ I ⋙ p)
    (k : q ⋙ K ⟶ L ⋙ p) (c : p ⋙ J' ⟶ H' ⋙ q)
    (ha : ∀ M, a.unit.app M ≫ G.map (x.hom.app M) ≫ e.hom.app (J'.obj M) =
      a'.unit.app M)
    (hb : ∀ M, b.unit.app M ≫ I.map (y.hom.app M) ≫ f.hom.app (H'.obj M) =
      b'.unit.app M)
    (hd : ∀ M, d.app M ≫ p.map (f.hom.app M) = e.hom.app (q.obj M) ≫ k.app M)
    (hc : ∀ M, a'.unit.app (p.obj M) ≫ K.map (c.app M) ≫ k.app (H'.obj M) =
      p.map (b'.unit.app M)) (M : C) :
    a.unit.app (p.obj M) ≫ G.map (x.hom.app (p.obj M) ≫ c.app M ≫
      q.map (y.inv.app M)) ≫ d.app (H.obj M) = p.map (b.unit.app M) := by
  apply (cancel_mono (p.map (I.map (y.hom.app M) ≫ f.hom.app (H'.obj M)))).mp
  simp only [Functor.map_comp, Category.assoc]
  have hn := d.naturality (y.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  simp only [← Category.assoc, ← p.map_comp, ← I.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.assoc]
  rw [hd]
  have he := e.hom.naturality (c.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at he
  rw [reassoc_of% he, reassoc_of% (ha (p.obj M)), hc, hb]

private theorem upperModel_unit (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (sfIntrinsicOpenAdjunction A j).unit.app M ≫
      (upperModel A j).hom.app ((sfIntrinsicExtensionByZero j A).obj M) =
    (sfIntrinsicExtensionByZeroAdjunction j A).unit.app M := by
  simp only [sfIntrinsicOpenAdjunction, sfIntrinsicExtensionByZeroAdjunction,
    Adjunction.comp_unit_app, upperModel, sfIntrinsicTransportIso,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  simp only [ProEtale.openImmersionLowerShriekUpperStarAdjunction,
    ProEtale.localizationLowerShriekUpperStarAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  simp only [Equivalence.symm_inverse, Equivalence.symm_functor]
  have hn := (ProEtale.upperStarIsoOpenImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).hom.naturality
      ((sfIntrinsicModuleEquivalence Z A).toAdjunction.unit.app
        (((sfIntrinsicModuleEquivalence X A).symm.functor ⋙
          ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj M))
  dsimp only [ProEtale.upperStarIsoOpenImmersionRestriction, Functor.comp_obj,
    Equivalence.symm_functor] at hn
  dsimp only [sfIntrinsicExtensionByZero, Functor.comp_obj]
  slice_lhs 4 5 =>
    rw [← (sfIntrinsicModuleEquivalence X A).functor.map_comp]
    erw [hn]
    rw [(sfIntrinsicModuleEquivalence X A).functor.map_comp]
  slice_lhs 3 4 =>
    rw [← (sfIntrinsicModuleEquivalence X A).functor.map_comp]
    erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, ProEtale.openImmersionLowerShriekAdjunction]

private theorem compactSupportOpenRestrictionModel_unit (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} A) j).unit.app M ≫
      (ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} A) j).map
        ((compactSupportOpenModel j A).hom.app M) ≫
      (compactSupportOpenRestrictionModel A j).hom.app ((sfIntrinsicExtensionByZero j A).obj M) =
    (sfIntrinsicExtensionByZeroAdjunction j A).unit.app M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} A) j)
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm) M
  change _ ≫ (ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} A) j).map
    ((compactSupportOpenModel j A).hom.app M) = _ at h
  simp only [Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app] at h
  simp only [compactSupportOpenRestrictionModel, Iso.trans_hom, NatTrans.comp_app, ← Category.assoc]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact upperModel_unit A j M

attribute [local semireducible] sfIntrinsicModuleEquivalence

private theorem scalarRealization_sections (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (V : T.ProEtᵒᵖ) (x : ((sfIntrinsicModuleEquivalence T B).functor.obj M).val.obj V) :
    ((sfRealizationRestriction T φ).hom.app M).val.app V x = x :=
  (sfRealizationRestriction_existsUnique T φ).exists.choose_spec M V x

private theorem scalarRealization_unit (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (V : T.ProEtᵒᵖ) (x : M.obj.obj V) :
    ((sfRealizationRestriction T φ).hom.app M).val.app V
        (sfIntrinsicRealizationUnit T B M V x) =
      sfIntrinsicRealizationUnit T A ((sfFixedRestriction T φ).obj M) V x := by
  rw [scalarRealization_sections]
  rfl

private theorem coefficientDirect_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B)
    (N : proEtaleRingModules X (proEtaleConstantRing X B)) (V : Y.ProEtᵒᵖ)
    (x : N.val.obj ((proEtaleBaseChange f).op.obj V)) :
    ((proEtaleCoefficientDirectImageComparison f φ).hom.app N).val.app V x = x :=
  (proEtaleCoefficientDirectImageComparison_existsUnique f φ).choose_spec.1 N V x

private theorem directRealization_sections (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (V : Y.ProEtᵒᵖ) (x : M.obj.obj ((proEtaleBaseChange f).op.obj V)) :
    ((sfIntrinsicDirectImageComparison f A).hom.app M).val.app V
        (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj V) x) =
      sfIntrinsicRealizationUnit Y A
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M) V x :=
  (sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose_spec M V x

attribute [local irreducible] sfRealizationRestriction sfIntrinsicDirectImageComparison
  proEtaleCoefficientDirectImageComparison

private theorem scalarDirectRealization {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (proEtaleCoefficientDirectImageComparison f φ).hom.app
        ((sfIntrinsicModuleEquivalence X B).functor.obj M) ≫
      (proEtaleConstantModuleDirectImage f A).map
        ((sfRealizationRestriction X φ).hom.app M) ≫
      (sfIntrinsicDirectImageComparison f A).hom.app ((sfFixedRestriction X φ).obj M) =
    (proEtaleCoefficientRestrictScalars Y φ).map
        ((sfIntrinsicDirectImageComparison f B).hom.app M) ≫
      (sfRealizationRestriction Y φ).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M) := by
  ext V x
  let W := (proEtaleBaseChange f).op.obj V
  let η := ((intrinsicUnitIso X B).hom.app M).app W
  let η' := ((intrinsicUnitIso X B).inv.app M).app W
  have hη : η (η' x) = x := by
    change (((intrinsicUnitIso X B).inv.app M ≫
      (intrinsicUnitIso X B).hom.app M).app W) x = x
    rw [Iso.inv_hom_id_app]
    rfl
  let m := η' x
  have hx : sfIntrinsicRealizationUnit X B M W m = x := hη
  change ((sfIntrinsicDirectImageComparison f A).hom.app
      ((sfFixedRestriction X φ).obj M)).val.app V
      (((sfRealizationRestriction X φ).hom.app M).val.app W
        (((proEtaleCoefficientDirectImageComparison f φ).hom.app
          ((sfIntrinsicModuleEquivalence X B).functor.obj M)).val.app V x)) =
    ((sfRealizationRestriction Y φ).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M)).val.app V
      (((sfIntrinsicDirectImageComparison f B).hom.app M).val.app V x)
  erw [coefficientDirect_sections, ← hx, scalarRealization_unit,
    directRealization_sections, directRealization_sections, scalarRealization_unit]
  rfl

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem inverseRealization_counit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (e : C ≌ D) (f : E ≌ F) (p : F ⥤ D) (q : E ⥤ C)
    (r : f.functor ⋙ p ≅ q ⋙ e.functor) (N : F) :
    e.counitIso.inv.app (p.obj N) ≫
        e.functor.map
          (e.inverse.map (p.map (f.counitIso.inv.app N)) ≫
            e.inverse.map (r.hom.app (f.inverse.obj N)) ≫
            e.unitIso.inv.app (q.obj (f.inverse.obj N))) =
      p.map (f.counitIso.inv.app N) ≫ r.hom.app (f.inverse.obj N) := by
  simp only [Functor.map_comp]
  erw [← e.counitIso.inv.naturality_assoc, ← e.counitIso.inv.naturality_assoc]
  simp only [Functor.comp_obj, Functor.id_map, Equivalence.counitInv_functor_comp]
  erw [Category.comp_id]

private theorem realizedAdjunction_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (e : C ≌ D) (f : E ≌ F) {L : C ⥤ E} {R : E ⥤ C} (a : L ⊣ R)
    (P : F ⥤ D) (c : f.functor ⋙ P ≅ R ⋙ e.functor) (N : D) :
    ((((e.symm.toAdjunction.comp a).comp f.toAdjunction).ofNatIsoRight
      (Functor.isoWhiskerLeft _ c.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight f.counitIso _ ≪≫ Functor.leftUnitor _)).unit.app N) =
    e.counitIso.inv.app N ≫ e.functor.map (a.unit.app (e.inverse.obj N)) ≫
      c.inv.app (L.obj (e.inverse.obj N)) := by
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Equivalence.symm_inverse,
    Equivalence.symm_functor, Category.id_comp, Category.assoc]
  erw [c.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  slice_lhs 4 5 =>
    rw [← P.map_comp]
    erw [f.functor_unitIso_comp]
  erw [P.map_id, Category.comp_id, Category.comp_id]

private def literalUnit (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) :
    N ⟶ (proEtaleConstantModuleDirectImage j A).obj
      ((sfIntrinsicOpenRestriction j A).obj N) :=
  (sfIntrinsicModuleEquivalence Z A).counitIso.inv.app N ≫
    (sfIntrinsicModuleEquivalence Z A).functor.map
      ((ProEtale.openImmersionRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
          ((sfIntrinsicModuleEquivalence Z A).inverse.obj N)) ≫
    (sfIntrinsicDirectImageComparison j A).inv.app
      ((ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          ((sfIntrinsicModuleEquivalence Z A).inverse.obj N))

private theorem upperModel_direct_unit (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) :
    (sfIntrinsicConstantModuleAdjunction j A).unit.app N ≫
      (proEtaleConstantModuleDirectImage j A).map ((upperModel A j).hom.app N) =
      literalUnit A j N := by
  rw [sfIntrinsicConstantModuleAdjunction, realizedAdjunction_unit]
  dsimp only [upperModel, sfIntrinsicTransportIso, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  erw [← (sfIntrinsicDirectImageComparison j A).inv.naturality]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  change _ ≫ (sfIntrinsicModuleEquivalence Z A).functor.map
    (_ ≫ (ProEtale.lowerStar _ j).map
      (((ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).leftAdjointUniq
          (ProEtale.openImmersionRestrictionLowerStarAdjunction _ j)).hom.app _)) ≫ _ = _
  rw [Adjunction.unit_leftAdjointUniq_hom_app]
  rfl

private theorem scalarDirectRealization_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (sfRealizationRestriction Y φ).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M) ≫
      (sfIntrinsicDirectImageComparison f A).inv.app ((sfFixedRestriction X φ).obj M) ≫
      (proEtaleConstantModuleDirectImage f A).map
        ((sfRealizationRestriction X φ).inv.app M) =
    (proEtaleCoefficientRestrictScalars Y φ).map
        ((sfIntrinsicDirectImageComparison f B).inv.app M) ≫
      (proEtaleCoefficientDirectImageComparison f φ).hom.app
        ((sfIntrinsicModuleEquivalence X B).functor.obj M) := by
  apply (cancel_epi ((proEtaleCoefficientRestrictScalars Y φ).map
    ((sfIntrinsicDirectImageComparison f B).hom.app M))).mp
  simp only [← Category.assoc]
  rw [← scalarDirectRealization f φ M]
  simp only [Category.assoc, Category.id_comp, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

private theorem literalUnit_scalar {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) (N : proEtaleRingModules Z (proEtaleConstantRing Z B)) :
    literalUnit A j ((proEtaleCoefficientRestrictScalars Z φ).obj N) ≫
        (proEtaleConstantModuleDirectImage j A).map
          ((sfOpenRestrictionCoefficientSquare j φ).hom.app N) =
      (proEtaleCoefficientRestrictScalars Z φ).map (literalUnit B j N) ≫
        (proEtaleCoefficientDirectImageComparison j φ).hom.app
          ((sfIntrinsicOpenRestriction j B).obj N) := by
  let M := (sfIntrinsicModuleEquivalence Z B).inverse.obj N
  let M' := (sfIntrinsicModuleEquivalence Z A).inverse.obj
    ((proEtaleCoefficientRestrictScalars Z φ).obj N)
  let ξ := (sfInverseRealizationRestriction Z φ).hom.app N
  let a := ProEtale.openImmersionRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let b := ProEtale.openImmersionRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  have hc : (sfIntrinsicModuleEquivalence Z A).counitIso.inv.app
        ((proEtaleCoefficientRestrictScalars Z φ).obj N) ≫
        (sfIntrinsicModuleEquivalence Z A).functor.map ξ =
      (proEtaleCoefficientRestrictScalars Z φ).map
        ((sfIntrinsicModuleEquivalence Z B).counitIso.inv.app N) ≫
        (sfRealizationRestriction Z φ).hom.app M := by
    simpa only [ξ, sfInverseRealizationRestriction, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
      Functor.map_comp, Functor.comp_map,
      Functor.comp_obj, Category.assoc] using
      inverseRealization_counit (sfIntrinsicModuleEquivalence Z A)
        (sfIntrinsicModuleEquivalence Z B) (proEtaleCoefficientRestrictScalars Z φ)
        (sfFixedRestriction Z φ) (sfRealizationRestriction Z φ) N
  have hu : a.unit.app M' ≫ (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((ProEtale.openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map ξ) =
      ξ ≫ (sfFixedRestriction Z φ).map (b.unit.app M) := by
    erw [← a.unit.naturality]
    rfl
  have hn := (sfRealizationRestriction Z φ).hom.naturality (b.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [literalUnit]
  simp only [sfOpenRestrictionCoefficientSquare, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app,
    Iso.symm_hom, Functor.comp_map, CategoryTheory.Functor.map_id,
    Functor.map_comp, Category.assoc]
  erw [← reassoc_of% (sfIntrinsicDirectImageComparison j A).inv.naturality
    ((ProEtale.openImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map ξ)]
  slice_lhs 2 3 =>
    erw [← (sfIntrinsicModuleEquivalence Z A).functor.map_comp, hu,
      (sfIntrinsicModuleEquivalence Z A).functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hc, ← reassoc_of% hn]
  erw [(proEtaleConstantModuleDirectImage j A).map_id, Category.id_comp,
    scalarDirectRealization_inv]
  rfl

private theorem native_literal_unit (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (V : Z.ProEtᵒᵖ)
    (x : N.val.obj V) :
    ((compactSupportOpenRestrictionModel A j).hom.app N).val.app
        ((proEtaleBaseChange j).op.obj V)
        (((proEtaleConstantRingAdjunction A j).unit.app N).val.app V x) =
      (literalUnit A j N).val.app V x := by
  have h := (openSquarePullbackModel_existsUnique A j).exists.choose_spec N V.unop x
  have h' := congrArg (fun t ↦ t.val.app V x) (upperModel_direct_unit A j N)
  change ((upperModel A j).hom.app N).val.app ((proEtaleBaseChange j).op.obj V)
    (((sfIntrinsicConstantModuleAdjunction j A).unit.app N).val.app V x) = _ at h'
  change ((upperModel A j).hom.app N).val.app ((proEtaleBaseChange j).op.obj V)
    (((openSquarePullbackModel A j).hom.app N).val.app ((proEtaleBaseChange j).op.obj V)
      (((proEtaleConstantRingAdjunction A j).unit.app N).val.app V x)) = _
  erw [h]
  exact h'

/-- Scalar restriction commutes with the normalized identification of tensor inverse
image with literal open restriction.
Source: Stacks Project, Tag 03D3 (adjoint inverse and direct images of modules),
Tag 03CY (restriction to a localized site), and Tag 03DI (open adjunction).
(blueprint: lem-weil-compact-support-open-restriction-scalar).
Proof: transpose the two composites under the tensor inverse-image/direct-image
adjunction. By the definition of compactSupportScalarPullback as inverse mate, its transpose is the
section-normalized scalar direct-image square. The comparison
openSquarePullbackModel preserves the specified tensor and realization units.
The comparison from fixed-scalar inverse image to literal restriction is likewise
fixed by the open-restriction/direct-image adjunction unit. In fixed-scalar
coordinates, restriction to the open is precomposition and hence commutes literally
with restriction of scalars. The realization coefficient squares preserve the
constant-section maps; the direct-image comparisons preserve those same sections.
Thus both transposes send every section at V to the same section over the pullback
of V, with the same restricted coefficient action. They agree by sectionwise
extensionality, and the adjunction Hom equivalence is injective. This also applies
to the zero ring, the identity coefficient homomorphism, and an empty open. -/
theorem compactSupportOpenRestrictionModel_scalar {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) (N : proEtaleRingModules Z (proEtaleConstantRing Z B)) :
    (compactSupportScalarPullback j φ).app N ≫
      (proEtaleCoefficientRestrictScalars X φ).map
        ((compactSupportOpenRestrictionModel B j).hom.app N) =
    (compactSupportOpenRestrictionModel A j).hom.app
        ((proEtaleCoefficientRestrictScalars Z φ).obj N) ≫
      (sfOpenRestrictionCoefficientSquare j φ).hom.app N := by
  apply ((proEtaleConstantRingAdjunction A j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V x
  let W := (proEtaleBaseChange j).op.obj V
  have hm := unit_mateEquiv_symm (proEtaleConstantRingAdjunction B j)
    (proEtaleConstantRingAdjunction A j) (compactSupportScalarDirectImage j φ).hom N
  have hmx := congrArg (fun t ↦ t.val.app V x) hm
  change ((compactSupportScalarDirectImage j φ).hom.app
      ((ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} B) j).obj N)).val.app V
        (((proEtaleConstantRingAdjunction B j).unit.app N).val.app V x) =
    ((compactSupportScalarPullback j φ).app N).val.app W
      (((proEtaleConstantRingAdjunction A j).unit.app
        ((proEtaleCoefficientRestrictScalars Z φ).obj N)).val.app V x) at hmx
  rw [compactSupportScalarDirectImage_sections] at hmx
  have hl := congrArg (fun t ↦ t.val.app V x) (literalUnit_scalar j φ N)
  change ((sfOpenRestrictionCoefficientSquare j φ).hom.app N).val.app W
      ((literalUnit A j ((proEtaleCoefficientRestrictScalars Z φ).obj N)).val.app V x) =
    ((proEtaleCoefficientDirectImageComparison j φ).hom.app
      ((sfIntrinsicOpenRestriction j B).obj N)).val.app V
        ((literalUnit B j N).val.app V x) at hl
  have hl' := hl.trans (coefficientDirect_sections j φ
    ((sfIntrinsicOpenRestriction j B).obj N) V ((literalUnit B j N).val.app V x))
  change ((compactSupportOpenRestrictionModel B j).hom.app N).val.app W
      (((compactSupportScalarPullback j φ).app N).val.app W
        (((proEtaleConstantRingAdjunction A j).unit.app
          ((proEtaleCoefficientRestrictScalars Z φ).obj N)).val.app V x)) =
    ((sfOpenRestrictionCoefficientSquare j φ).hom.app N).val.app W
      (((compactSupportOpenRestrictionModel A j).hom.app
        ((proEtaleCoefficientRestrictScalars Z φ).obj N)).val.app W
          (((proEtaleConstantRingAdjunction A j).unit.app
            ((proEtaleCoefficientRestrictScalars Z φ).obj N)).val.app V x))
  exact (congrArg
    (fun y ↦ ((compactSupportOpenRestrictionModel B j).hom.app N).val.app W y)
    hmx.symm).trans ((native_literal_unit B j N V x).trans
      (hl'.symm.trans (congrArg
        (fun y ↦ ((sfOpenRestrictionCoefficientSquare j φ).hom.app N).val.app W y)
        (native_literal_unit A j ((proEtaleCoefficientRestrictScalars Z φ).obj N)
          V x).symm)))

private def scalarJ {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars X φ ⋙
        ProEtale.StrictTower.moduleJ (ULift.{u + 1, u} A) j ≅
      ProEtale.StrictTower.moduleJ (ULift.{u + 1, u} B) j ⋙
        proEtaleCoefficientRestrictScalars Z φ :=
  Functor.isoWhiskerLeft _ (compactSupportOpenModel j A) ≪≫
    sfOpenRestriction j φ ≪≫
      Functor.isoWhiskerRight (compactSupportOpenModel j B).symm _

private theorem scalarJ_unit {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (φ : A →+* B) (N : proEtaleRingModules X (proEtaleConstantRing X B)) :
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} A) j).unit.app
        ((proEtaleCoefficientRestrictScalars X φ).obj N) ≫
      (ProEtale.StrictTower.modulePullback (ULift.{u + 1, u} A) j).map
        ((scalarJ j φ).hom.app N) ≫
      (compactSupportScalarPullback j φ).app
        ((ProEtale.StrictTower.moduleJ (ULift.{u + 1, u} B) j).obj N) =
    (proEtaleCoefficientRestrictScalars X φ).map
      ((ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} B) j).unit.app N) := by
  exact normalizedTransport
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} A) j)
    (sfIntrinsicExtensionByZeroAdjunction j A)
    (ProEtale.StrictTower.moduleJAdj (ULift.{u + 1, u} B) j)
    (sfIntrinsicExtensionByZeroAdjunction j B)
    (compactSupportOpenModel j A) (compactSupportOpenModel j B)
    (compactSupportOpenRestrictionModel A j) (compactSupportOpenRestrictionModel B j)
    (proEtaleCoefficientRestrictScalars X φ) (proEtaleCoefficientRestrictScalars Z φ)
    (compactSupportScalarPullback j φ) (sfOpenRestrictionCoefficientSquare j φ).hom
    (sfOpenRestriction j φ).hom
    (compactSupportOpenRestrictionModel_unit A j) (compactSupportOpenRestrictionModel_unit B j)
    (compactSupportOpenRestrictionModel_scalar j φ)
    (sfOpenRestriction_normalized_unique j φ).1 N

end WeilConjectures
