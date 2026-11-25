/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.CompactSupportProperImageTower.CompactSupportProperImageTower
import all WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageRestrictionTransition

/-! # Pasting the normalized direct-image coefficient squares -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem restrictionCompositor_factors
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (J : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Q.obj J) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app J) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
    H.mapDerivedCategoryFactors.hom.app J ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app J) := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  exact Functor.mapDerivedCategoryNatIso_fac e.symm J

private theorem transportSection
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {F G : C ⥤ SheafOfModules.{u} R}
    (h : F = G) (M : C) (U : Dᵒᵖ) (x : (G.obj M).val.obj U) :
    HEq (((eqToIso h).inv.app M).val.app U x) x := by
  cases h
  rfl

private theorem inverseSection
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U), HEq (e.hom.val.app U x) x)
    (U : Cᵒᵖ) (x : N.val.obj U) : HEq (e.inv.val.app U x) x := by
  have hi := congrArg (fun f ↦ f.val.app U x) e.inv_hom_id
  exact (h U (e.inv.val.app U x)).symm.trans (heq_of_eq hi)

private theorem inversePasting
    {C : Type*} [Category C] {A B D E F : C}
    (s : A ≅ B) (b : B ≅ D) (t : E ≅ D) (a : F ≅ E) (c : A ≅ F)
    (h : t.inv ≫ a.inv = b.inv ≫ s.inv ≫ c.hom) :
    c.hom ≫ a.hom ≫ t.hom = s.hom ≫ b.hom := by
  apply (cancel_epi (b.inv ≫ s.inv)).mp
  have hh := congrArg (fun f ↦ f ≫ a.hom ≫ t.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id] using hh.symm

section NormalizedTriangle

variable {C Cm Cn A Am An : Type*}
  [Category C] [Category Cm] [Category Cn] [Category A] [Category Am] [Category An]
  [Abelian C] [Abelian Cm] [Abelian Cn] [Abelian A] [Abelian Am] [Abelian An]
  [HasDerivedCategory C] [HasDerivedCategory Cm] [HasDerivedCategory Cn]
  [HasDerivedCategory A] [HasDerivedCategory Am] [HasDerivedCategory An]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions Cm]
  [Abelian.HasKInjectiveResolutions Cn]
  (G : C ⥤ A) (Gm : Cm ⥤ Am) (Gn : Cn ⥤ An)
  (Hm : C ⥤ Cm) (Hn : C ⥤ Cn) (Km : A ⥤ Am) (Kn : A ⥤ An)
  (R : Cn ⥤ Cm) (S : An ⥤ Am)
  [G.Additive] [Gm.Additive] [Gn.Additive]
  [Hm.Additive] [Hn.Additive] [Km.Additive] [Kn.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits Hm] [PreservesFiniteColimits Hm]
  [PreservesFiniteLimits Hn] [PreservesFiniteColimits Hn]
  [PreservesFiniteLimits Km] [PreservesFiniteColimits Km]
  [PreservesFiniteLimits Kn] [PreservesFiniteColimits Kn]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

private theorem normalizedTriangle
    (a : R.mapDerivedCategory ⋙ Gm.rightDerivedFunctor ≅
      Gn.rightDerivedFunctor ⋙ S.mapDerivedCategory)
    (b : R ⋙ Gm ≅ Gn ⋙ S)
    (dm : Hm.mapDerivedCategory ⋙ Gm.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ Km.mapDerivedCategory)
    (dn : Hn.mapDerivedCategory ⋙ Gn.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ Kn.mapDerivedCategory)
    (bm : G ⋙ Km ≅ Hm ⋙ Gm) (bn : Hn ⋙ Gn ≅ G ⋙ Kn)
    (hc : CompactSupportDerivedSquareNormalization Gn Gm R S b a)
    (hm : CompactSupportDerivedSquareNormalization G Gm Hm Km bm.symm dm)
    (hn : CompactSupportDerivedSquareNormalization G Gn Hn Kn bn dn)
    (eX : Hn ⋙ R ≅ Hm) (eY : Kn ⋙ S ≅ Km)
    (ho : ∀ M : C, eY.inv.app (G.obj M) ≫ S.map (bn.inv.app M) =
      bm.hom.app M ≫ Gm.map (eX.inv.app M) ≫ b.hom.app (Hn.obj M))
    (N : DerivedCategory C) :
    a.hom.app (Hn.mapDerivedCategory.obj N) ≫ S.mapDerivedCategory.map (dn.hom.app N) ≫
        (Functor.mapDerivedCategoryCompIso Kn S ≪≫
          Functor.mapDerivedCategoryNatIso eY).hom.app (G.rightDerivedFunctor.obj N) =
      Gm.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso Hn R ≪≫
            Functor.mapDerivedCategoryNatIso eX).hom.app N) ≫ dm.hom.app N := by
  let cX := Functor.mapDerivedCategoryCompIso Hn R ≪≫
    Functor.mapDerivedCategoryNatIso eX
  let cY := Functor.mapDerivedCategoryCompIso Kn S ≪≫
    Functor.mapDerivedCategoryNatIso eY
  have h := derived_transition G Gm Gn Hm Hn Km Kn R S a b dm.symm dn.symm
    bm bn.symm hc hm hn eX.inv eY.inv cX.inv cY.inv
    (restrictionCompositor_factors Hn R Hm eX)
    (restrictionCompositor_factors Kn S Km eY) ho N
  exact inversePasting (Gm.rightDerivedFunctor.mapIso (cX.app N)) (dm.app N)
    (cY.app (G.rightDerivedFunctor.obj N))
    (S.mapDerivedCategory.mapIso (dn.app N)) (a.app (Hn.mapDerivedCategory.obj N)) h

end NormalizedTriangle

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

private theorem mapTransportSection
    {C D T : Type*} [Category C] [Category D] [Category T]
    {J : GrothendieckTopology T} {R : Sheaf J RingCat.{u}}
    {F G : C ⥤ D} (P : D ⥤ SheafOfModules.{u} R)
    (h : F = G) (M : C) (U : Tᵒᵖ) (x : (P.obj (G.obj M)).val.obj U) :
    HEq ((P.map (X := G.obj M) (Y := F.obj M)
      ((eqToIso h).inv.app M)).val.app U x) x := by
  cases h
  change HEq ((P.map (𝟙 (F.obj M))).val.app U x) x
  rw [P.map_id]
  rfl

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  HasDerivedCategory.standard

private theorem scalarRestriction_identity (T : Scheme.{u}) (k : ℕ)
    {M N : normalizedDVRModules l E T k} (f : M ⟶ N)
    (hf : ∀ (V : T.ProEtᵒᵖ) (x : M.val.obj V), HEq (f.val.app V x) x)
    (U : T.ProEtᵒᵖ) (x : ((scalarReductionRestriction l E T k).obj M).val.obj U) :
    HEq ((((scalarReductionRestriction l E T k).map f).val.app U) x) x := by
  exact restrict_identity _ f hf U x

private theorem sheaf_square_all_identity
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M0 M1 M2 M3 M4 : SheafOfModules.{u} R}
    (f1 : M0 ⟶ M1) (f2 : M1 ⟶ M2)
    (g1 : M0 ⟶ M3) (g2 : M3 ⟶ M4) (g3 : M4 ⟶ M2)
    (hf1 : ∀ U (x : M0.val.obj U), HEq (f1.val.app U x) x)
    (hf2 : ∀ U (x : M1.val.obj U), HEq (f2.val.app U x) x)
    (hg1 : ∀ U (x : M0.val.obj U), HEq (g1.val.app U x) x)
    (hg2 : ∀ U (x : M3.val.obj U), HEq (g2.val.app U x) x)
    (hg3 : ∀ U (x : M4.val.obj U), HEq (g3.val.app U x) x) :
    f1 ≫ f2 = g1 ≫ g2 ≫ g3 := by
  exact sheaf_square_identity f1 f2 g1 g2 g3 hf2 hg1 hg3
    (fun U x y hxy ↦ (hf1 U x).trans (hxy.trans (hg2 U y).symm))

private theorem finiteComparison_identity
    (d : CompactSupportProperImageTower.DirectData l E p) (n : ℕ)
    (M : normalizedDVRModules l E X n) (U : Y.ProEtᵒᵖ)
    (y : ((normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
      compactSupportLevelDirectImage l E p (n + 1)).obj M).val.obj U) :
    HEq (((d.ordinary n).hom.app M).val.app U y) y := by
  have eA := (level_carrier_eq l E p (n + 1)
    ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) U).trans
    (normalized_res_carrier_eq l E X (Nat.le_succ n) M
      ((proEtaleBaseChange p).op.obj U))
  have eB := (normalized_res_carrier_eq l E Y (Nat.le_succ n)
    ((compactSupportLevelDirectImage l E p n).obj M) U).trans
    (level_carrier_eq l E p n M U)
  exact function_identity_of_heq eA eB _ (d.sections n M U) y

private theorem completedComparison_identity (n : ℕ)
    (M : normalizedDVRModules l E X n) (U : Y.ProEtᵒᵖ)
    (x : ((compactSupportLevelDirectImage l E p n ⋙
      scalarReductionRestriction l E Y n).obj M).val.obj U) :
    HEq (((sfDirectImageRestrictionComparison l E p n).hom.app M).val.app U x) x := by
  exact heq_of_eq
    ((sfDirectImageRestrictionComparison_existsUnique l E p n).exists.choose_spec M U x)

section OrdinaryTriangle

variable {C0 C1 C2 D : Type*} [Category C0] [Category C1] [Category C2] [Category D]
  {J : GrothendieckTopology D} {S0 S1 S2 : Sheaf J RingCat.{u}}
  (Fn : C0 ⥤ SheafOfModules.{u} S0) (Fm : C1 ⥤ SheafOfModules.{u} S1)
  (G : C2 ⥤ SheafOfModules.{u} S2)
  (PX : C0 ⥤ C2) (RX : C0 ⥤ C1) (QX : C1 ⥤ C2)
  (PY : SheafOfModules.{u} S0 ⥤ SheafOfModules.{u} S2)
  (RY : SheafOfModules.{u} S0 ⥤ SheafOfModules.{u} S1)
  (QY : SheafOfModules.{u} S1 ⥤ SheafOfModules.{u} S2)

private theorem ordinaryTriangle
    (hX : RX ⋙ QX = PX) (hY : RY ⋙ QY = PY)
    (a : RX ⋙ Fm ≅ Fn ⋙ RY)
    (b0 : Fn ⋙ PY ≅ PX ⋙ G) (b1 : Fm ⋙ QY ≅ QX ⋙ G)
    (hQ : ∀ {M N : SheafOfModules.{u} S1} (f : M ⟶ N),
      (∀ U (x : M.val.obj U), HEq (f.val.app U x) x) →
      ∀ U (x : (QY.obj M).val.obj U), HEq ((QY.map f).val.app U x) x)
    (ha : ∀ (M : C0) U (x : ((RX ⋙ Fm).obj M).val.obj U),
      HEq ((a.hom.app M).val.app U x) x)
    (hb0 : ∀ (M : C0) U (x : ((Fn ⋙ PY).obj M).val.obj U),
      HEq ((b0.hom.app M).val.app U x) x)
    (hb1 : ∀ (M : C1) U (x : ((Fm ⋙ QY).obj M).val.obj U),
      HEq ((b1.hom.app M).val.app U x) x)
    (M : C0) :
    (eqToIso hY).inv.app (Fn.obj M) ≫
      QY.map (X := (Fn ⋙ RY).obj M) (Y := (RX ⋙ Fm).obj M) (a.inv.app M) =
      b0.hom.app M ≫ G.map (X := PX.obj M) (Y := (RX ⋙ QX).obj M)
        ((eqToIso hX).inv.app M) ≫ b1.inv.app (RX.obj M) := by
  exact sheaf_square_all_identity _ _ _ _ _
    (transportSection hY (Fn.obj M))
    (hQ (a.inv.app M) (inverseSection (a.app M) (ha M)))
    (hb0 M) (mapTransportSection G hX M)
    (inverseSection (b1.app (RX.obj M)) (hb1 (RX.obj M)))

variable [Abelian C0] [Abelian C1] [Abelian C2]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory C0] [HasDerivedCategory C1] [HasDerivedCategory C2]
  [HasDerivedCategory (SheafOfModules.{u} S0)]
  [HasDerivedCategory (SheafOfModules.{u} S1)]
  [HasDerivedCategory (SheafOfModules.{u} S2)]
  [Abelian.HasKInjectiveResolutions C0] [Abelian.HasKInjectiveResolutions C1]
  [Abelian.HasKInjectiveResolutions C2]
  [Fn.Additive] [Fm.Additive] [G.Additive] [PX.Additive] [RX.Additive] [QX.Additive]
  [PY.Additive] [RY.Additive] [QY.Additive]
  [PreservesFiniteLimits PX] [PreservesFiniteColimits PX]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits QX] [PreservesFiniteColimits QX]
  [PreservesFiniteLimits PY] [PreservesFiniteColimits PY]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [PreservesFiniteLimits QY] [PreservesFiniteColimits QY]

-- Combine the section calculation with the derived triangle before specializing coefficients.
private theorem sheafDerivedTriangle
    (hX : RX ⋙ QX = PX) (hY : RY ⋙ QY = PY)
    (a0 : RX ⋙ Fm ≅ Fn ⋙ RY)
    (b0 : Fn ⋙ PY ≅ PX ⋙ G) (b1 : Fm ⋙ QY ≅ QX ⋙ G)
    (a : QX.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      Fm.rightDerivedFunctor ⋙ QY.mapDerivedCategory)
    (dm : PX.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      Fn.rightDerivedFunctor ⋙ PY.mapDerivedCategory)
    (dn : RX.mapDerivedCategory ⋙ Fm.rightDerivedFunctor ≅
      Fn.rightDerivedFunctor ⋙ RY.mapDerivedCategory)
    (hc : CompactSupportDerivedSquareNormalization Fm G QX QY b1.symm a)
    (hm : CompactSupportDerivedSquareNormalization Fn G PX PY b0.symm dm)
    (hn : CompactSupportDerivedSquareNormalization Fn Fm RX RY a0 dn)
    (hQ : ∀ {M N : SheafOfModules.{u} S1} (f : M ⟶ N),
      (∀ U (x : M.val.obj U), HEq (f.val.app U x) x) →
      ∀ U (x : (QY.obj M).val.obj U), HEq ((QY.map f).val.app U x) x)
    (ha : ∀ (M : C0) U (x : ((RX ⋙ Fm).obj M).val.obj U),
      HEq ((a0.hom.app M).val.app U x) x)
    (hb0 : ∀ (M : C0) U (x : ((Fn ⋙ PY).obj M).val.obj U),
      HEq ((b0.hom.app M).val.app U x) x)
    (hb1 : ∀ (M : C1) U (x : ((Fm ⋙ QY).obj M).val.obj U),
      HEq ((b1.hom.app M).val.app U x) x)
    (N : DerivedCategory C0) :
    a.hom.app (RX.mapDerivedCategory.obj N) ≫ QY.mapDerivedCategory.map (dn.hom.app N) ≫
        (Functor.mapDerivedCategoryCompIso RY QY ≪≫
          Functor.mapDerivedCategoryNatIso (eqToIso hY)).hom.app (Fn.rightDerivedFunctor.obj N) =
      G.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso RX QX ≪≫
            Functor.mapDerivedCategoryNatIso (eqToIso hX)).hom.app N) ≫ dm.hom.app N := by
  exact normalizedTriangle Fn G Fm PX RX PY RY QX QY a b1.symm dm dn b0 a0
    hc hm hn (eqToIso hX) (eqToIso hY)
    (ordinaryTriangle Fn Fm G PX RX QX PY RY QY hX hY a0 b0 b1 hQ ha hb0 hb1) N

end OrdinaryTriangle

attribute [local irreducible] sfCompletedModuleDirectImage sheafCompose
  CommRingCat.hasForgetToRingCat
  CommRingCat.instConcreteCategoryRingHomCarrier
  RingCat.instConcreteCategoryRingHomCarrier

-- Inference shares the coefficient-category interfaces with the abstract lemma.
set_option linter.defProp false in
private def derivedBase
    (d : CompactSupportProperImageTower.DirectData l E p) (n : ℕ) :=
  let := d
  let := normalizedDVRModuleRes_limits l E X (Nat.le_succ n)
  let := normalizedDVRModuleRes_colimits l E X (Nat.le_succ n)
  let := normalizedDVRModuleRes_limits l E Y (Nat.le_succ n)
  let := normalizedDVRModuleRes_colimits l E Y (Nat.le_succ n)
  let := sfRestrictionLimits l E X n
  let := sfRestrictionColimits l E X n
  let := sfRestrictionLimits l E Y n
  let := sfRestrictionColimits l E Y n
  let := sfRestrictionLimits l E X (n + 1)
  let := sfRestrictionColimits l E X (n + 1)
  let := sfRestrictionLimits l E Y (n + 1)
  let := sfRestrictionColimits l E Y (n + 1)
  let Fn := compactSupportLevelDirectImage l E p n
  let Fm := compactSupportLevelDirectImage l E p (n + 1)
  let G := sfCompletedModuleDirectImage l E p
  let PX := scalarReductionRestriction l E X n
  let PY := scalarReductionRestriction l E Y n
  let QX := scalarReductionRestriction l E X (n + 1)
  let QY := scalarReductionRestriction l E Y (n + 1)
  let RX := normalizedDVRModuleRes l E X (Nat.le_succ n)
  let RY := normalizedDVRModuleRes l E Y (Nat.le_succ n)
  sheafDerivedTriangle
    (C0 := normalizedDVRModules l E X n)
    (C1 := normalizedDVRModules l E X (n + 1))
    (C2 := scalarReductionSource.{u, u} l E X)
    (D := Y.ProEt) (J := ProEt.topology Y)
    (S0 := integralCoefficientSheaf l E Y n)
    (S1 := integralCoefficientSheaf l E Y (n + 1))
    Fn Fm G PX RX QX PY RY QY

-- Retain that shared interface when supplying the concrete normalizations.
set_option linter.defProp false in
private def completePasting
    (d : CompactSupportProperImageTower.DirectData l E p) (n : ℕ) :=
  let := d
  derivedBase l E p d n
    (coefficientRestrictionComp l E X (Nat.le_succ n))
    (coefficientRestrictionComp l E Y (Nat.le_succ n)) (d.ordinary n)
    (sfDirectImageRestrictionComparison l E p n)
    (sfDirectImageRestrictionComparison l E p (n + 1))
    (sfDerivedRestrictionComparison l E p (n + 1))
    (sfDerivedRestrictionComparison l E p n) (d.comparison n)
    (sfDerivedRestrictionComparison_existsUnique l E p (n + 1)).exists.choose_spec
    (sfDerivedRestrictionComparison_existsUnique l E p n).exists.choose_spec
    (d.normalization n)
    (scalarRestriction_identity l E Y (n + 1)) (finiteComparison_identity l E p d n)
    (completedComparison_identity l E p n) (completedComparison_identity l E p (n + 1))

/-- The normalized direct-image restriction squares respect successive restriction.
This is independent of a completed input K and of the coefficient reduction map.
Source: Stacks Tags 0D6E and 0D6J.
(blueprint: lem-sf-direct-image-restriction-pasting).
Proof: the underived completed/finite and finite/finite restriction squares preserve
sections by sfDirectImageRestrictionComparison_existsUnique and d.sections. Their
pastes are consequently equal after inserting the restriction compositors. Resolve a
finite-coefficient complex by a K-injective complex, and resolve every restricted
complex once more. Apply d.normalization and the resolution characterization of
sfDerivedRestrictionComparison to the two pastes. The common ordinary paste gives
equal derived maps on these models. Cancel the resolution quasi-isomorphisms and
extend by naturality to B. This never assumes restriction preserves K-injectives. -/
theorem sfDirectImageRestriction_pasting
    (d : CompactSupportProperImageTower.DirectData l E p) (n : ℕ)
    (B : normalizedDVRDerived l E X n) :
    (sfDerivedRestrictionComparison l E p (n + 1)).hom.app
          ((normalizedDVRRes l E X (Nat.le_succ n)).obj B) ≫
        (coefficientFiniteDerivedRestriction l E Y (n + 1)).map
          ((d.comparison n).hom.app B) ≫
        (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n)).hom.app
          ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj B) =
      (sfCompletedDerivedDirectImage l E p).map
          ((compactSupportSystemRestrictionComp l E X (Nat.le_succ n)).hom.app B) ≫
        (sfDerivedRestrictionComparison l E p n).hom.app B := by
  exact completePasting l E p d n B

end WeilConjectures
