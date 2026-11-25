/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientStructureMap
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.ProEtaleRestrictionPushforwardAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Normalized direct image at the constant and finite coefficient levels

Source: Stacks Project, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-pur-completed-coefficient-image-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv c cv z zv d e ev q qv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
section FormalCoherence
variable {A₀ : Type a} [Category.{av} A₀] [Abelian A₀] [HasDerivedCategory.{d} A₀]
  {B₀ : Type b} [Category.{bv} B₀] [Abelian B₀] [HasDerivedCategory.{d} B₀]
  {A₁ : Type c} [Category.{cv} A₁] [Abelian A₁] [HasDerivedCategory.{d} A₁]
  {B₁ : Type z} [Category.{zv} B₁] [Abelian B₁] [HasDerivedCategory.{d} B₁]
  (F : A₀ ⥤ B₀) (G : A₁ ⥤ B₁) (x : A₀ ⥤ A₁) (y : B₀ ⥤ B₁)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [x.PreservesZeroMorphisms] [y.PreservesZeroMorphisms]
  (RF : RightImage F) (RG : RightImage G) (DX : ExactImage x) (DY : ExactImage y)

private theorem image_unit_ext [Abelian.HasKInjectiveResolutions A₀]
    (Y : DerivedCategory B₀ ⥤ DerivedCategory B₁)
    {T : DerivedCategory A₀ ⥤ DerivedCategory B₁}
    (α β : RF.functor ⋙ Y ⟶ T)
    (h : ∀ I : CochainComplex A₀ ℤ,
      Y.map (RF.unit.app I) ≫ α.app (DerivedCategory.Q.obj I) =
        Y.map (RF.unit.app I) ≫ β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply NatTrans.ext
  funext N
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := RF.computes I hI
  have hi : α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I) :=
    (cancel_epi (Y.map (RF.unit.app I))).mp (h I)
  apply (cancel_mono (T.map e.hom)).mp
  rw [← α.naturality e.hom, ← β.naturality e.hom, hi]

private theorem square_naturality [Abelian.HasKInjectiveResolutions A₀]
    (x' : A₀ ⥤ A₁) (y' : B₀ ⥤ B₁)
    [x'.PreservesZeroMorphisms] [y'.PreservesZeroMorphisms]
    (DX' : ExactImage x') (DY' : ExactImage y')
    (S : Square F G x y RF RG DX DY) (S' : Square F G x' y' RF RG DX' DY')
    (a : x ⟶ x') (b : y ⟶ y')
    (ad : DX.functor ⟶ DX'.functor) (bd : DY.functor ⟶ DY'.functor)
    (ha : ∀ I : CochainComplex A₀ ℤ,
      ad.app (DerivedCategory.Q.obj I) ≫ DX'.factors.hom.app I =
        DX.factors.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I))
    (hb : ∀ I : CochainComplex B₀ ℤ,
      bd.app (DerivedCategory.Q.obj I) ≫ DY'.factors.hom.app I =
        DY.factors.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex b (.up ℤ)).app I))
    (hc : ∀ M : A₀, b.app (F.obj M) ≫ S'.ordinary.hom.app M =
      S.ordinary.hom.app M ≫ G.map (a.app M)) :
    Functor.whiskerLeft RF.functor bd ≫ S'.comparison.hom =
      S.comparison.hom ≫ Functor.whiskerRight ad RG.functor := by
  apply image_unit_ext F RF DY.functor
  intro I
  apply (cancel_mono (RG.functor.map (DX'.factors.hom.app I))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [reassoc_of% bd.naturality (RF.unit.app I)]
  rw [S'.normalization I]
  rw [reassoc_of% hb ((F.mapHomologicalComplex (.up ℤ)).obj I)]
  rw [← RG.functor.map_comp, ha, Functor.map_comp]
  rw [reassoc_of% S.normalization I]
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hcI :
      (NatTrans.mapHomologicalComplex b (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (NatIso.mapHomologicalComplex S'.ordinary (.up ℤ)).hom.app I =
      (NatIso.mapHomologicalComplex S.ordinary (.up ℤ)).hom.app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I) := by
    ext n
    exact hc (I.X n)
  rw [hcI, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ DY.factors.hom.app
    ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex S.ordinary.hom (.up ℤ)).app I) ≫ k)
    (RG.unit.naturality ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I))

private theorem square_identity [Abelian.HasKInjectiveResolutions A₀]
    (x : A₀ ⥤ A₀) (y : B₀ ⥤ B₀)
    [x.PreservesZeroMorphisms] [y.PreservesZeroMorphisms]
    (DX : ExactImage x) (DY : ExactImage y)
    (IX : ExactIdentity x DX) (IY : ExactIdentity y DY)
    (S : Square F F x y RF RF DX DY)
    (hc : ∀ M : A₀, IY.ordinary.hom.app (F.obj M) =
      S.ordinary.hom.app M ≫ F.map (IX.ordinary.hom.app M))
    (K : DerivedCategory A₀) :
    S.comparison.hom.app K ≫ RF.functor.map (IX.comparison.hom.app K) =
      IY.comparison.hom.app (RF.functor.obj K) := by
  let DA : ExactImage (𝟭 A₀) := ⟨𝟭 _, Functor.rightUnitor _⟩
  let DB : ExactImage (𝟭 B₀) := ⟨𝟭 _, Functor.rightUnitor _⟩
  let T : Square F F (𝟭 A₀) (𝟭 B₀) RF RF DA DB :=
    ⟨Iso.refl _, Iso.refl _, fun I ↦ by
      change RF.unit.app I ≫ 𝟙 _ ≫ RF.functor.map (𝟙 _) =
        𝟙 _ ≫ DerivedCategory.Q.map (𝟙 _) ≫ RF.unit.app I
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      erw [Category.comp_id]⟩
  have ht := square_naturality F F x y RF RF DX DY (𝟭 A₀) (𝟭 B₀) DA DB S T
    IX.ordinary.hom IY.ordinary.hom IX.comparison.hom IY.comparison.hom
    (fun I ↦ by
      change IX.comparison.hom.app (DerivedCategory.Q.obj I) ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact IX.normalization I)
    (fun I ↦ by
      change IY.comparison.hom.app (DerivedCategory.Q.obj I) ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact IY.normalization I)
    (fun M ↦ by
      change IY.ordinary.hom.app (F.obj M) ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact hc M)
  have hh := NatTrans.congr_app ht K
  simpa only [T, Iso.refl_hom, NatTrans.id_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.comp_id] using hh.symm

variable {A₂ : Type e} [Category.{ev} A₂] [Abelian A₂] [HasDerivedCategory.{d} A₂]
  {B₂ : Type q} [Category.{qv} B₂] [Abelian B₂] [HasDerivedCategory.{d} B₂]
  (H : A₂ ⥤ B₂) (x' : A₁ ⥤ A₂) (y' : B₁ ⥤ B₂)
  [H.PreservesZeroMorphisms] [x'.PreservesZeroMorphisms] [y'.PreservesZeroMorphisms]
  (RH : RightImage H) (DX' : ExactImage x') (DY' : ExactImage y')

private def exactComposite : ExactImage (x ⋙ x') where
  functor := DX.functor ⋙ DX'.functor
  factors := Functor.isoWhiskerRight DX.factors DX'.functor ≪≫
    Functor.isoWhiskerLeft (x.mapHomologicalComplex (.up ℤ)) DX'.factors

private def squareComposite (S : Square F G x y RF RG DX DY)
    (S' : Square G H x' y' RG RH DX' DY') :
    Square F H (x ⋙ x') (y ⋙ y') RF RH
      (exactComposite x DX x' DX') (exactComposite y DY y' DY') where
  ordinary := Functor.isoWhiskerRight S.ordinary y' ≪≫
    Functor.isoWhiskerLeft x S'.ordinary
  comparison := Functor.isoWhiskerRight S.comparison DY'.functor ≪≫
    Functor.isoWhiskerLeft DX.functor S'.comparison
  normalization I := by
    simp only [exactComposite, Functor.comp_map, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Category.assoc, Functor.map_comp]
    erw [← reassoc_of% S'.comparison.hom.naturality (DX.factors.hom.app I)]
    simp only [Functor.comp_obj]
    erw [← DY'.functor.map_comp_assoc, ← DY'.functor.map_comp_assoc]
    erw [Category.assoc, S.normalization I]
    simp only [Functor.map_comp, Category.assoc]
    erw [S'.normalization ((x.mapHomologicalComplex (.up ℤ)).obj I)]
    erw [reassoc_of% (DY'.factors.hom.naturality
      ((NatTrans.mapHomologicalComplex S.ordinary.hom (.up ℤ)).app I))]
    simp only [← DerivedCategory.Q.map_comp_assoc]
    rfl

private theorem square_composition [Abelian.HasKInjectiveResolutions A₀]
    (z : A₀ ⥤ A₂) (w : B₀ ⥤ B₂)
    [z.PreservesZeroMorphisms] [w.PreservesZeroMorphisms]
    (DZ : ExactImage z) (DW : ExactImage w)
    (CX : ExactComposition x x' z DZ DX DX')
    (CY : ExactComposition y y' w DW DY DY')
    (S : Square F G x y RF RG DX DY)
    (S' : Square G H x' y' RG RH DX' DY')
    (S₀ : Square F H z w RF RH DZ DW)
    (hc : ∀ M : A₀, CY.ordinary.hom.app (F.obj M) ≫ S₀.ordinary.hom.app M =
      y'.map (S.ordinary.hom.app M) ≫ S'.ordinary.hom.app (x.obj M) ≫
        H.map (CX.ordinary.hom.app M))
    (K : DerivedCategory A₀) :
    S₀.comparison.hom.app K ≫ RH.functor.map (CX.comparison.inv.app K) =
      CY.comparison.inv.app (RF.functor.obj K) ≫
        DY'.functor.map (S.comparison.hom.app K) ≫
        S'.comparison.hom.app (DX.functor.obj K) := by
  let T := squareComposite F G x y RF RG DX DY H x' y' RH DX' DY' S S'
  have ht := square_naturality F H (x ⋙ x') (y ⋙ y') RF RH
    (exactComposite x DX x' DX') (exactComposite y DY y' DY')
    z w DZ DW T S₀ CX.ordinary.hom CY.ordinary.hom
    CX.comparison.hom CY.comparison.hom
    (fun I ↦ by
      simpa only [exactComposite, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
        NatIso.mapHomologicalComplex] using CX.normalization I)
    (fun I ↦ by
      simpa only [exactComposite, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
        NatIso.mapHomologicalComplex] using CY.normalization I)
    (fun M ↦ by
      simpa only [T, squareComposite, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using hc M)
  have h := congrArg (fun k ↦ CY.comparison.inv.app (RF.functor.obj K) ≫
    k.app K ≫ RH.functor.map (CX.comparison.inv.app K)) ht
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← RH.functor.map_comp,
    Iso.hom_inv_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h
end FormalCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance moduleGrothendieck (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    IsGrothendieckAbelian.{max u (t + 1)} (Mod W B) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := integralCoefficientAbSheafify.{t, u} W
  let := integralCoefficientAbLocallyBijective.{t, u} W
  exact CategoryTheory.moduleSheaves_grothendieck (ProEt.topology W) B

private theorem moduleKInjectiveResolutions (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    Abelian.HasKInjectiveResolutions (Mod W B) := by
  let := moduleGrothendieck.{t, u} W B
  infer_instance

private theorem moduleHom_ext (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)})
    {M N : Mod W B} {p q : M ⟶ N}
    (h : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      HEq ((p.val.app U) x) ((q.val.app U) x)) : p = q := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact eq_of_heq (h U x)

private theorem ordinary_identity {X Y : Scheme.{t}} (f : X ⟶ Y)
    {B : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {D : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (aX : B ⟶ B) (aY : D ⟶ D) (c : D ⟶ (ringPush.{t, u} f).obj B)
    (eX : SheafOfModules.restrictScalars aX ⟶ 𝟭 (Mod X B))
    (eY : SheafOfModules.restrictScalars aY ⟶ 𝟭 (Mod Y D))
    (S : push f c ⋙ SheafOfModules.restrictScalars aY ⟶
      SheafOfModules.restrictScalars aX ⋙ push f c)
    (hX : IsSectionwiseIdentity X B eX) (hY : IsSectionwiseIdentity Y D eY)
    (hS : IsSectionwiseIdentity Y D S) (M : Mod X B) :
    eY.app ((push f c).obj M) = S.app M ≫ (push f c).map (eX.app M) := by
  apply moduleHom_ext.{t, u} Y D
  intro U x
  exact (hY _ U x).trans ((hX M _ _).trans (hS M U x)).symm

private theorem ordinary_composition {X Y : Scheme.{t}} (f : X ⟶ Y)
    {B₀ B₁ B₂ : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {D₀ D₁ D₂ : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (aX : B₁ ⟶ B₀) (aY : D₁ ⟶ D₀) (bX : B₂ ⟶ B₁) (bY : D₂ ⟶ D₁)
    (dX : B₂ ⟶ B₀) (dY : D₂ ⟶ D₀)
    (c₀ : D₀ ⟶ (ringPush.{t, u} f).obj B₀)
    (c₁ : D₁ ⟶ (ringPush.{t, u} f).obj B₁)
    (c₂ : D₂ ⟶ (ringPush.{t, u} f).obj B₂)
    (eX : SheafOfModules.restrictScalars aX ⋙ SheafOfModules.restrictScalars bX ⟶
      SheafOfModules.restrictScalars dX)
    (eY : SheafOfModules.restrictScalars aY ⋙ SheafOfModules.restrictScalars bY ⟶
      SheafOfModules.restrictScalars dY)
    (S : push f c₀ ⋙ SheafOfModules.restrictScalars aY ⟶
      SheafOfModules.restrictScalars aX ⋙ push f c₁)
    (T : push f c₁ ⋙ SheafOfModules.restrictScalars bY ⟶
      SheafOfModules.restrictScalars bX ⋙ push f c₂)
    (S₀ : push f c₀ ⋙ SheafOfModules.restrictScalars dY ⟶
      SheafOfModules.restrictScalars dX ⋙ push f c₂)
    (hX : IsSectionwiseIdentity X B₂ eX) (hY : IsSectionwiseIdentity Y D₂ eY)
    (hS : IsSectionwiseIdentity Y D₁ S) (hT : IsSectionwiseIdentity Y D₂ T)
    (hS₀ : IsSectionwiseIdentity Y D₂ S₀) (M : Mod X B₀) :
    eY.app ((push f c₀).obj M) ≫ S₀.app M =
      (SheafOfModules.restrictScalars bY).map (S.app M) ≫
        T.app ((SheafOfModules.restrictScalars aX).obj M) ≫
        (push f c₂).map (eX.app M) := by
  apply moduleHom_ext.{t, u} Y D₂
  intro U x
  exact ((hS₀ M U _).trans (hY _ U x)).trans
    ((hX M _ _).trans ((hT _ U _).trans (hS M U x))).symm

private instance pushAdditive {X Y : Scheme.{t}} (f : X ⟶ Y)
    {B : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {C : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (c : C ⟶ (ringPush.{t, u} f).obj B) : (push f c).Additive where

private def ordinarySquare {X Y : Scheme.{t}} (f : X ⟶ Y)
    {AX BX : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {AY BY : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (cA : AY ⟶ (ringPush.{t, u} f).obj AX)
    (cB : BY ⟶ (ringPush.{t, u} f).obj BX)
    (h : aY ≫ cB = cA ≫ (ringPush.{t, u} f).map aX) :
    push f cB ⋙ SheafOfModules.restrictScalars.{max u (t + 1)} aY ≅
      SheafOfModules.restrictScalars.{max u (t + 1)} aX ⋙ push f cA :=
  SheafOfModules.pushforwardComp.{max u (t + 1)}
      (F := 𝟭 Y.ProEt) (G := proEtaleBaseChange f) aY cB ≪≫
    SheafOfModules.pushforwardCongr h ≪≫
      (SheafOfModules.pushforwardComp.{max u (t + 1)}
        (F := proEtaleBaseChange f) (G := 𝟭 X.ProEt) cA aX).symm

private theorem ordinarySquare_sections {X Y : Scheme.{t}} (f : X ⟶ Y)
    {AX BX : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {AY BY : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (cA : AY ⟶ (ringPush.{t, u} f).obj AX)
    (cB : BY ⟶ (ringPush.{t, u} f).obj BX)
    (h : aY ≫ cB = cA ≫ (ringPush.{t, u} f).map aX) :
    IsSectionwiseIdentity Y AY (ordinarySquare f aX aY cA cB h).hom := by
  intro M U x
  rfl

private theorem derivedSquare {X Y : Scheme.{t}} (f : X ⟶ Y)
    {AX BX : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {AY BY : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (hAX : ∀ (U : X.ProEtᵒᵖ) (a b : AX.obj.obj U), a * b = b * a)
    (hBX : ∀ (U : X.ProEtᵒᵖ) (a b : BX.obj.obj U), a * b = b * a)
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (cA : AY ⟶ (ringPush.{t, u} f).obj AX)
    (cB : BY ⟶ (ringPush.{t, u} f).obj BX)
    (h : aY ≫ cB = cA ≫ (ringPush.{t, u} f).map aX)
    (FB : RightImage (push f cB)) (FA : RightImage (push f cA))
    (DX : ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)} aX))
    (DY : ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)} aY)) :
    ∃ S : Square (push f cB) (push f cA)
        (SheafOfModules.restrictScalars.{max u (t + 1)} aX)
        (SheafOfModules.restrictScalars.{max u (t + 1)} aY) FB FA DX DY,
      IsSectionwiseIdentity Y AY S.ordinary.hom := by
  let e := ordinarySquare f aX aY cA cB h
  obtain ⟨b, hb, -⟩ := CategoryTheory.derivedCoefficientComparison
    (push f cB) (push f cA) (SheafOfModules.restrictScalars aX)
    (SheafOfModules.restrictScalars aY) DX.functor DY.functor DX.factors DY.factors
    FB.functor FA.functor FB.unit FA.unit FB.computes
    (restrictionPushforward_acyclic f hAX hBX aX cA FA) e
  refine ⟨⟨e, b, ?_⟩, ordinarySquare_sections f aX aY cA cB h⟩
  intro K
  have hh := congrArg (fun z ↦
    DY.factors.hom.app (((push f cB).mapHomologicalComplex (.up ℤ)).obj K) ≫ z ≫
      FA.functor.map (DX.factors.hom.app K)) (hb K)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  exact hh

private theorem constant_comm (W : Scheme.{t}) (B : CommRingCat.{max u (t + 1)})
    (U : W.ProEtᵒᵖ)
    (a b : ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj B)).obj.obj U) :
    a * b = b * a :=
  @mul_comm (((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj B).obj.obj U)
    inferInstance a b

private theorem finiteStructure_quotient {X Y : Scheme.{t}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    quotientMap l E Y h ≫ finiteStructure l E f n =
      finiteStructure l E f m ≫ (ringPush.{t, u} f).map (quotientMap l E X h) := by
  let e : integralCoefficientSheafSystem l E Y ⟶
      integralCoefficientSheafSystem l E X ⋙ ringPush.{t, u} f :=
    NatTrans.ofOpSequence (finiteStructure l E f) (by
      intro k
      simp only [Functor.comp_map, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (finiteStructure_transition f l E k).symm)
  exact e.naturality (homOfLE h).op

private theorem quotientIdentity_of_sections {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientImageData l E f)
    (hSQ : ∀ m n (h : n ≤ m),
      IsSectionwiseIdentity Y (N l E Y m) (C.quotientSquare h).ordinary.hom) :
    ∀ n (K : DerivedCategory (Mod X (N l E X n))),
    (C.quotientSquare (le_refl n)).comparison.hom.app K ≫
        (C.finiteImage n).functor.map ((C.source.restrictionIdentity n).comparison.hom.app K) =
      (C.target.restrictionIdentity n).comparison.hom.app ((C.finiteImage n).functor.obj K) := by
  intro n K
  let : Abelian (Mod X (N l E X n)) := modAbelian.{t, u} X (N l E X n)
  let : Abelian (Mod Y (N l E Y n)) := modAbelian.{t, u} Y (N l E Y n)
  have : Abelian.HasKInjectiveResolutions (Mod X (N l E X n)) :=
    moduleKInjectiveResolutions.{t, u} X (N l E X n)
  apply square_identity
    (A₀ := Mod X (N l E X n)) (B₀ := Mod Y (N l E Y n))
    (push f (finiteStructure l E f n)) (C.finiteImage n)
    (SheafOfModules.restrictScalars (quotientMap l E X (le_refl n)))
    (SheafOfModules.restrictScalars (quotientMap l E Y (le_refl n)))
    (C.source.restriction (le_refl n)) (C.target.restriction (le_refl n))
    (C.source.restrictionIdentity n) (C.target.restrictionIdentity n) (C.quotientSquare (le_refl n))
    ?_ K
  exact ordinary_identity f
    (B := N l E X n) (D := N l E Y n)
    (quotientMap l E X (le_refl n)) (quotientMap l E Y (le_refl n))
    (finiteStructure l E f n)
    (C.source.restrictionIdentity n).ordinary.hom
    (C.target.restrictionIdentity n).ordinary.hom
    (C.quotientSquare (le_refl n)).ordinary.hom
    (C.source.restrictionIdentity_sections n) (C.target.restrictionIdentity_sections n)
    (hSQ n n (le_refl n))

private theorem quotientOrdinaryCoherence {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientImageData l E f)
    (hSQ : ∀ m n (h : n ≤ m),
      IsSectionwiseIdentity Y (N l E Y m) (C.quotientSquare h).ordinary.hom)
    {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m) (M : Mod X (N l E X n)) :
    (C.target.restrictionComposition hkm hmn).ordinary.hom.app
        ((push f (finiteStructure l E f n)).obj M) ≫
      (C.quotientSquare (hmn.trans hkm)).ordinary.hom.app M =
    (SheafOfModules.restrictScalars (quotientMap l E Y hkm)).map
        ((C.quotientSquare hmn).ordinary.hom.app M) ≫
      (C.quotientSquare hkm).ordinary.hom.app
        ((SheafOfModules.restrictScalars (quotientMap l E X hmn)).obj M) ≫
      (push f (finiteStructure l E f k)).map
        ((C.source.restrictionComposition hkm hmn).ordinary.hom.app M) := by
  exact ordinary_composition f
    (B₀ := N l E X n) (B₁ := N l E X m) (B₂ := N l E X k)
    (D₀ := N l E Y n) (D₁ := N l E Y m) (D₂ := N l E Y k)
    (quotientMap l E X hmn) (quotientMap l E Y hmn)
    (quotientMap l E X hkm) (quotientMap l E Y hkm)
    (quotientMap l E X (hmn.trans hkm)) (quotientMap l E Y (hmn.trans hkm))
    (finiteStructure l E f n) (finiteStructure l E f m) (finiteStructure l E f k)
    (C.source.restrictionComposition hkm hmn).ordinary.hom
    (C.target.restrictionComposition hkm hmn).ordinary.hom
    (C.quotientSquare hmn).ordinary.hom (C.quotientSquare hkm).ordinary.hom
    (C.quotientSquare (hmn.trans hkm)).ordinary.hom
    (C.source.restrictionComposition_identity hkm hmn)
    (C.target.restrictionComposition_identity hkm hmn)
    (hSQ m n hmn) (hSQ k m hkm) (hSQ k n (hmn.trans hkm)) M

private theorem quotientCoherence_of_sections {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientImageData l E f)
    (hSQ : ∀ m n (h : n ≤ m),
      IsSectionwiseIdentity Y (N l E Y m) (C.quotientSquare h).ordinary.hom) :
    ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m)
    (K : DerivedCategory (Mod X (N l E X n))),
    (C.quotientSquare (hmn.trans hkm)).comparison.hom.app K ≫
        (C.finiteImage k).functor.map
          ((C.source.restrictionComposition hkm hmn).comparison.inv.app K) =
      (C.target.restrictionComposition hkm hmn).comparison.inv.app
          ((C.finiteImage n).functor.obj K) ≫
        (C.target.restriction hkm).functor.map ((C.quotientSquare hmn).comparison.hom.app K) ≫
        (C.quotientSquare hkm).comparison.hom.app ((C.source.restriction hmn).functor.obj K) := by
  intro k m n hkm hmn K
  let : Abelian (Mod X (N l E X n)) := modAbelian.{t, u} X (N l E X n)
  let : Abelian (Mod Y (N l E Y n)) := modAbelian.{t, u} Y (N l E Y n)
  let : Abelian (Mod X (N l E X m)) := modAbelian.{t, u} X (N l E X m)
  let : Abelian (Mod Y (N l E Y m)) := modAbelian.{t, u} Y (N l E Y m)
  let : Abelian (Mod X (N l E X k)) := modAbelian.{t, u} X (N l E X k)
  let : Abelian (Mod Y (N l E Y k)) := modAbelian.{t, u} Y (N l E Y k)
  have : Abelian.HasKInjectiveResolutions (Mod X (N l E X n)) :=
    moduleKInjectiveResolutions.{t, u} X (N l E X n)
  exact square_composition
    (A₀ := Mod X (N l E X n)) (B₀ := Mod Y (N l E Y n))
    (A₁ := Mod X (N l E X m)) (B₁ := Mod Y (N l E Y m))
    (A₂ := Mod X (N l E X k)) (B₂ := Mod Y (N l E Y k))
    (push f (finiteStructure l E f n)) (push f (finiteStructure l E f m))
    (SheafOfModules.restrictScalars (quotientMap l E X hmn))
    (SheafOfModules.restrictScalars (quotientMap l E Y hmn))
    (C.finiteImage n) (C.finiteImage m) (C.source.restriction hmn) (C.target.restriction hmn)
    (push f (finiteStructure l E f k))
    (SheafOfModules.restrictScalars (quotientMap l E X hkm))
    (SheafOfModules.restrictScalars (quotientMap l E Y hkm))
    (C.finiteImage k) (C.source.restriction hkm) (C.target.restriction hkm)
    (SheafOfModules.restrictScalars (quotientMap l E X (hmn.trans hkm)))
    (SheafOfModules.restrictScalars (quotientMap l E Y (hmn.trans hkm)))
    (C.source.restriction (hmn.trans hkm)) (C.target.restriction (hmn.trans hkm))
    (C.source.restrictionComposition hkm hmn) (C.target.restrictionComposition hkm hmn)
    (C.quotientSquare hmn) (C.quotientSquare hkm) (C.quotientSquare (hmn.trans hkm))
    (quotientOrdinaryCoherence l E f C hSQ hkm hmn) K

private theorem projectionOrdinaryCoherence {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientImageData l E f)
    (hSN : ∀ n, IsSectionwiseIdentity Y (R l E Y) (C.finiteSquare n).ordinary.hom)
    (hSQ : ∀ m n (h : n ≤ m),
      IsSectionwiseIdentity Y (N l E Y m) (C.quotientSquare h).ordinary.hom)
    {m n : ℕ} (h : n ≤ m) (M : Mod X (N l E X n)) :
    (C.target.projectionComposition h).ordinary.hom.app
        ((push f (finiteStructure l E f n)).obj M) ≫
      (C.finiteSquare n).ordinary.hom.app M =
    (SheafOfModules.restrictScalars (projection l E Y m)).map
        ((C.quotientSquare h).ordinary.hom.app M) ≫
      (C.finiteSquare m).ordinary.hom.app
        ((SheafOfModules.restrictScalars (quotientMap l E X h)).obj M) ≫
      (push f C.structureMap).map
        ((C.source.projectionComposition h).ordinary.hom.app M) := by
  exact ordinary_composition f
    (B₀ := N l E X n) (B₁ := N l E X m) (B₂ := R l E X)
    (D₀ := N l E Y n) (D₁ := N l E Y m) (D₂ := R l E Y)
    (quotientMap l E X h) (quotientMap l E Y h)
    (projection l E X m) (projection l E Y m)
    (projection l E X n) (projection l E Y n)
    (finiteStructure l E f n) (finiteStructure l E f m) C.structureMap
    (C.source.projectionComposition h).ordinary.hom
    (C.target.projectionComposition h).ordinary.hom
    (C.quotientSquare h).ordinary.hom (C.finiteSquare m).ordinary.hom
    (C.finiteSquare n).ordinary.hom
    (C.source.projectionComposition_identity h) (C.target.projectionComposition_identity h)
    (hSQ m n h) (hSN m) (hSN n) M

private theorem projectionCoherence_of_sections {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CoefficientImageData l E f)
    (hSN : ∀ n, IsSectionwiseIdentity Y (R l E Y) (C.finiteSquare n).ordinary.hom)
    (hSQ : ∀ m n (h : n ≤ m),
      IsSectionwiseIdentity Y (N l E Y m) (C.quotientSquare h).ordinary.hom) :
    ∀ {m n : ℕ} (h : n ≤ m) (K : DerivedCategory (Mod X (N l E X n))),
    (C.finiteSquare n).comparison.hom.app K =
      (C.target.projectionComposition h).comparison.inv.app ((C.finiteImage n).functor.obj K) ≫
        (C.target.V m).functor.map ((C.quotientSquare h).comparison.hom.app K) ≫
        (C.finiteSquare m).comparison.hom.app ((C.source.restriction h).functor.obj K) ≫
        C.completedImage.functor.map ((C.source.projectionComposition h).comparison.hom.app K) := by
  intro m n h K
  let : Abelian (Mod X (N l E X n)) := modAbelian.{t, u} X (N l E X n)
  let : Abelian (Mod Y (N l E Y n)) := modAbelian.{t, u} Y (N l E Y n)
  let : Abelian (Mod X (N l E X m)) := modAbelian.{t, u} X (N l E X m)
  let : Abelian (Mod Y (N l E Y m)) := modAbelian.{t, u} Y (N l E Y m)
  let : Abelian (Mod X (R l E X)) := modAbelian.{t, u} X (R l E X)
  let : Abelian (Mod Y (R l E Y)) := modAbelian.{t, u} Y (R l E Y)
  have : Abelian.HasKInjectiveResolutions (Mod X (N l E X n)) :=
    moduleKInjectiveResolutions.{t, u} X (N l E X n)
  have hh := square_composition
    (A₀ := Mod X (N l E X n)) (B₀ := Mod Y (N l E Y n))
    (A₁ := Mod X (N l E X m)) (B₁ := Mod Y (N l E Y m))
    (A₂ := Mod X (R l E X)) (B₂ := Mod Y (R l E Y))
    (push f (finiteStructure l E f n)) (push f (finiteStructure l E f m))
    (SheafOfModules.restrictScalars (quotientMap l E X h))
    (SheafOfModules.restrictScalars (quotientMap l E Y h))
    (C.finiteImage n) (C.finiteImage m) (C.source.restriction h) (C.target.restriction h)
    (push f C.structureMap) (SheafOfModules.restrictScalars (projection l E X m))
    (SheafOfModules.restrictScalars (projection l E Y m))
    C.completedImage (C.source.V m) (C.target.V m)
    (SheafOfModules.restrictScalars (projection l E X n))
    (SheafOfModules.restrictScalars (projection l E Y n))
    (C.source.V n) (C.target.V n)
    (C.source.projectionComposition h) (C.target.projectionComposition h)
    (C.quotientSquare h) (C.finiteSquare m) (C.finiteSquare n)
    (projectionOrdinaryCoherence l E f C hSN hSQ h) K
  have hh' := congrArg (fun z ↦ z ≫
    C.completedImage.functor.map ((C.source.projectionComposition h).comparison.hom.app K)) hh
  simp only [Category.assoc, ← C.completedImage.functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id] at hh'
  erw [Category.comp_id] at hh'
  exact hh'

/-- Constant, finite and quotient coefficient comparisons, with their section identities
and identity, composition and projection coherence. This concerns individual coefficient
categories; it constructs neither a strict-system direct image nor a limit comparison.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, derived pushforward composition;
blueprint fix-prop-adjunctions, Step 1
(blueprint: lem-pur-completed-coefficient-image-comparisons).

Proof: Use c and hc for the completed structural map and its projections. The constant
square is hconstant, and naturality of constant sheafification gives every finite quotient
ring square. Pushforward followed by scalar restriction and scalar restriction followed
by pushforward have the same underlying sections; the ring squares identify their scalar
actions. These identity maps give the ordinary coefficient isomorphisms. Choose total
right derived pushforwards by K-injective resolutions. Scalar restriction of a K-injective
is direct-image acyclic: check the resolution on each slice using scalar-restriction
acyclicity for sections, then use sectionwise detection. Thus both sides of each coefficient
square derive the same ordinary composite. Identify them by uniqueness of total derived
functors, using the factorization isomorphisms of the supplied exact models. The defining
unit equation gives Square.normalization. For an identity or a composite quotient, both proposed
comparisons have the same ordinary section map and induce the same transformation after
precomposition with the universal derived unit. Uniqueness of derived transformations
gives quotientIdentity, quotientCoherence and projectionCoherence. The supplied source
and target models are retained throughout. The argument also applies to identity
quotients and empty sites. -/
theorem coefficientComparisons_exists {X Y : Scheme.{t}} (f : X ⟶ Y)
    (source : SiteData l E X) (target : SiteData l E Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    (hconstant : integralConstantToCompletionOfUniverses l E Y ≫ c =
      constantStructure l E f ≫
        (ringPush.{t, u} f).map (integralConstantToCompletionOfUniverses l E X)) :
    ∃ D : CoefficientComparisonData l E f,
      D.source = source ∧ D.target = target ∧ D.structureMap = c := by
  classical
  obtain ⟨FR, ηR, hR, hIR, -⟩ := CategoryTheory.totalDerivedData (push f c)
  let DR : RightImage (push f c) := ⟨FR, ηR, hR, hIR⟩
  obtain ⟨FA, ηA, hA, hIA, -⟩ :=
    CategoryTheory.totalDerivedData (push f (constantStructure l E f))
  let DA : RightImage (push f (constantStructure l E f)) := ⟨FA, ηA, hA, hIA⟩
  have hn (n : ℕ) : Nonempty (RightImage (push f (finiteStructure l E f n))) := by
    obtain ⟨FN, ηN, hN, hIN, -⟩ :=
      CategoryTheory.totalDerivedData (push f (finiteStructure l E f n))
    exact ⟨⟨FN, ηN, hN, hIN⟩⟩
  let DN (n : ℕ) : RightImage (push f (finiteStructure l E f n)) := Classical.choice (hn n)
  obtain ⟨SA, hSA⟩ := derivedSquare f (constant_comm X _)
    (completedIntegralCoefficient_mul_commUnrestricted l E X)
    (integralConstantToCompletionOfUniverses l E X)
    (integralConstantToCompletionOfUniverses l E Y) (constantStructure l E f) c
    hconstant DR DA source.U target.U
  have hsN (n : ℕ) := derivedSquare f
    (completedIntegralCoefficient_mul_commUnrestricted l E X)
    (constant_comm X _)
    (projection l E X n) (projection l E Y n) c (finiteStructure l E f n)
    (hc n).symm (DN n) DR (source.V n) (target.V n)
  choose SN hSN using hsN
  have hsQ (m n : ℕ) (h : n ≤ m) := derivedSquare f
    (constant_comm X _) (constant_comm X _)
    (quotientMap l E X h) (quotientMap l E Y h)
    (finiteStructure l E f m) (finiteStructure l E f n)
    (finiteStructure_quotient l E f h) (DN n) (DN m)
    (source.restriction h) (target.restriction h)
  choose SQ hSQ using hsQ
  let C : CoefficientImageData l E f :=
    { source := source
      target := target
      structureMap := c
      structureProjection := hc
      completedAdditive := inferInstance
      constantAdditive := inferInstance
      finiteAdditive := fun _ ↦ inferInstance
      completedImage := DR
      constantImage := DA
      finiteImage := DN
      constantSquare := SA
      finiteSquare := SN
      quotientSquare := fun {m n} h ↦ SQ m n h }
  exact ⟨{ toCoefficientImageData := C
           constantOrdinary_identity := hSA
           finiteOrdinary_identity := hSN
           quotientOrdinary_identity := fun {m n} h ↦ hSQ m n h
           quotientIdentity := quotientIdentity_of_sections l E f C hSQ
           quotientCoherence := quotientCoherence_of_sections l E f C hSQ
           projectionCoherence := projectionCoherence_of_sections l E f C hSN hSQ },
    rfl, rfl, rfl⟩

end WeilConjectures.CompletedCoefficientPushforward
