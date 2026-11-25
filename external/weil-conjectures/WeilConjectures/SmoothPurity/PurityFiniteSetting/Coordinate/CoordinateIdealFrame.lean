/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackFrames
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-! # The global coordinate frame of the affine-line zero ideal

Source: the rank-one paragraph of the current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md
(blueprint: lem-pur-coordinate-ideal-frame).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate open and zero section are complementary.
Source: the affine-line datum (blueprint: lem-pur-coordinate-ideal-frame). -/
theorem coordinateLocalization_complement (T : Scheme.{u}) :
    Set.range (zeroSection T).base = (Set.range (openImmersion T).base)ᶜ := by
  rw [show Set.range (openImmersion T).base = (Set.range (zeroSection T).base)ᶜ from
    AffineSpace.range_basicOpen_ι_coord T, compl_compl]

/-- The coordinate basic open is etale. Source: the affine-line datum
(blueprint: lem-pur-coordinate-ideal-frame). -/
instance coordinateFrameOpenEtale (T : Scheme.{u}) :
    AlgebraicGeometry.Etale (openImmersion T) := by
  dsimp only [openImmersion]
  infer_instance

/-- The coordinate zero section is a closed immersion. Source: the affine-line datum
(blueprint: lem-pur-coordinate-ideal-frame). -/
instance coordinateFrameZeroClosed (T : Scheme.{u}) :
    IsClosedImmersion (zeroSection T) := by
  dsimp only [zeroSection]
  infer_instance

/-- The coordinate itself generates the zero ideal globally, including over a
nonaffine base. This is the frame whose dual is the inverse-coordinate frame.
Source: the rank-one Cartier calculation in the current blueprint
(blueprint: lem-pur-coordinate-ideal-frame).
Proof: the closed subscheme cut out by the coordinate has its inclusion equal to
its projection followed by the zero section, by the affine-space universal
property. Conversely the coordinate vanishes on the zero section. Their kernel
ideal sheaves are therefore equal. The coordinate lifts to the ideal sheaf since
it vanishes on that subscheme. On every affine open its image generates the ideal;
invertibility of the ideal makes this section a free generator. -/
theorem coordinateIdealFrame (T : Scheme.{u}) (hI : (zeroSection T).ker.IsInvertible) :
    ∃ e : Γ((zeroSection T).ker.toModules, ⊤),
      (zeroSection T).ker.toModulesι.app ⊤ e = AffineSpace.coord T (ULift.up (0 : Fin 1)) ∧
      Scheme.Modules.IsFreeGenerator e := by
  let t := AffineSpace.coord T (ULift.up (0 : Fin 1))
  let J : (Line T).IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})
  let j := (Line T).zeroLocusSubschemeι {t}
  have hj : (j ≫ lineProjection T) ≫ zeroSection T = j := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, zeroSection, lineProjection,
        AffineSpace.zeroSection_comp_over, Category.comp_id]
    · intro k
      have hk : k = ULift.up (0 : Fin 1) := Subsingleton.elim _ _
      subst k
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      change (j ≫ lineProjection T).appTop
        ((AffineSpace.zeroSection (ULift.{u} (Fin 1)) T).appTop _) = j.appTop t
      rw [AffineSpace.zeroSection_appTop_coord, map_zero]
      exact (Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton t)).symm
  have hker : (zeroSection T).ker = J := by
    apply le_antisymm
    · calc
        (zeroSection T).ker ≤ ((j ≫ lineProjection T) ≫ zeroSection T).ker :=
          Scheme.Hom.le_ker_comp _ _
        _ = j.ker := congrArg Scheme.Hom.ker hj
        _ = J := Scheme.IdealSheafData.ker_subschemeι J
    · apply Scheme.IdealSheafData.ofIdealTop_span_le_ker
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact AffineSpace.zeroSection_appTop_coord _ _ _
  have ht : t ∈ Set.range ((zeroSection T).ker.toModulesι.app ⊤) := by
    rw [Scheme.IdealSheafData.range_toModulesι_app_eq, hker]
    apply Scheme.IdealSheafData.subschemeι_appTop_eq_zero
    intro V
    change (Line T).presheaf.map (homOfLE le_top).op t ∈
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).ideal V
    rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨e, he⟩ := ht
  refine ⟨e, he, hI.isFreeGenerator e ?_⟩
  intro V hV
  rw [he, hker]
  change (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t})).ideal V = _
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
  rfl

private theorem coordinateDivisorSection_eq (T : Scheme.{u}) :
    Etale.supportedDivisorSection (zeroSection T) =
      (SheafOfModules.homObjUnitIso (unit (Line T))).inv ≫
        dualMap (zeroSection T).ker.toModulesι := by
  ext U x : 3
  change @Eq
    ((PresheafOfModules.restrictOver (Line T).sheaf.obj U).obj
      (zeroSection T).ker.toModules.val ⟶
      (PresheafOfModules.restrictOver (Line T).sheaf.obj U).obj (unit (Line T)).val) _ _
  ext V : 2
  ext y
  change (Line T).presheaf.map V.unop.hom.op x *
      (show Γ(Line T, V.unop.left) from
        ((zeroSection T).ker.toModulesι.val.app (.op V.unop.left)) y) =
    (show Γ(Line T, V.unop.left) from
      ((zeroSection T).ker.toModulesι.val.app (.op V.unop.left)) y) *
      (Line T).presheaf.map V.unop.hom.op x
  exact mul_comm _ _

private theorem coordinateUnitDualConjugation (T : Scheme.{u})
    (f : unit (Line T) ⟶ unit (Line T)) :
    (SheafOfModules.homObjUnitIso (unit (Line T))).inv ≫ dualMap f ≫
      (SheafOfModules.homObjUnitIso (unit (Line T))).hom = f := by
  apply SheafOfModules.hom_ext
  ext V
  change (PresheafOfModules.homObjUnitInvApp (unit (Line T)).val
      (1 : (Line T).ringCatSheaf.obj.obj V)).app
      (.op (Over.mk (𝟙 V.unop))) (f.val.app V (1 : (Line T).ringCatSheaf.obj.obj V)) =
    f.val.app V (1 : (Line T).ringCatSheaf.obj.obj V)
  rw [PresheafOfModules.homObjUnitInvApp_app_apply]
  let a : (Line T).ringCatSheaf.obj.obj V :=
    f.val.app V (1 : (Line T).ringCatSheaf.obj.obj V)
  change a * (Line T).ringCatSheaf.obj.map (𝟙 V)
    (1 : (Line T).ringCatSheaf.obj.obj V) = a
  rw [(Line T).ringCatSheaf.obj.map_id]
  exact mul_one _

/-- The dual coordinate frame has coefficient t in the canonical divisor section.
Source: the rank-one Cartier calculation, e=t inverse and tau=t e
(blueprint: lem-pur-coordinate-ideal-frame).
Proof: the coordinate generator trivializes the ideal. Dualize this isomorphism
and the unit internal-Hom comparison. The dual of the ideal inclusion is the
canonical divisor section; its coefficient in this dual frame is t since the
original inclusion sends the coordinate generator to t. -/
theorem coordinateDualIdealFrame (T : Scheme.{u})
    (hI : (zeroSection T).ker.IsInvertible) :
    ∃ e : unit (Line T) ≅ dual (zeroSection T).ker.toModules,
      Etale.supportedDivisorSection (zeroSection T) =
        smulMor (unit (Line T)) (AffineSpace.coord T (ULift.up (0 : Fin 1))) ≫ e.hom := by
  obtain ⟨e, he, hgen⟩ := coordinateIdealFrame T hI
  let g := homOfGlobalSection (zeroSection T).ker.toModules e
  have : IsIso g := isIso_homOfGlobalSection hgen
  let d : dual (zeroSection T).ker.toModules ≅ dual (unit (Line T)) :=
    (dualFunctor (Line T)).mapIso (asIso g).op
  let E : unit (Line T) ≅ dual (zeroSection T).ker.toModules :=
    (SheafOfModules.homObjUnitIso (unit (Line T))).symm ≪≫ d.symm
  refine ⟨E, ?_⟩
  let t := AffineSpace.coord T (ULift.up (0 : Fin 1))
  have hg : g ≫ (zeroSection T).ker.toModulesι = smulMor (unit (Line T)) t := by
    ext V r
    change (zeroSection T).ker.toModulesι.app V
      ((homOfGlobalSection (zeroSection T).ker.toModules e).app V r) = _
    rw [homOfGlobalSection_app, Hom.app_smul, Hom.app_presheaf_map, he]
    change (show Γ(Line T, V) from r) *
        (Line T).presheaf.map (homOfLE (le_top (a := V))).op t =
      (Line T).presheaf.map (homOfLE (le_top (a := V))).op t *
        (show Γ(Line T, V) from r)
    exact mul_comm _ _
  apply (cancel_mono d.hom).1
  change Etale.supportedDivisorSection (zeroSection T) ≫ dualMap g =
    (smulMor (unit (Line T)) t ≫
      (SheafOfModules.homObjUnitIso (unit (Line T))).inv ≫ d.inv) ≫ d.hom
  rw [Category.assoc, Category.assoc, d.inv_hom_id, Category.comp_id]
  have hd : dualMap (zeroSection T).ker.toModulesι ≫ dualMap g =
      dualMap (g ≫ (zeroSection T).ker.toModulesι) :=
    ((dualFunctor (Line T)).map_comp
      (zeroSection T).ker.toModulesι.op g.op).symm
  rw [coordinateDivisorSection_eq, Category.assoc, hd, hg]
  apply (cancel_mono (SheafOfModules.homObjUnitIso (unit (Line T))).hom).1
  simp only [Category.assoc]
  rw [coordinateUnitDualConjugation, Iso.inv_hom_id, Category.comp_id]

private theorem coordinateDivisorSectionPullback_eq (T : Scheme.{u})
    (W : (Line T).Opens) :
    Etale.supportedDivisorSectionPullback (zeroSection T) W =
      (pullback W.ι).map (Etale.supportedDivisorSection (zeroSection T)) := by
  let e := (Classical.choose (exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (pullbackPushforwardAdjunction W.ι)
  change (e.app _).inv ≫ (tensorPullback W.ι).map
    (Etale.supportedDivisorSection (zeroSection T)) ≫ (e.app _).hom = _
  erw [e.hom.naturality, e.inv_hom_id_app_assoc]

/-- The canonical open Cartier frame is the coordinate acting on a global dual
frame. This supplies the literal framed-torsor input for the Yoneda sign theorem.
Source: the rank-one Cartier calculation in the current blueprint
(blueprint: lem-pur-coordinate-ideal-frame).
Proof: pull back the dual coordinate trivialization to the terminal etale object
and restrict it to the coordinate basic open. Restriction of a pulled-back global
map is its pullback on the smaller object. The torsor action multiplies its source
by the coordinate unit. Pullback of scalar multiplication is scalar multiplication
by the pulled coordinate; the global divisor-section equation then identifies
this frame with the canonical complementary section. -/
theorem coordinateDualTorsorFrame (T : Scheme.{u})
    (hI : (zeroSection T).ker.IsInvertible)
    [SheafOfModules.IsInvertible.{u, u, u} (dual (zeroSection T).ker.toModules)] :
    ∃ (e : (etaleIsoTorsor (X := Line T) (dual (zeroSection T).ker.toModules)).sheaf.obj.obj
        (op (Scheme.Etale.mk (𝟙 (Line T)))))
      (τ : (etaleIsoTorsor (X := Line T) (dual (zeroSection T).ker.toModules)).sheaf.obj.obj
        (op (Scheme.Etale.mk (openImmersion T)))),
      etaleIsoTorsorVal (X := Line T) (dual (zeroSection T).ker.toModules) τ =
        Etale.supportedDivisorSectionPullback (zeroSection T)
          ((Line T).basicOpen (coordinate T)) ∧
      τ = (etaleIsoTorsor (X := Line T) (dual (zeroSection T).ker.toModules)).vadd
        (op (Scheme.Etale.mk (openImmersion T)))
        (ULift.up (Additive.ofMul (coordinateUnit T)))
        ((etaleIsoTorsor (X := Line T) (dual (zeroSection T).ker.toModules)).sheaf.obj.map
          ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Line T)).from
            (Scheme.Etale.mk (openImmersion T))).op e) := by
  obtain ⟨E, hE⟩ := coordinateDualIdealFrame T hI
  let L := dual (zeroSection T).ker.toModules
  let e := etaleIsoTorsorMk L (U := op (Scheme.Etale.mk (𝟙 (Line T))))
    ((pullback (𝟙 (Line T))).map E.hom) inferInstance
  let v := ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Line T)).from
    (Scheme.Etale.mk (openImmersion T))).op
  let eW := (etaleIsoTorsor L).sheaf.obj.map v e
  let g := ULift.up (Additive.ofMul (coordinateUnit T))
  let τ := (etaleIsoTorsor L).vadd (op (Scheme.Etale.mk (openImmersion T))) g eW
  refine ⟨e, τ, ?_, rfl⟩
  have hres : etaleIsoTorsorVal L eW = (pullback (openImmersion T)).map E.hom := by
    change (modulesPseudofunctor.presheafHom (unitObj (Line T)) L).map
      ((Scheme.toProEt (Line T) ⋙ Scheme.ProEt.forget (Line T)).map v.unop).op
      ((pullback (𝟙 (Line T))).map E.hom) = _
    exact pullbackMap_presheaf_map _ _ _ _
  change etaleIsoTorsorVal L τ = _
  rw [etaleIsoTorsorVal_vadd, hres, coordinateDivisorSectionPullback_eq, hE,
    Functor.map_comp]
  congr 1
  exact (pullback_map_smulHom (openImmersion T) (unit (Line T)) _).symm

end WeilConjectures.PurityFiniteSetting
