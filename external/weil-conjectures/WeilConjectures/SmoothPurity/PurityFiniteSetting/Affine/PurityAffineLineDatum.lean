/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor

import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement

/-!
# The concrete finite-level affine-line datum

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-affine-line-datum.md
(blueprint: def-pur-affine-line-datum).

The coordinate is an actual global unit on its basic open. The finite twist is the
published root sheaf with scalar extension. The Kummer class is the image of the
published Kummer connecting homomorphism, not an abstract class satisfying naturality.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The relative affine line, with its standard coordinate. Source: blueprint
sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def Line (Y : Scheme.{u}) : Scheme.{u} := AffineSpace (ULift.{u} (Fin 1)) Y

/-- The standard coordinate. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def coordinate (Y : Scheme.{u}) : Γ(Line Y, ⊤) :=
  AffineSpace.coord Y (ULift.up 0)

/-- The actual open complement of the zero section. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def Punctured (Y : Scheme.{u}) : Scheme.{u} :=
  ((Line Y).basicOpen (coordinate Y)).toScheme

/-- Its open immersion into the line. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def openImmersion (Y : Scheme.{u}) : Punctured Y ⟶ Line Y :=
  ((Line Y).basicOpen (coordinate Y)).ι

/-- The zero section. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def zeroSection (Y : Scheme.{u}) : Y ⟶ Line Y :=
  AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y

/-- The affine projection p. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def lineProjection (Y : Scheme.{u}) : Line Y ⟶ Y :=
  (AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y

/-- The punctured projection pi=pj. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def puncturedProjection (Y : Scheme.{u}) : Punctured Y ⟶ Y :=
  openImmersion Y ≫ lineProjection Y

/-- The coordinate is a genuine global unit on Gm. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def coordinateUnit (Y : Scheme.{u}) : Γ(Punctured Y, ⊤)ˣ :=
  (Line Y).basicOpenUnit (coordinate Y)

/-- The coefficient map from roots to the root line is characterized on every section
by z mapping to 1 tensor z. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum).
Proof: the pure-tensor map is additive and natural in etale restriction. Compose it with
the sheafification unit. Sectionwise equality determines a unique sheaf morphism. -/
theorem existsUnique_rootCoefficientMap (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    ∃! f : T.rootsOfUnitySheaf P.exponent ⟶
        (P.forgetEtale T).obj (P.twistEtale h T),
      ∀ (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf P.exponent).obj.obj W),
        f.hom.app W z = Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T
          (P.exponent_coefficient_eq_zero h) W 1 z := by
  refine ⟨Etale.ordinaryFiniteRootMap P.Coefficient P.exponent
    (P.exponent_coefficient_eq_zero h) T, ?_, ?_⟩
  · intro W z
    rfl
  · intro g hg
    apply Sheaf.hom_ext
    ext W z
    exact hg W z

/-- The canonical coefficient extension map, determined uniquely by its pure tensors.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def rootCoefficientMap (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    T.rootsOfUnitySheaf P.exponent ⟶ (P.forgetEtale T).obj (P.twistEtale h T) :=
  Classical.choose (P.existsUnique_rootCoefficientMap h T)

/-- The actual finite Kummer class of any unit, with A-coefficients. The inverse is of
a specified bijection, so the defining boundary determines the class uniquely.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def kummerEtale (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (hr : IsUnit (P.exponent : Γ(T, ⊤))) (t : Γ(T, ⊤)ˣ) :
    Abelian.Ext (P.constantEtale T) (P.twistEtale h T) 1 :=
  Equiv.ofBijective _ (P.moduleClassToAbelian_bijective T (P.twistEtale h T)) |>.symm
    (Sheaf.H.map (P.rootCoefficientMap h T) 1 (T.kummerδ₀ P.exponent hr (Additive.ofMul t)))

/-- The actual class transported to the small pro-etale site.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def kummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (hr : IsUnit (P.exponent : Γ(T, ⊤))) (t : Γ(T, ⊤)ˣ) :
    Abelian.Ext (P.constant T) (P.twist h T) 1 :=
  (P.kummerEtale h T hr t).mapExactFunctor
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)

/-- The inverse image of roots has its canonical map to roots, characterized by the
kernel inclusion into Gm. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum).
Proof: exact inverse image preserves the kernel of multiplication by r. Pullback of
units commutes with the power map. The universal property of the target kernel gives
existence, and its monic inclusion gives uniqueness. -/
theorem existsUnique_rootPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! b : (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
        (Y.rootsOfUnitySheaf P.exponent) ⟶ X.rootsOfUnitySheaf P.exponent,
      b ≫ kernel.ι (P.exponent • 𝟙 X.gmSheaf) =
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map
          (kernel.ι (P.exponent • 𝟙 Y.gmSheaf)) ≫ Scheme.upperStarGmSheafToGmSheaf f := by
  refine ⟨Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent f,
    Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι P.exponent f, ?_⟩
  intro b hb
  apply (cancel_mono (kernel.ι (P.exponent • 𝟙 X.gmSheaf))).1
  exact hb.trans (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι
    P.exponent f).symm

/-- The canonical map on roots, uniquely fixed by the kernel inclusion.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def rootPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
        (Y.rootsOfUnitySheaf P.exponent) ⟶ X.rootsOfUnitySheaf P.exponent :=
  Classical.choose (P.existsUnique_rootPullback f)

/-- Additive maps from the roots are linear over their canonical ZMod action.
Source: blueprint sk-def-purity-conv, scalar extension of roots
(blueprint: def-pur-affine-line-datum). -/
private noncomputable def rootLinearHomEquiv (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (Scheme.finiteEtaleMuModulePresheaf T P.exponent ⟶
      F.obj ⋙ ModuleCat.restrictScalars (Scheme.finiteEtaleTwistScalar P.exponent
        P.Coefficient (P.exponent_coefficient_eq_zero h))) ≃
      (T.rootsOfUnitySheaf P.exponent ⟶ (P.forgetEtale T).obj F) where
  toFun a := ⟨{
    app := fun W ↦ AddCommGrpCat.ofHom (a.app W).hom.toAddMonoidHom
    naturality := by
      intro W V g
      ext z
      exact congrArg (fun k ↦ k z) (a.naturality g) }⟩
  invFun a := {
    app := fun W ↦ by
      letI := AddCommGroup.zmodModule (Scheme.finiteEtaleMu_annihilated T P.exponent W)
      exact ModuleCat.ofHom
        (X := Scheme.finiteEtaleMuModuleObj T P.exponent W)
        (Y := (ModuleCat.restrictScalars (Scheme.finiteEtaleTwistScalar P.exponent
          P.Coefficient (P.exponent_coefficient_eq_zero h))).obj (F.obj.obj W))
        (AddMonoidHom.toZModLinearMap P.exponent
          (M := Scheme.finiteEtaleMuModuleObj T P.exponent W)
          (M₁ := (ModuleCat.restrictScalars (Scheme.finiteEtaleTwistScalar P.exponent
            P.Coefficient (P.exponent_coefficient_eq_zero h))).obj (F.obj.obj W))
          (a.hom.app W).hom)
    naturality := by
      intro W V g
      ext z
      exact congrArg (fun k ↦ k z) (a.hom.naturality g) }
  left_inv a := by ext W z; rfl
  right_inv a := by apply Sheaf.hom_ext; ext W z; rfl

/-- The universal property of the sheafified tensor of roots.
Source: blueprint sk-def-purity-conv, scalar extension of roots
(blueprint: def-pur-affine-line-datum). -/
private noncomputable def rootExtensionEquiv (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (P.twistEtale h T ⟶ F) ≃
      (T.rootsOfUnitySheaf P.exponent ⟶ (P.forgetEtale T).obj F) :=
  ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} P.Coefficient)).homEquiv _ F).trans
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Scheme.finiteEtaleTwistScalar P.exponent P.Coefficient
          (P.exponent_coefficient_eq_zero h))).whiskerRight T.Etaleᵒᵖ).homEquiv _ _)
      |>.trans (rootLinearHomEquiv P h T F)

/-- The scalar-extension adjunction is precomposition with the coefficient generator.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
private theorem rootExtensionEquiv_apply (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (b : P.twistEtale h T ⟶ F) :
    rootExtensionEquiv P h T F b = P.rootCoefficientMap h T ≫ (P.forgetEtale T).map b := by
  apply Sheaf.hom_ext
  ext W z
  have hc : (P.rootCoefficientMap h T).hom.app W z =
      Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T
        (P.exponent_coefficient_eq_zero h) W 1 z :=
    (Classical.choose_spec (P.existsUnique_rootCoefficientMap h T)).1 W z
  dsimp only [forgetEtale] at *
  change _ = b.hom.app W ((P.rootCoefficientMap h T).hom.app W z)
  exact (congrArg (fun x ↦ b.hom.app W x) hc).symm

/-- The forgetting comparison identifies the two inverse-image adjunction mates.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
private theorem rootPullback_mate (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
      (P.twistEtale h Y) ⟶ F) :
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h Y) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h Y) ≫
        (P.forgetEtale X).map b) =
      P.rootCoefficientMap h Y ≫ (P.forgetEtale Y).map
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).homEquiv
          _ _ b) := by
  dsimp only [forgetEtale]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  congr 1
  rw [Adjunction.homEquiv_unit,
    Etale.unit_comp_lowerStar_map_upperStarForget₂Comparison]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-- Pullback of the scalar root line has the universal property of pulled-back roots.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
private noncomputable def pullbackRootExtensionEquiv (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.twistEtale h Y) ⟶ F) ≃
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj (Y.rootsOfUnitySheaf P.exponent) ⟶
        (P.forgetEtale X).obj F) :=
  by
    dsimp only [forgetEtale]
    exact ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).homEquiv (P.twistEtale h Y) F).trans
      ((rootExtensionEquiv P h Y
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).obj F)).trans
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          (Y.rootsOfUnitySheaf P.exponent) ((P.forgetEtale X).obj F)).symm)

/-- The pulled-back universal property is given by the canonical forgetting comparison.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
private theorem pullbackRootExtensionEquiv_apply (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
      (P.twistEtale h Y) ⟶ F) :
    pullbackRootExtensionEquiv P h f F b =
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h Y) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h Y) ≫
        (P.forgetEtale X).map b := by
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
  rw [rootPullback_mate]
  dsimp only [forgetEtale] at *
  dsimp only [pullbackRootExtensionEquiv, id_eq, Equiv.trans_apply]
  erw [Equiv.apply_symm_apply]
  exact rootExtensionEquiv_apply P h Y _ _

/-- The canonical scalar extension of root pullback, uniquely characterized on roots.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: inverse image commutes with the sheafified tensor product. Extend the canonical
map on roots A-linearly. The root image generates its scalar extension locally, giving
uniqueness. The coefficient-forgetting comparison is its canonical adjunction mate. -/
theorem existsUnique_twistEtalePullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
        (P.twistEtale h Y) ⟶ P.twistEtale h X,
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h Y) ≫
          Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h Y) ≫
          (P.forgetEtale X).map b = P.rootPullback f ≫ P.rootCoefficientMap h X := by
  let e := pullbackRootExtensionEquiv P h f (P.twistEtale h X)
  let a := P.rootPullback f ≫ P.rootCoefficientMap h X
  refine ⟨e.symm a, ?_, ?_⟩
  · exact (pullbackRootExtensionEquiv_apply P h f _ (e.symm a)).symm.trans
      (e.apply_symm_apply a)
  · intro b hb
    apply e.injective
    rw [show e b = _ from pullbackRootExtensionEquiv_apply P h f _ b, hb,
      e.apply_symm_apply]

/-- The actual canonical pullback map of the finite root line.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def twistEtalePullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
        (P.twistEtale h Y) ⟶ P.twistEtale h X :=
  Classical.choose (P.existsUnique_twistEtalePullback h f)

/-- The root line commutes with arbitrary inverse image when r is invertible.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: etale locally choose a primitive r-th root. The root sheaf and its scalar
extension become constant Z/r and A; the specified map is the identity on their
standard generators. Hence it is an isomorphism locally, and therefore globally. -/
theorem isIso_twistEtalePullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) : IsIso (P.twistEtalePullback h f) := by
  have hn : NeZero P.exponent :=
    ⟨ne_of_gt (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)⟩
  have hroot : P.rootPullback f =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent f := by
    exact ((Classical.choose_spec (P.existsUnique_rootPullback f)).2 _
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι P.exponent f)).symm
  have hri : IsIso (P.rootPullback f) := by
    rw [hroot]
    exact Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit
      P.exponent f hr
  apply isIso_of_coyoneda_map_bijective
  intro F
  let eX := rootExtensionEquiv P h X F
  let eY := pullbackRootExtensionEquiv P h f F
  have hbij : Function.Bijective (fun a : X.rootsOfUnitySheaf P.exponent ⟶
      (P.forgetEtale X).obj F ↦ P.rootPullback f ≫ a) :=
    (isIso_iff_coyoneda_map_bijective (P.rootPullback f)).1 hri _
  have heq : (fun b : P.twistEtale h X ⟶ F ↦ P.twistEtalePullback h f ≫ b) =
      fun b ↦ eY.symm (P.rootPullback f ≫ eX b) := by
    funext b
    apply eY.injective
    rw [eY.apply_symm_apply]
    change pullbackRootExtensionEquiv P h f F _ = _
    rw [pullbackRootExtensionEquiv_apply, rootExtensionEquiv_apply, Functor.map_comp,
      ← Category.assoc, ← Category.assoc]
    have hs : (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h Y) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h Y) ≫
        (P.forgetEtale X).map (P.twistEtalePullback h f) =
        P.rootPullback f ≫ P.rootCoefficientMap h X :=
      (Classical.choose_spec (P.existsUnique_twistEtalePullback h f)).1
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ (P.forgetEtale X).map b) hs
  rw [heq]
  exact eY.symm.bijective.comp (hbij.comp eX.bijective)

/-- The canonical punctured-line base-change arrow is uniquely determined by its open
immersion. Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: the standard affine-space base-change arrow pulls the coordinate to the
coordinate. Its restriction to the coordinate basic open therefore factors through
the target basic open. The open immersion is monic, giving uniqueness. -/
theorem existsUnique_puncturedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! b : Punctured X ⟶ Punctured Y,
      b ≫ openImmersion Y = openImmersion X ≫ AffineSpace.map (ULift.{u} (Fin 1)) f := by
  have e : (Line X).basicOpen (coordinate X) ≤
      AffineSpace.map (ULift.{u} (Fin 1)) f ⁻¹ᵁ (Line Y).basicOpen (coordinate Y) := by
    dsimp only [Line, coordinate]
    rw [Scheme.preimage_basicOpen_top, AffineSpace.map_appTop_coord]
  refine ⟨(AffineSpace.map (ULift.{u} (Fin 1)) f).resLE _ _ e,
    Scheme.Hom.resLE_comp_ι _ _, ?_⟩
  intro b hb
  apply (cancel_mono ((Line Y).basicOpen (coordinate Y)).ι).1
  exact hb.trans (Scheme.Hom.resLE_comp_ι _ e).symm

/-- The actual punctured-line base-change arrow.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def puncturedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Punctured X ⟶ Punctured Y :=
  Classical.choose (existsUnique_puncturedMap f)

/-- The class of the actual coordinate, transported through the exact site comparison.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def coordinateKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    Abelian.Ext (P.constant (Punctured Y)) (P.twist h (Punctured Y)) 1 :=
  P.kummer h (Punctured Y)
    (P.exponent_isUnit (Punctured Y) (puncturedProjection Y ≫ a)) (coordinateUnit Y)

end WeilConjectures.PurityFiniteSetting
