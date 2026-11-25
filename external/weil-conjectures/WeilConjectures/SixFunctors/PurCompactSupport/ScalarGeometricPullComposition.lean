/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! Scalar extension and the geometric pullback compositor.
(blueprint: lem-sf-scalar-geometric-pull-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local implicit_reducible] pbcDerivedRestrict
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] scalarPull geometricPullComposition
  Functor.leftAdjoint presheafToSheaf

private theorem left_mate_compositor_square
    {A₀ A₁ A₂ N₀ N₁ N₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category N₀] [Category N₁] [Category N₂]
    {P : A₀ ⥤ A₁} {Q : A₁ ⥤ A₀} {P' : A₁ ⥤ A₂} {Q' : A₂ ⥤ A₁}
    {P'' : A₀ ⥤ A₂} {Q'' : A₂ ⥤ A₀}
    {F : N₀ ⥤ N₁} {G : N₁ ⥤ N₀} {F' : N₁ ⥤ N₂} {G' : N₂ ⥤ N₁}
    {F'' : N₀ ⥤ N₂} {G'' : N₂ ⥤ N₀}
    {R₀ : A₀ ⥤ N₀} {R₁ : A₁ ⥤ N₁} {R₂ : A₂ ⥤ N₂}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (a'' : P'' ⊣ Q'')
    (b : F ⊣ G) (b' : F' ⊣ G') (b'' : F'' ⊣ G'')
    (χ : R₀ ⋙ F ⟶ P ⋙ R₁) (χ' : R₁ ⋙ F' ⟶ P' ⋙ R₂)
    (χ'' : R₀ ⋙ F'' ⟶ P'' ⋙ R₂)
    (α : P'' ⟶ P ⋙ P') (β : F'' ⟶ F ⋙ F')
    (h : ∀ X : A₂,
      (mateEquiv a b χ).app (Q'.obj X) ≫
          G.map ((mateEquiv a' b' χ').app X) ≫
          (conjugateEquiv (b.comp b') b'' β).app (R₂.obj X) =
        R₀.map ((conjugateEquiv (a.comp a') a'' α).app X) ≫
          (mateEquiv a'' b'' χ'').app X) :
    (TwoSquare.vComp χ χ').whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ'').whiskerLeft α := by
  apply (mateEquiv (a.comp a') b'').injective
  rw [mateEquiv_conjugateEquiv_vcomp (a.comp a') (b.comp b') b'',
    conjugateEquiv_mateEquiv_vcomp (a.comp a') a'' b'', mateEquiv_hcomp a b a' b']
  apply NatTrans.ext
  funext X
  simpa only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Category.assoc] using h X

private abbrev mate {AY BY AX BX : Type*}
    [Category AY] [Category BY] [Category AX] [Category BX]
    {TY : AY ⥤ BY} {rY : BY ⥤ AY} {TX : AX ⥤ BX} {rX : BX ⥤ AX}
    (dY : TY ⊣ rY) (dX : TX ⊣ rX) {IA : AY ⥤ AX} {IB : BY ⥤ BX}
    (a : rY ⋙ IA ⟶ IB ⋙ rX) : IA ⋙ TX ⟶ TY ⋙ IB :=
  ((mateEquiv dY dX).symm (TwoSquare.mk _ _ _ _ a))

private theorem mate_composition_square
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {T₀ : A₀ ⥤ B₀} {r₀ : B₀ ⥤ A₀} (d₀ : T₀ ⊣ r₀)
    {T₁ : A₁ ⥤ B₁} {r₁ : B₁ ⥤ A₁} (d₁ : T₁ ⊣ r₁)
    {T₂ : A₂ ⥤ B₂} {r₂ : B₂ ⥤ A₂} (d₂ : T₂ ⊣ r₂)
    {gA : A₀ ⥤ A₁} {gB : B₀ ⥤ B₁}
    {fA : A₁ ⥤ A₂} {fB : B₁ ⥤ B₂}
    {hA : A₀ ⥤ A₂} {hB : B₀ ⥤ B₂}
    (cA : gA ⋙ fA ≅ hA) (cB : gB ⋙ fB ≅ hB)
    (ag : r₀ ⋙ gA ⟶ gB ⋙ r₁) (af : r₁ ⋙ fA ⟶ fB ⋙ r₂)
    (ah : r₀ ⋙ hA ⟶ hB ⋙ r₂)
    (ha : ∀ M : B₀, cA.hom.app (r₀.obj M) ≫ ah.app M =
      fA.map (ag.app M) ≫ af.app (gB.obj M) ≫ r₂.map (cB.hom.app M))
    (X : A₀) :
    T₂.map (cA.hom.app X) ≫ (mate d₀ d₂ ah).app X ≫ cB.inv.app (T₀.obj X) =
      (mate d₁ d₂ af).app (gA.obj X) ≫ fB.map ((mate d₀ d₁ ag).app X) := by
  apply (cancel_mono (cB.hom.app (T₀.obj X))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  apply (d₂.homEquiv _ _).injective
  rw [d₂.homEquiv_unit, d₂.homEquiv_unit]
  simp only [Functor.map_comp]
  have uh := unit_mateEquiv_symm d₀ d₂ (TwoSquare.mk _ _ _ _ ah) X
  have uf := unit_mateEquiv_symm d₁ d₂ (TwoSquare.mk _ _ _ _ af) (gA.obj X)
  have ug := unit_mateEquiv_symm d₀ d₁ (TwoSquare.mk _ _ _ _ ag) X
  change hA.map (d₀.unit.app X) ≫ ah.app (T₀.obj X) =
    d₂.unit.app (hA.obj X) ≫ r₂.map ((mate d₀ d₂ ah).app X) at uh
  change fA.map (d₁.unit.app (gA.obj X)) ≫ af.app (T₁.obj (gA.obj X)) =
    d₂.unit.app (fA.obj (gA.obj X)) ≫
      r₂.map ((mate d₁ d₂ af).app (gA.obj X)) at uf
  change gA.map (d₀.unit.app X) ≫ ag.app (T₀.obj X) =
    d₁.unit.app (gA.obj X) ≫ r₁.map ((mate d₀ d₁ ag).app X) at ug
  rw [d₂.unit_naturality_assoc]
  rw [← uh,
    ← reassoc_of% (cA.hom.naturality (d₀.unit.app X)), ha]
  dsimp only [Functor.comp_obj]
  rw [← reassoc_of% uf]
  have hn := af.naturality ((mate d₀ d₁ ag).app X)
  change fA.map (r₁.map ((mate d₀ d₁ ag).app X)) ≫ af.app (gB.obj (T₀.obj X)) =
    af.app (T₁.obj (gA.obj X)) ≫ r₂.map (fB.map ((mate d₀ d₁ ag).app X)) at hn
  rw [← reassoc_of% hn]
  rw [← fA.map_comp_assoc, ug, fA.map_comp]
  simp only [Category.assoc]

private theorem scalarPull_eq_mate {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (scalarPull a g).hom =
      ((mateEquiv (pbcDerivedScalarAdjunction (a.map Y))
        (pbcDerivedScalarAdjunction (a.map X))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedPullback g
          (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
          (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).inv)) := by
  let ar := proEtaleRingDerivedAdjunction g (R.ring Y) (R.ring X) (R.pull g)
  let bs := proEtaleRingDerivedAdjunction g (S.ring Y) (S.ring X) (S.pull g)
  let dx := pbcDerivedScalarAdjunction (a.map X)
  let dy := pbcDerivedScalarAdjunction (a.map Y)
  let t := (proEtaleRingRestrictionDerivedPullback g
    (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
    (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).inv
  let d := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
    (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)
  have hd : (mateEquiv bs ar (TwoSquare.mk _ _ _ _ t)) = d.hom := by
    ext M
    apply (ar.homEquiv _ _).symm.injective
    have hs := (proEtaleRingSheafChangeAdjunction g
      (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
      (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).2.2
      ((proEtaleRingDerivedDirectImage g (S.ring Y) (S.ring X) (S.pull g)).obj M)
      M (bs.counit.app M)
    have hb : (bs.homEquiv _ M) (bs.counit.app M) = 𝟙 _ := by
      rw [← bs.homEquiv_symm_id M]
      exact (bs.homEquiv _ M).apply_symm_apply _
    change (ar.homEquiv _ _) (t.app _ ≫
      (proEtaleRingRestrictScalars (a.map X)).mapDerivedCategory.map
        (bs.counit.app M)) =
      (proEtaleRingRestrictScalars (a.map Y)).mapDerivedCategory.map
        ((bs.homEquiv _ M) (bs.counit.app M)) ≫ d.hom.app M at hs
    rw [hb] at hs
    erw [(proEtaleRingRestrictScalars (a.map Y)).mapDerivedCategory.map_id,
      Category.id_comp] at hs
    conv_lhs => rw [Adjunction.homEquiv_counit, mateEquiv_counit]
    exact (ar.homEquiv _ _).eq_symm_apply.mpr hs
  have hu : (scalarPull a g).hom =
      (conjugateEquiv (dy.comp bs) (ar.comp dx)).symm d.hom := by
    unfold scalarPull
    change (((ar.comp dx).ofNatIsoRight d.symm).leftAdjointUniq (dy.comp bs)).hom = _
    ext M
    simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv_symm_apply_inv,
      conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight_counit]
  rw [hu]
  apply (conjugateEquiv (dy.comp bs) (ar.comp dx)).injective
  rw [Equiv.apply_symm_apply,
    ← iterated_mateEquiv_conjugateEquiv dy dx ar bs]
  rw [Equiv.apply_symm_apply]
  exact hd.symm

private noncomputable def actionIso {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  @asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv g
    (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
    (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g))
    (proEtaleRingRestrictionPullbackInv_isIso g
      (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
      (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g))

private theorem actionIso_derived {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Functor.mapDerivedCategorySquareIso (actionIso a g)).hom =
      (proEtaleRingRestrictionDerivedPullback g
        (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
        (a.map Y) (a.map X) (R.pull g) (S.pull g) (a.square g)).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, actionIso,
    proEtaleRingRestrictionDerivedPullback, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, Iso.symm_hom, Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_symm]
  rfl

/-- Scalar/pullback balancing respects composition of two geometric pullbacks.

Source: Stacks Project, Tags 0D6D and 07A6.
(blueprint: lem-sf-scalar-geometric-pull-composition).
Proof: first take geometric mates of the ordinary inverse-image/restriction
squares. Restriction of scalars does not change sections, so its normalized
comparison with direct image is identity on sections. Both direct-image
compositors restrict sections along the same fibre-product pasting isomorphism.
Their commuting square therefore follows sectionwise. Injectivity of the mate
equivalence gives the ordinary inverse-image square, and exact localization
preserves that square. The coefficient-change adjunction theorem identifies
scalarPull with the scalar-adjunction mate of the localized restriction square.
Pasting scalar mates and cancelling the invertible S-compositor gives the stated
equation. This argument includes identity morphisms and zero objects and does
not assume flatness of the coefficient map: scalar extension is derived
throughout. -/
theorem scalarPull_geometric_composition
    {R S : Coefficients.{u}} (a : Change R S)
    {X Z Y : Scheme.{u}} (h : X ⟶ Z) (k : Z ⟶ Y)
    (hR : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring Y) (R.ring Z) (R.ring X) (R.pull k) (R.pull h))
    (hS : S.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (S.ring Y) (S.ring Z) (S.ring X) (S.pull k) (S.pull h))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map X)).map
        ((geometricPullComposition R h k hR).inv.app L) ≫
      (scalarPull a (h ≫ k)).hom.app L =
    (scalarPull a h).hom.app ((pull R k).obj L) ≫
      (pull S h).map ((scalarPull a k).hom.app L) ≫
      (geometricPullComposition S h k hS).inv.app
        ((pbcDerivedExtend (a.map Y)).obj L) := by
  let rY := proEtaleRingRestrictScalars (a.map Y)
  let rZ := proEtaleRingRestrictScalars (a.map Z)
  let rX := proEtaleRingRestrictScalars (a.map X)
  let pR (U V : Scheme.{u}) (g : U ⟶ V) :=
    proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)
  let pS (U V : Scheme.{u}) (g : U ⟶ V) :=
    proEtaleRingModulePullback g (S.ring V) (S.ring U) (S.pull g)
  let ar (U V : Scheme.{u}) (g : U ⟶ V) :=
    proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g)
  let bs (U V : Scheme.{u}) (g : U ⟶ V) :=
    proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g)
  let dR := (modulePushComposition_existsUnique R h k hR).exists.choose
  let dS := (modulePushComposition_existsUnique S h k hS).exists.choose
  let cR := (conjugateIsoEquiv ((ar Z Y k).comp (ar X Z h))
    (ar X Y (h ≫ k))).symm dR
  let cS := (conjugateIsoEquiv ((bs Z Y k).comp (bs X Z h))
    (bs X Y (h ≫ k))).symm dS
  have ha (M : proEtaleRingModules Y (S.ring Y)) :
      (actionIso a (h ≫ k)).hom.app M ≫ rX.map (cS.hom.app M) =
        cR.hom.app (rY.obj M) ≫ (pR X Z h).map ((actionIso a k).hom.app M) ≫
          (actionIso a h).hom.app ((pS Z Y k).obj M) := by
    have hs := left_mate_compositor_square
      (bs Z Y k) (bs X Z h) (bs X Y (h ≫ k))
      (ar Z Y k) (ar X Z h) (ar X Y (h ≫ k))
      (actionIso a k).hom (actionIso a h).hom (actionIso a (h ≫ k)).hom
      cS.hom cR.hom (by
        intro N
        dsimp only [cR, cS, ar, bs]
        simp only [actionIso, asIso_hom, restrictionPullback_mate,
          ← conjugateIsoEquiv_apply_hom, Equiv.apply_symm_apply]
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro T
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        let σ (U V : Scheme.{u}) (g : U ⟶ V) :=
          proEtaleRingRestrictionDirectImage g
            (R.ring V) (S.ring V) (R.ring U) (S.ring U)
            (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
        have hk := (proEtaleRingRestrictionDirectImage_existsUnique k
          (R.ring Y) (S.ring Y) (R.ring Z) (S.ring Z)
          (a.map Y) (a.map Z) (R.pull k) (S.pull k) (a.square k)).choose_spec.1
        have hh := (proEtaleRingRestrictionDirectImage_existsUnique h
          (R.ring Z) (S.ring Z) (R.ring X) (S.ring X)
          (a.map Z) (a.map X) (R.pull h) (S.pull h) (a.square h)).choose_spec.1
        have hhk := (proEtaleRingRestrictionDirectImage_existsUnique (h ≫ k)
          (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
          (a.map Y) (a.map X) (R.pull (h ≫ k)) (S.pull (h ≫ k))
          (a.square (h ≫ k))).choose_spec.1
        change (dR.hom.app (rX.obj N)).val.app T
            (((σ X Z h).hom.app N).val.app ((proEtaleBaseChange k).op.obj T)
              (((σ Z Y k).hom.app
                ((proEtaleRingModuleDirectImage h
                  (S.ring Z) (S.ring X) (S.pull h)).obj N)).val.app T m)) =
          ((σ X Y (h ≫ k)).hom.app N).val.app T ((dS.hom.app N).val.app T m)
        erw [hk, hh, hhk]
        exact ((modulePushComposition_existsUnique R h k hR).exists.choose_spec
          (rX.obj N) T.unop m).trans
            ((modulePushComposition_existsUnique S h k hS).exists.choose_spec
              N T.unop m).symm)
    have he := congrArg (fun z ↦ z.app M) hs
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using he.symm
  let CR := Functor.mapDerivedCategoryNatIso cR ≪≫
    (Functor.mapDerivedCategoryCompIso (pR Z Y k) (pR X Z h)).symm
  let CS := Functor.mapDerivedCategoryNatIso cS ≪≫
    (Functor.mapDerivedCategoryCompIso (pS Z Y k) (pS X Z h)).symm
  have hd (M : DerivedCategory (proEtaleRingModules Y (S.ring Y))) :=
    Functor.exactSquare_comp_inverse
      (pS Z Y k) (pS X Z h) (pS X Y (h ≫ k))
      (pR Z Y k) (pR X Z h) (pR X Y (h ≫ k)) rY rZ rX
      (actionIso a k) (actionIso a h) (actionIso a (h ≫ k)) cS cR ha M
  have hi (M : DerivedCategory (proEtaleRingModules Y (S.ring Y))) :
      CR.inv.app (rY.mapDerivedCategory.obj M) ≫
          (Functor.mapDerivedCategorySquareIso (actionIso a (h ≫ k))).hom.app M =
        (pR X Z h).mapDerivedCategory.map
            ((Functor.mapDerivedCategorySquareIso (actionIso a k)).hom.app M) ≫
          (Functor.mapDerivedCategorySquareIso (actionIso a h)).hom.app
            ((pS Z Y k).mapDerivedCategory.obj M) ≫
          rX.mapDerivedCategory.map (CS.inv.app M) := by
    have he := congrArg (fun z ↦ CR.inv.app (rY.mapDerivedCategory.obj M) ≫
      z ≫ rX.mapDerivedCategory.map (CS.inv.app M)) (hd M)
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, CR, CS] at he
    erw [rX.mapDerivedCategory.map_id, Category.comp_id] at he
    exact he
  have hm := mate_composition_square
    (pbcDerivedScalarAdjunction (a.map Y))
    (pbcDerivedScalarAdjunction (a.map Z))
    (pbcDerivedScalarAdjunction (a.map X)) CR.symm CS.symm
    (Functor.mapDerivedCategorySquareIso (actionIso a k)).hom
    (Functor.mapDerivedCategorySquareIso (actionIso a h)).hom
    (Functor.mapDerivedCategorySquareIso (actionIso a (h ≫ k))).hom hi L
  dsimp only [pR, pS] at hm
  simp only [mate, actionIso_derived, ← scalarPull_eq_mate, Iso.symm_hom,
    Iso.symm_inv] at hm
  have he := congrArg (fun z ↦ z ≫ CS.inv.app ((pbcDerivedExtend (a.map Y)).obj L)) hm
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [CR, CS, cR, cS, ar, bs, pR, pS, dR, dS,
    geometricPullComposition] using he

end WeilConjectures.PurCompactSupport
