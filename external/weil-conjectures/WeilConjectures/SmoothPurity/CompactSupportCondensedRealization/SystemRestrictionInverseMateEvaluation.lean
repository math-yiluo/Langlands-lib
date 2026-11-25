/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Evaluation of scalar-restriction inverse mates

The generic coefficient-tower argument for the compact-support coefficient comparison.
(blueprint: lem-pur-system-restriction-inverse-mate-evaluation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 256
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CompactSupportCondensedRealization
attribute [local irreducible] constantSheaf Functor.leftAdjoint
section OrdinaryOpenComparison
open SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
private theorem ordinary_coefficient_map_forget_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f) = VaryingRing.ringMap C τ f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map a)
    (eq_of_heq ((coefficientMap_existsUnique C τ f).choose_spec.1 U.unop.1 U.unop.2))

private theorem ordinary_push_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push C τ f = VaryingRing.push C τ f := by
  unfold push VaryingRing.push
  rw [ordinary_coefficient_map_forget_eq]

end OrdinaryOpenComparison

section PullbackIso
attribute [local irreducible] VaryingRing.moduleEvalP SemilinearSections.systemRing
  SemilinearProperOpen.coefficientMap VaryingRing.ringMap
attribute [local implicit_reducible] SemilinearSections.ringPresheaf

private theorem scalarInverseMateEqOfUnit
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {P : B ⥤ A} {F' : C ⥤ D} {P' : D ⥤ C}
    (a : F ⊣ P) (b : F' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    (d : P ⋙ E ⟶ E' ⋙ P') (q : F ⋙ E' ≅ E ⋙ F')
    (hq : ∀ N, E.map (a.unit.app N) ≫ d.app (F.obj N) ≫
      P'.map (q.hom.app N) = b.unit.app (E.obj N)) :
    ((mateEquiv a b).symm d) = q.inv := by
  apply NatTrans.ext
  funext N
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu : E.map (a.unit.app N) ≫ d.app (F.obj N) =
      b.unit.app (E.obj N) ≫ P'.map (((mateEquiv a b).symm d).app N) :=
    unit_mateEquiv_symm a b d N
  rw [← hu]
  apply (cancel_mono (P'.map (q.hom.app N))).mp
  simp only [Category.assoc]
  rw [← P'.map_comp, Iso.inv_hom_id_app]
  exact (hq N).trans ((congrArg (fun z ↦ b.unit.app (E.obj N) ≫ z)
    (P'.map_id _)).trans (Category.comp_id _)).symm

private theorem inverseMateCube
    {A B C D E F H I : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E} {L₄ : H ⥤ I} {R₄ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G : A ⥤ C} {G' : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {J : A ⥤ H} {J' : H ⥤ E} {K : B ⥤ I} {K' : I ⥤ F}
    (α : TwoSquare G L₁ L₂ H₁) (β : TwoSquare G' L₂ L₃ H₂)
    (γ : TwoSquare J L₁ L₄ K) (δ : TwoSquare J' L₄ L₃ K')
    (p : G ⋙ G' ≅ J ⋙ J') (q : H₁ ⋙ H₂ ≅ K ⋙ K')
    (hc : ∀ N : B,
      G'.map ((mateEquiv a₁ a₂ α).app N) ≫
          (mateEquiv a₂ a₃ β).app (H₁.obj N) ≫ R₃.map (q.hom.app N) =
        p.hom.app (R₁.obj N) ≫ J'.map ((mateEquiv a₁ a₄ γ).app N) ≫
          (mateEquiv a₄ a₃ δ).app (K.obj N)) :
    ∀ M : A,
      β.app (G.obj M) ≫ H₂.map (α.app M) ≫ q.hom.app (L₁.obj M) =
        L₃.map (p.hom.app M) ≫ δ.app (J.obj M) ≫ K'.map (γ.app M) := by
  have he :
      ((((TwoSquare.hComp α β).whiskerTop (𝟙 _)).whiskerBottom q.hom)) =
        (((TwoSquare.hComp γ δ).whiskerTop p.hom).whiskerBottom (𝟙 _)) := by
    apply (mateEquiv a₁ a₃).injective
    rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_whiskerTop_whiskerBottom,
      mateEquiv_vcomp a₁ a₂ a₃, mateEquiv_vcomp a₁ a₄ a₃]
    ext N
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
      Category.id_comp, Category.assoc, Functor.comp_obj]
    erw [R₃.map_id]
    simpa only [Category.comp_id, Category.assoc] using hc N
  intro M
  have hm := congrArg (fun z ↦ z.app M) he
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc, CategoryTheory.Functor.map_id,
    TwoSquare.mk, Functor.comp_obj] using hm

section CanonicalEvaluation
attribute [local irreducible] proEtaleRingDirectImageMap proEtaleConstantDirectImageMap
  StrictTower.constantRingIso
attribute [local implicit_reducible] VaryingRing.coefficientTransition

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem level_push_evaluation_local
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : SemilinearProperOpen.Modules C τ X ⥤ SemilinearProperOpen.Modules C τ Y)
    (hF : F = VaryingRing.push C τ f) :
    ∃ d : F ⋙ VaryingRing.eval C τ Y n ≅
        VaryingRing.eval C τ X n ⋙ StrictTower.moduleDirectImage (C n) f,
      (∀ (M : SemilinearProperOpen.Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.hom.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) ∧
      d = eqToIso (congrArg (fun T ↦ T ⋙ VaryingRing.eval C τ Y n) hF) ≪≫
        VaryingRing.moduleEvalP C τ f n := by
  subst F
  refine ⟨VaryingRing.moduleEvalP C τ f n, ?_, ?_⟩
  · intro M U
    apply heq_of_eq
    funext x
    unfold VaryingRing.moduleEvalP
    exact (VaryingRing.moduleEvalP_existsUnique C τ f n).choose_spec.1 M U x
  · simp only [eqToIso_refl, Iso.refl_trans]

end CanonicalEvaluation

private theorem single_evaluation_inverse_isIso
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : VaryingRing.Modules C τ X ⥤ VaryingRing.Modules C τ Y) [P.IsRightAdjoint]
    (hP : P = VaryingRing.push C τ f)
    (d : P ⋙ VaryingRing.eval C τ Y n ≅
      VaryingRing.eval C τ X n ⋙ StrictTower.moduleDirectImage (C n) f)
    (hd : d = eqToIso (congrArg (fun T ↦ T ⋙ VaryingRing.eval C τ Y n) hP) ≪≫
      VaryingRing.moduleEvalP C τ f n) :
    IsIso (((mateEquiv (Adjunction.ofIsRightAdjoint P)
      (proEtaleRingModuleAdjunction f (VaryingRing.coefficients C Y n)
        (VaryingRing.coefficients C X n) (StrictTower.constantRingIso (C n) f))).symm
          (TwoSquare.mk _ _ _ _ d.hom))) := by
  subst P
  simp only [eqToIso_refl, Iso.refl_trans] at hd
  subst d
  have hm := scalarInverseMateEqOfUnit (VaryingRing.moduleAdj C τ f)
    (proEtaleRingModuleAdjunction f (VaryingRing.coefficients C Y n)
      (VaryingRing.coefficients C X n) (StrictTower.constantRingIso (C n) f))
    (VaryingRing.eval C τ Y n) (VaryingRing.eval C τ X n)
    (VaryingRing.moduleEvalP C τ f n).hom (VaryingRing.moduleEvalG C τ f n)
    (VaryingRing.moduleEvalG_existsUnique C τ f n).choose_spec.1
  change IsIso (((mateEquiv (VaryingRing.moduleAdj C τ f) _).symm
    (VaryingRing.moduleEvalP C τ f n).hom))
  exact (congrArg IsIso hm).mpr inferInstance

private theorem normalized_six_functions
    {A B C D E F I : Type u} (hA : A = I) (hB : B = I) (hC : C = I)
    (hD : D = I) (hE : E = I) (hF : F = I)
    {a : A → B} {b : B → C} {c : C → D} {d : A → E} {e : E → F} {f : F → D}
    (ha : HEq a (id : I → I)) (hb : HEq b (id : I → I))
    (hc : HEq c (id : I → I)) (hd : HEq d (id : I → I))
    (he : HEq e (id : I → I)) (hf : HEq f (id : I → I)) :
    (fun x ↦ c (b (a x))) = (fun x ↦ f (e (d x))) := by
  subst A B C D E F
  rw [eq_of_heq ha, eq_of_heq hb, eq_of_heq hc, eq_of_heq hd,
    eq_of_heq he, eq_of_heq hf]

private theorem identity_heq {A B : Type u} (h : A = B) :
    HEq (id : A → A) (id : B → B) := by subst B; rfl

private theorem eval_section_type
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (X : Scheme.{u}) (n : ℕ) (M : VaryingRing.Modules C τ X) (U : X.ProEtᵒᵖ) :
    (((VaryingRing.eval C τ X n).obj M).val.obj U : Type (u + 1)) =
      (M.val.obj (op (n, U.unop)) : Type (u + 1)) := rfl

private theorem eval_map_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (X : Scheme.{u}) (n : ℕ) {M N : VaryingRing.Modules C τ X} (g : M ⟶ N)
    (U : X.ProEtᵒᵖ) :
    HEq (fun x ↦ (((VaryingRing.eval C τ X n).map g).val.app U) x)
      (fun x ↦ (g.val.app (op (n, U.unop))) x) := HEq.rfl

private theorem push_section_type
    (C : CommRingCat.{u + 1}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : StrictTower.Modules C X) (U : Y.ProEtᵒᵖ) :
    (((StrictTower.moduleDirectImage C f).obj M).val.obj U : Type (u + 1)) =
      (M.val.obj ((proEtaleBaseChange f).op.obj U) : Type (u + 1)) := rfl

private theorem push_map_heq
    (C : CommRingCat.{u + 1}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : StrictTower.Modules C X} (g : M ⟶ N) (U : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ (((StrictTower.moduleDirectImage C f).map g).val.app U) x)
      (fun x ↦ (g.val.app ((proEtaleBaseChange f).op.obj U)) x) := HEq.rfl

private theorem ordinary_push_section_type
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : SemilinearProperOpen.Modules C τ X)
    (U : (ℕ × Y.ProEt)ᵒᵖ) :
    (((SemilinearProperOpen.push C τ f).obj M).val.obj U : Type (u + 1)) =
      (M.val.obj ((SemilinearProperOpen.siteMap f).op.obj U) : Type (u + 1)) := rfl

private theorem res_section_type {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : SemilinearSections.Mod (ProEt.topology X) S) (U : X.ProEtᵒᵖ) :
    (((SemilinearSections.res a).obj M).val.obj U : Type (u + 1)) =
      (M.val.obj U : Type (u + 1)) := rfl

private theorem res_map_heq {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : SemilinearSections.Mod (ProEt.topology X) S} (g : M ⟶ N) (U : X.ProEtᵒᵖ) :
    HEq (fun x ↦ (((SemilinearSections.res a).map g).val.app U) x)
      (fun x ↦ (g.val.app U) x) := HEq.rfl

private theorem fixed_push_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (comm : cR.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)
    (M : proEtaleRingModules X SX) (U : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ ((proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cR cS comm).hom.app
      M).val.app U x) (fun x : M.val.obj ((proEtaleBaseChange f).op.obj U) ↦ x) :=
  heq_of_eq (funext ((proEtaleRingRestrictionDirectImage_existsUnique f RY SY RX SX
    aY aX cR cS comm).choose_spec.1 M U))

universe siteObj siteHom ringSize

private theorem res_section_type_general
    {C : Type siteObj} [Category.{siteHom} C] [EssentiallySmall.{ringSize} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{ringSize}} (a : R ⟶ S)
    (M : SemilinearSections.Mod J S) (U : Cᵒᵖ) :
    (((SemilinearSections.res a).obj M).val.obj U : Type ringSize) =
      (M.val.obj U : Type ringSize) := rfl

-- Elaborate the six normalized section maps and their adjunction mate cube together.
/-- The inverse mate of normalized scalar restriction commutes with geometric pullback
at every coefficient level. Source: blueprint theorem-smooth-purity-all-admissible-coefficients,
Step 10; Stacks 03EK. (blueprint: lem-pur-system-restriction-inverse-mate-evaluation).
Proof: the six sectionwise identity comparisons form a commuting direct-image cube.
Taking mates gives the inverse-image cube. The canonical evaluation comparisons and
fixed-ring scalar pullback comparison are invertible, so cancellation proves the claim. -/
theorem restriction_inverse_mate_eval_isIso
    (CE CF : ℕ → CommRingCat.{u + 1})
    (τE : ∀ n, CE (n + 1) ⟶ CE n) (τF : ∀ n, CF (n + 1) ⟶ CF n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (rX : SemilinearProperOpen.ringSystem CE τE X ⟶
      SemilinearProperOpen.ringSystem CF τF X)
    (rY : SemilinearProperOpen.ringSystem CE τE Y ⟶
      SemilinearProperOpen.ringSystem CF τF Y)
    (aX : VaryingRing.coefficients CE X n ⟶ VaryingRing.coefficients CF X n)
    (aY : VaryingRing.coefficients CE Y n ⟶ VaryingRing.coefficients CF Y n)
    (hs : (StrictTower.constantRingIso (CE n) f).hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫
        (StrictTower.constantRingIso (CF n) f).hom)
    (d : SemilinearSections.res rX ⋙ SemilinearProperOpen.push CE τE f ≅
      SemilinearProperOpen.push CF τF f ⋙ SemilinearSections.res rY)
    (hd : ∀ (N : VaryingRing.Modules CF τF X) (U : (ℕ × Y.ProEt)ᵒᵖ)
      (x : ((SemilinearSections.res rX ⋙ SemilinearProperOpen.push CE τE f).obj N).val.obj U),
      HEq ((d.hom.app N).val.app U x) x)
    (eX : SemilinearSections.res rX ⋙ VaryingRing.eval CE τE X n ≅
      VaryingRing.eval CF τF X n ⋙ SemilinearSections.res aX)
    (heX : ∀ (N : VaryingRing.Modules CF τF X) (U : X.ProEtᵒᵖ),
      HEq (fun x ↦ (eX.hom.app N).val.app U x)
        (fun x : N.val.obj (op (n, U.unop)) ↦ x))
    (eY : SemilinearSections.res rY ⋙ VaryingRing.eval CE τE Y n ≅
      VaryingRing.eval CF τF Y n ⋙ SemilinearSections.res aY)
    (heY : ∀ (N : VaryingRing.Modules CF τF Y) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (eY.hom.app N).val.app U x)
        (fun x : N.val.obj (op (n, U.unop)) ↦ x))
    (M : VaryingRing.Modules CF τF Y) :
    IsIso ((VaryingRing.eval CE τE X n).map
      ((((mateEquiv (SemilinearProperOpen.ordinaryAdj CF τF f)
        (SemilinearProperOpen.ordinaryAdj CE τE f)).symm
          (TwoSquare.mk _ _ _ _ d.inv))).app M)) := by
  let adjE := SemilinearProperOpen.ordinaryAdj CE τE f
  let adjF := SemilinearProperOpen.ordinaryAdj CF τF f
  let t := ((mateEquiv adjF adjE).symm (TwoSquare.mk _ _ _ _ d.inv))
  change IsIso ((VaryingRing.eval CE τE X n).map (t.app M))
  let aE := proEtaleRingModuleAdjunction f (VaryingRing.coefficients CE Y n)
    (VaryingRing.coefficients CE X n) (StrictTower.constantRingIso (CE n) f)
  let aF := proEtaleRingModuleAdjunction f (VaryingRing.coefficients CF Y n)
    (VaryingRing.coefficients CF X n) (StrictTower.constantRingIso (CF n) f)
  obtain ⟨dE, hdE, hcE⟩ := level_push_evaluation_local
    CE τE n f (SemilinearProperOpen.push CE τE f) (ordinary_push_eq CE τE f)
  obtain ⟨dF, hdF, hcF⟩ := level_push_evaluation_local
    CF τF n f (SemilinearProperOpen.push CF τF f) (ordinary_push_eq CF τF f)
  let bE := ((mateEquiv adjE aE).symm (TwoSquare.mk _ _ _ _ dE.hom))
  let bF := ((mateEquiv adjF aF).symm (TwoSquare.mk _ _ _ _ dF.hom))
  have : (SemilinearProperOpen.push CE τE f).IsRightAdjoint :=
    SemilinearProperOpen.push_isRightAdjoint CE τE f
  have : (SemilinearProperOpen.push CF τF f).IsRightAdjoint :=
    SemilinearProperOpen.push_isRightAdjoint CF τF f
  have : IsIso bE := single_evaluation_inverse_isIso CE τE f n _
    (ordinary_push_eq CE τE f) dE hcE
  have : IsIso bF := single_evaluation_inverse_isIso CF τF f n _
    (ordinary_push_eq CF τF f) dF hcF
  let b := proEtaleRingRestrictionPullbackInv f
    (VaryingRing.coefficients CE Y n) (VaryingRing.coefficients CF Y n)
    (VaryingRing.coefficients CE X n) (VaryingRing.coefficients CF X n)
    aY aX (StrictTower.constantRingIso (CE n) f) (StrictTower.constantRingIso (CF n) f) hs
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  have hdinv (N : VaryingRing.Modules CF τF X) (U : (ℕ × Y.ProEt)ᵒᵖ) :
      HEq (fun x ↦ (d.inv.app N).val.app U x)
        (fun x : ((SemilinearProperOpen.push CF τF f ⋙ SemilinearSections.res rY).obj
          N).val.obj U ↦ x) := by
    apply heq_of_eq
    funext x
    have hh := congrArg (fun z ↦ z.val.app U x) (d.inv_hom_id_app N)
    have ht := eq_of_heq
      (hd N U ((d.inv.app N).val.app U x))
    exact ht.symm.trans hh
  have hc (N : VaryingRing.Modules CF τF X) :
      (VaryingRing.eval CE τE Y n).map (d.inv.app N) ≫
          dE.hom.app ((SemilinearSections.res rX).obj N) ≫
          (StrictTower.moduleDirectImage (CE n) f).map (eX.hom.app N) =
        eY.hom.app ((SemilinearProperOpen.push CF τF f).obj N) ≫
          (SemilinearSections.res aY).map (dF.hom.app N) ≫
          (proEtaleRingRestrictionDirectImage f
            (VaryingRing.coefficients CE Y n) (VaryingRing.coefficients CF Y n)
            (VaryingRing.coefficients CE X n) (VaryingRing.coefficients CF X n)
            aY aX (StrictTower.constantRingIso (CE n) f)
            (StrictTower.constantRingIso (CF n) f) hs).hom.app
              ((VaryingRing.eval CF τF X n).obj N) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    let V := (proEtaleBaseChange f).op.obj U
    let dS := proEtaleRingRestrictionDirectImage f
      (VaryingRing.coefficients CE Y n) (VaryingRing.coefficients CF Y n)
      (VaryingRing.coefficients CE X n) (VaryingRing.coefficients CF X n)
      aY aX (StrictTower.constantRingIso (CE n) f)
      (StrictTower.constantRingIso (CF n) f) hs
    have hA := (eval_section_type CE τE Y n
      ((SemilinearSections.res rY).obj ((SemilinearProperOpen.push CF τF f).obj N)) U).trans
        ((res_section_type_general _ rY _ (op (n, U.unop))).trans
          (ordinary_push_section_type CF τF f N (op (n, U.unop))))
    have hB := (eval_section_type CE τE Y n
      ((SemilinearProperOpen.push CE τE f).obj ((SemilinearSections.res rX).obj N)) U).trans
        ((ordinary_push_section_type CE τE f _ (op (n, U.unop))).trans
          (res_section_type_general _ rX N (op (n, V.unop))))
    have hC := (push_section_type (CE n) f
      ((VaryingRing.eval CE τE X n).obj ((SemilinearSections.res rX).obj N)) U).trans
        ((eval_section_type CE τE X n _ V).trans
          (res_section_type_general _ rX N (op (n, V.unop))))
    have hD := (push_section_type (CE n) f
      ((SemilinearSections.res aX).obj ((VaryingRing.eval CF τF X n).obj N)) U).trans
        ((res_section_type aX _ V).trans (eval_section_type CF τF X n N V))
    have hE := (res_section_type aY
      ((VaryingRing.eval CF τF Y n).obj ((SemilinearProperOpen.push CF τF f).obj N)) U).trans
        ((eval_section_type CF τF Y n _ U).trans
          (ordinary_push_section_type CF τF f N (op (n, U.unop))))
    have hF := (res_section_type aY
      ((StrictTower.moduleDirectImage (CF n) f).obj
        ((VaryingRing.eval CF τF X n).obj N)) U).trans
          ((push_section_type (CF n) f _ U).trans (eval_section_type CF τF X n N V))
    have ha := (eval_map_heq CE τE Y n (d.inv.app N) U).trans
      ((hdinv N (op (n, U.unop))).trans
        (identity_heq ((res_section_type_general _ rY _ (op (n, U.unop))).trans
          (ordinary_push_section_type CF τF f N (op (n, U.unop))))))
    have hb := (hdE ((SemilinearSections.res rX).obj N) U.unop).trans
      (identity_heq (res_section_type_general _ rX N (op (n, V.unop))))
    have hc := (push_map_heq (CE n) f (eX.hom.app N) U).trans (heX N V)
    have hd := (heY ((SemilinearProperOpen.push CF τF f).obj N) U).trans
      (identity_heq (ordinary_push_section_type CF τF f N (op (n, U.unop))))
    have he := (res_map_heq aY (dF.hom.app N) U).trans (hdF N U.unop)
    have hf := (fixed_push_normalized f
      (VaryingRing.coefficients CE Y n) (VaryingRing.coefficients CF Y n)
      (VaryingRing.coefficients CE X n) (VaryingRing.coefficients CF X n)
      aY aX (StrictTower.constantRingIso (CE n) f)
      (StrictTower.constantRingIso (CF n) f) hs
        ((VaryingRing.eval CF τF X n).obj N) U).trans
          (identity_heq (eval_section_type CF τF X n N V))
    have hh := normalized_six_functions hA hB hC hD hE hF ha hb hc hd he hf
    ext x
    exact congrFun hh x
  have h := inverseMateCube adjF adjE aE aF
    (TwoSquare.mk _ _ _ _ (t))
    (TwoSquare.mk _ _ _ _ bE) (TwoSquare.mk _ _ _ _ bF)
    (TwoSquare.mk _ _ _ _ b) eY eX (by
      intro N
      have h₁ := Equiv.apply_symm_apply (mateEquiv adjF adjE)
        (TwoSquare.mk _ _ _ _ d.inv)
      have h₂ := Equiv.apply_symm_apply (mateEquiv adjE aE)
        (TwoSquare.mk _ _ _ _ dE.hom)
      have h₃ := Equiv.apply_symm_apply (mateEquiv adjF aF)
        (TwoSquare.mk _ _ _ _ dF.hom)
      have h₄ := restrictionPullback_mate f
        (VaryingRing.coefficients CE Y n) (VaryingRing.coefficients CF Y n)
        (VaryingRing.coefficients CE X n) (VaryingRing.coefficients CF X n)
        aY aX (StrictTower.constantRingIso (CE n) f)
        (StrictTower.constantRingIso (CF n) f) hs
      have h₁' : (mateEquiv adjF adjE
          (TwoSquare.mk _ _ _ _ (t))) =
          d.inv := by
        dsimp only [t]
        exact h₁
      have h₂' : (mateEquiv adjE aE (TwoSquare.mk _ _ _ _ bE)) =
          dE.hom := h₂
      have h₃' : (mateEquiv adjF aF (TwoSquare.mk _ _ _ _ bF)) =
          dF.hom := h₃
      exact (congrArg₂ (fun a c ↦ (VaryingRing.eval CE τE Y n).map a ≫ c ≫
        (StrictTower.moduleDirectImage (CE n) f).map (eX.hom.app N))
          (congr_app h₁' N) (congr_app h₂' ((SemilinearSections.res rX).obj N))).trans
        ((hc N).trans (congrArg₂ (fun a c ↦
          eY.hom.app ((SemilinearProperOpen.push CF τF f).obj N) ≫
            (SemilinearSections.res aY).map a ≫ c)
              (congr_app h₃' N)
              (congr_app h₄ ((VaryingRing.eval CF τF X n).obj N))).symm)) M
  have hR : IsIso ((StrictTower.modulePullback (CE n) f).map (eY.hom.app M) ≫
      b.app ((VaryingRing.eval CF τF Y n).obj M) ≫
        (SemilinearSections.res aX).map (bF.app M)) := by infer_instance
  have hL : IsIso (bE.app ((SemilinearSections.res rY).obj M) ≫
      (VaryingRing.eval CE τE X n).map ((t).app M) ≫
        eX.hom.app ((SemilinearProperOpen.pull CF τF f).obj M)) := by
    rw [h]
    exact hR
  have : IsIso ((VaryingRing.eval CE τE X n).map
      ((t).app M) ≫
        eX.hom.app ((SemilinearProperOpen.pull CF τF f).obj M)) :=
    IsIso.of_isIso_comp_left (bE.app ((SemilinearSections.res rY).obj M)) _
  exact IsIso.of_isIso_comp_right _
    (eX.hom.app ((SemilinearProperOpen.pull CF τF f).obj M))

end PullbackIso
end WeilConjectures.CompactSupportCondensedRealization
