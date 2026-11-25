/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The ordinary quotient-system tensor and its inverse-limit adjunction

Source: Stacks 03D7, 03EK, 0940 and 0941.

The strict quotient system of a completed-coefficient module is the system of its
scalar extensions to the finite quotients. It is left adjoint to restriction of
coefficients followed by inverse limit. This file records that ordinary adjunction
together with its normalizations, independently of any derived coefficient calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! ### Generic scalar-extension transition comparisons

The following auxiliary statements are the generic transition comparison for the
sequence-site scalar models (Stacks 03D7, 03EK).
-/

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

section Generic
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory
namespace WeilConjectures.OrdinaryQuotient
open SemilinearSections

private theorem restriction_map_apply
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S) {M N : SheafOfModules.{r} S}
    (f : M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((SheafOfModules.restrictScalars φ).map f).val.app V x = f.val.app V x := rfl

private theorem restriction_composition_cast_apply
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (h : SheafOfModules.restrictScalars g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars k)
    (M : SheafOfModules.{r} T) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((eqToIso h).inv.app M).val.app V x = x := by
  let U := SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{r} ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{r}).obj V
  have he : U.map ((eqToIso h).inv.app M) = 𝟙 _ := by
    simp only [eqToIso.inv, eqToHom_app, eqToHom_map]
    rfl
  exact ConcreteCategory.congr_hom he x

private theorem quotient_mate_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {S : B ⥤ A} (adj : F ⊣ S)
    {F' : A ⥤ D} {S' : D ⥤ A} (adj' : F' ⊣ S')
    (U : D ⥤ B) (e : U ⋙ S ≅ S') (M : A) :
    adj.unit.app M ≫ S.map ((coefficientQuotientNatTrans adj adj' U e).app M) =
      adj'.unit.app M ≫ e.inv.app (F'.obj M) := by
  change adj.homEquiv M _ ((coefficientQuotientNatTrans adj adj' U e).app M) = _
  exact Equiv.apply_symm_apply _ _

private theorem quotient_mate_unit_of_eq
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {S : B ⥤ A} (adj : F ⊣ S)
    {F' : A ⥤ D} {S' : D ⥤ A} (adj' : F' ⊣ S')
    (U : D ⥤ B) (e : U ⋙ S ≅ S') (M : A)
    (q : F.obj M ⟶ U.obj (F'.obj M))
    (hq : q = (coefficientQuotientNatTrans adj adj' U e).app M) :
    adj.unit.app M ≫ S.map q = adj'.unit.app M ≫ e.inv.app (F'.obj M) := by
  subst q
  exact quotient_mate_unit adj adj' U e M

private theorem module_nat_iso_comp_apply
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {D : Type*} [Category D]
    {F G H : D ⥤ SheafOfModules.{r} R} (e : F ≅ G) (f : G ≅ H)
    (M : D) (V : Cᵒᵖ) (x : (F.obj M).val.obj V) :
    (((e ≪≫ f).hom.app M).val.app V) x =
      (f.hom.app M).val.app V ((e.hom.app M).val.app V x) := rfl

private theorem module_unit_sections_of_eq
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (h : SheafOfModules.restrictScalars g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars k)
    {M : SheafOfModules.{r} R} {Q : SheafOfModules.{r} S} {Q' : SheafOfModules.{r} T}
    (u : M ⟶ (SheafOfModules.restrictScalars f).obj Q)
    (v : M ⟶ (SheafOfModules.restrictScalars k).obj Q')
    (q : Q ⟶ (SheafOfModules.restrictScalars g).obj Q')
    (hu : u ≫ (SheafOfModules.restrictScalars f).map q = v ≫ (eqToIso h).inv.app Q')
    (V : Cᵒᵖ) (x : M.val.obj V) : q.val.app V (u.val.app V x) = v.val.app V x := by
  have hv := congrArg (fun f ↦ f.val.app V x) hu
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
  erw [restriction_map_apply] at hv
  exact hv.trans (restriction_composition_cast_apply f g k h Q' V (v.val.app V x))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_comparison_unit_abstract
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (A : SheafOfModules.SystemScalarModel φ) {F : Mod J R ⥤ Mod J S}
    (ad : F ⊣ res φ) (M : Mod J R) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((A.ordinaryAdj.leftAdjointUniq ad).hom.app M).val.app V
      (SheafOfModules.systemModelTmul A.model M V 1 x) = (ad.unit.app M).val.app V x := by
  have hu := congrArg (fun f ↦ f.val.app V x)
    (Adjunction.unit_leftAdjointUniq_hom_app A.ordinaryAdj ad M)
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hu
  rw [A.unit_normalized] at hu
  exact hu

private theorem module_iso_inv_hom_sections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {X Y : SheafOfModules.{r} R}
    (e : X ≅ Y) (V : Cᵒᵖ) (x : Y.val.obj V) :
    e.hom.val.app V (e.inv.val.app V x) = x := by
  have hh := congrArg (fun f ↦ f.val.app V x) e.inv_hom_id
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar-extension adjoint comparisons preserve a transition which preserves unit tensors.
Source: Stacks 03D7 and 03EK (blueprint: lem-pur-system-scalar-transition-comparison).
Proof: precompose with the inverse model comparison. Scalar-extension Hom
extensionality reduces equality to unit tensors. Both left-adjoint uniqueness
comparisons preserve the adjunction units. The defining quotient mate has the
same unit equation, and scalar restriction leaves every underlying section map
unchanged. The two maps therefore agree on all local generators. -/
private theorem systemScalarTransitionComparison
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S T : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (ψ : R ⟶ T)
    (A : SheafOfModules.SystemScalarModel φ) (B : SheafOfModules.SystemScalarModel ψ)
    {Fm : Mod J R ⥤ Mod J S} (am : Fm ⊣ res φ)
    {Fn : Mod J R ⥤ Mod J T} (an : Fn ⊣ res ψ)
    {Xm : Mod J R ⥤ Mod J S} {Xn : Mod J R ⥤ Mod J T}
    (em : Xm ≅ A.model.E) (en : Xn ≅ B.model.E) (M : Mod J R)
    (g : ring J S ⟶ ring J T)
    (e : SheafOfModules.restrictScalars g ⋙ res φ = res ψ)
    (δ : Xm.obj M ⟶ (SheafOfModules.restrictScalars g).obj (Xn.obj M))
    (hδ : ∀ (V : Cᵒᵖ) (x : M.val.obj V),
      (en.hom.app M).val.app V (δ.val.app V ((em.inv.app M).val.app V
        (SheafOfModules.systemModelTmul A.model M V 1 x))) =
          SheafOfModules.systemModelTmul B.model M V 1 x)
    (q : Fm.obj M ⟶ (SheafOfModules.restrictScalars g).obj (Fn.obj M))
    (hq : q = (coefficientQuotientNatTrans am an
      (SheafOfModules.restrictScalars g) (eqToIso e)).app M) :
    δ ≫ (SheafOfModules.restrictScalars g).map
      ((en ≪≫ B.ordinaryAdj.leftAdjointUniq an).hom.app M) =
        ((em ≪≫ A.ordinaryAdj.leftAdjointUniq am).hom.app M) ≫ q := by
  apply (cancel_epi (em.inv.app M)).mp
  apply SheafOfModules.systemScalarModel_hom_ext A M _
  intro V x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [restriction_map_apply]
  erw [module_nat_iso_comp_apply en (B.ordinaryAdj.leftAdjointUniq an) M V]
  rw [hδ V x, scalar_comparison_unit_abstract J ψ B an M V x]
  erw [module_nat_iso_comp_apply em (A.ordinaryAdj.leftAdjointUniq am) M V]
  erw [module_iso_inv_hom_sections (em.app M) V,
    scalar_comparison_unit_abstract J φ A am M V x]
  exact (module_unit_sections_of_eq
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ) g
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map ψ)
    e (am.unit.app M) (an.unit.app M) q
    (quotient_mate_unit_of_eq am an (SheafOfModules.restrictScalars g)
      (eqToIso e) M q hq) V x).symm

private theorem unit_iso_cancel
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y Z : A} {M : B} (u : M ⟶ F.obj X) (e : X ≅ Y) (f : Z ≅ Y) :
    u ≫ F.map e.hom ≫ F.map f.inv ≫ F.map f.hom ≫ F.map e.inv = u := by
  rw [← F.map_comp_assoc f.inv f.hom, Iso.inv_hom_id, F.map_id, Category.id_comp,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id]

private theorem unit_evaluation
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) (n : ℕ) :
    (seqModuleAdjunction J B τ b).unit.app M ≫
      limit.π ((seqRestriction J B τ b).obj ((seqExtension J B τ b).obj M)) (op n) ≫
      (res (b.π.app (op n))).map
        ((seqEvaluationIso J B τ n).inv.app ((seqExtension J B τ b).obj M)) ≫
      (res (b.π.app (op n))).map ((seqOrdinaryEvaluation J B τ b n).hom.app M) =
        (seqScalar J B τ b n).ordinaryAdj.unit.app M := by
  rw [← Category.assoc, ← Category.assoc, seqUnitMorphism]
  simp only [seqOrdinaryEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  change (seqScalar J B τ b n).ordinaryAdj.unit.app M ≫
    (res (b.π.app (op n))).map
      (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ)
        ((SheafOfModules.SequenceProjection.extension b.pt (rings J B τ) b.π).obj M) n).hom ≫
    (res (b.π.app (op n))).map
      ((seqEvaluationIso J B τ n).inv.app ((seqExtension J B τ b).obj M)) ≫
    (res (b.π.app (op n))).map
      ((seqEvaluationIso J B τ n).hom.app ((seqExtension J B τ b).obj M)) ≫
    (res (b.π.app (op n))).map
      (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ)
        ((SheafOfModules.SequenceProjection.extension b.pt (rings J B τ) b.π).obj M) n).inv = _
  exact unit_iso_cancel (res (b.π.app (op n)))
    ((seqScalar J B τ b n).ordinaryAdj.unit.app M)
    (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ)
      ((SheafOfModules.SequenceProjection.extension b.pt (rings J B τ) b.π).obj M) n)
    ((seqEvaluationIso J B τ n).app ((seqExtension J B τ b).obj M))

private theorem evaluation_comparison_eq
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (n : ℕ) :
    seqEvaluationIso J B τ n = eqToIso (seqEval_eq J B τ n) := by
  have h (φ ψ : ring J (B n) ⟶
      ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r}
        J (coefficientSequenceTopology J)).obj (ring (coefficientSequenceTopology J)
          (systemRing J B τ))) (e : φ = ψ) :
      SheafOfModules.pushforwardCongr e =
        eqToIso (congrArg (fun k ↦ SheafOfModules.pushforward (F := Prod.sectR n C) k) e) := by
    subst ψ
    ext N V x
    rfl
  exact h _ _ (seqEval_ringMap J B τ n)

private theorem extension_horizontal_unit
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) {m n : ℕ} (h : n ≤ m) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((seqExtension J B τ b).obj M).val.map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
      (SheafOfModules.systemModelTmul (seqScalar J B τ b m).model M V 1 x) =
        SheafOfModules.systemModelTmul (seqScalar J B τ b n).model M V 1 x := by
  change (((SheafOfModules.SequenceProjection.extensionObj b.pt (rings J B τ) b.π M).level
    n).val.map (𝟙 V))
      ((SheafOfModules.SequenceProjection.transition b.pt (rings J B τ) b.π M h).val.app V
        (SheafOfModules.systemModelTmul (seqScalar J B τ b m).model M V 1 x)) = _
  rw [PresheafOfModules.map_id]
  change (SheafOfModules.SequenceProjection.transition b.pt (rings J B τ) b.π M h).val.app V
    (SheafOfModules.systemModelTmul (seqScalar J B τ b m).model M V 1 x) = _
  erw [SheafOfModules.SequenceProjection.transition_tmul.{c, v, r}, map_one]

private theorem transpose_of_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R)
    {V : B ⥤ D} {S : D ⥤ A} {T : A ⥤ D} (fin : T ⊣ S)
    (e : F ⋙ V ≅ T) (π : R ⟶ V ⋙ S)
    (hu : ∀ M, adj.unit.app M ≫ π.app (F.obj M) ≫ S.map (e.hom.app M) = fin.unit.app M)
    (M : A) (N : B) (h : M ⟶ R.obj N) :
    fin.homEquiv M (V.obj N)
      (e.inv.app M ≫ V.map ((adj.homEquiv M N).symm h)) = h ≫ π.app N := by
  have hc : fin.unit.app M ≫ S.map (e.inv.app M) =
      adj.unit.app M ≫ π.app (F.obj M) := by
    apply (cancel_mono (S.map (e.hom.app M))).mp
    erw [Category.assoc, ← S.map_comp, Iso.inv_hom_id_app, S.map_id, Category.comp_id]
    simpa only [Category.assoc] using (hu M).symm
  erw [Adjunction.homEquiv_unit, S.map_comp, ← Category.assoc, hc,
    Category.assoc, ← π.naturality, ← Category.assoc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem generic_ordinary_transition
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) (m n : ℕ) (h : n ≤ m)
    {Fm : Mod J b.pt ⥤ Mod J (B m)} (am : Fm ⊣ res (b.π.app (op m)))
    {Fn : Mod J b.pt ⥤ Mod J (B n)} (an : Fn ⊣ res (b.π.app (op n)))
    (g : ring J (B m) ⟶ ring J (B n))
    (e : SheafOfModules.restrictScalars g ⋙ res (b.π.app (op m)) =
      res (b.π.app (op n)))
    (δ : (evaluation J B τ m).obj ((seqExtension J B τ b).obj M) ⟶
      (SheafOfModules.restrictScalars g).obj
        ((evaluation J B τ n).obj ((seqExtension J B τ b).obj M)))
    (hδ : ∀ (V : Cᵒᵖ),
      HEq (fun x : ((evaluation J B τ m).obj ((seqExtension J B τ b).obj M)).val.obj V ↦
        δ.val.app V x)
        (fun x : ((seqExtension J B τ b).obj M).val.obj (op (m, V.unop)) ↦
          ((seqExtension J B τ b).obj M).val.map
            (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    :
    δ ≫ (SheafOfModules.restrictScalars g).map
      (((seqOrdinaryEvaluation J B τ b n) ≪≫
        (seqScalar J B τ b n).ordinaryAdj.leftAdjointUniq an).hom.app M) =
      (((seqOrdinaryEvaluation J B τ b m) ≪≫
        (seqScalar J B τ b m).ordinaryAdj.leftAdjointUniq am).hom.app M) ≫
        (coefficientQuotientNatTrans am an
          (SheafOfModules.restrictScalars g) (eqToIso e)).app M := by
  apply systemScalarTransitionComparison J (b.π.app (op m)) (b.π.app (op n))
    (seqScalar J B τ b m) (seqScalar J B τ b n) am an
    (seqOrdinaryEvaluation J B τ b m) (seqOrdinaryEvaluation J B τ b n)
    M g e δ ?_
    ((coefficientQuotientNatTrans am an
      (SheafOfModules.restrictScalars g) (eqToIso e)).app M) rfl
  intro V x
  erw [seqOrdinaryEvaluation_hom J B τ b n M V]
  erw [seqOrdinaryEvaluation_inv J B τ b m M V]
  exact (congrFun (eq_of_heq (hδ V)) _).trans
    (extension_horizontal_unit J B τ b M h V x)

private def evaluatedIsoHom {A B D : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A) :
    G.obj (F.obj M) ⟶ H.obj M :=
  e.hom.app M

private theorem evaluatedIsoHom_heq {A B D : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A) :
    HEq (evaluatedIsoHom F G e M) (e.hom.app M) := HEq.rfl

private def evaluatedRightHom {A B D : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    (F : A ⥤ D) (G : A ⥤ B) (R : B ⥤ D) (q : F ⟶ G ⋙ R) (M : A) :
    F.obj M ⟶ R.obj (G.obj M) := q.app M

private theorem evaluatedIsoHom_precomp_heq {A B D D' : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D] [Category.{v} D']
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A)
    (R : D ⥤ D') {N : D'} (δ : N ⟶ R.obj (G.obj (F.obj M))) :
    HEq (δ ≫ R.map (e.hom.app M)) (δ ≫ R.map (evaluatedIsoHom F G e M)) := HEq.rfl

private theorem evaluatedIsoHom_compRight_heq {A B D D' : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D] [Category.{v} D']
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A)
    (K : A ⥤ D') (R : D' ⥤ D) (q : H ⟶ K ⋙ R) :
    HEq (e.hom.app M ≫ q.app M)
      (evaluatedIsoHom F G e M ≫ evaluatedRightHom H K R q M) := HEq.rfl

private theorem evaluatedIsoHom_transition_eq {A B D D' : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D] [Category.{v} D']
    (F : A ⥤ B) (Vm : B ⥤ D) (Vn : B ⥤ D')
    {Tm : A ⥤ D} {Tn : A ⥤ D'}
    (tm : F ⋙ Vm ≅ Tm) (tn : F ⋙ Vn ≅ Tn) (M : A)
    (R : D' ⥤ D) (δ : Vm.obj (F.obj M) ⟶ R.obj (Vn.obj (F.obj M)))
    (q : Tm ⟶ Tn ⋙ R)
    (h : HEq (δ ≫ R.map (tn.hom.app M)) (tm.hom.app M ≫ q.app M)) :
    δ ≫ R.map (tn.hom.app M) = tm.hom.app M ≫ q.app M := eq_of_heq h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem generic_ordinary_transition_comparisons
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) (m n : ℕ) (h : n ≤ m)
    {Fm : Mod J b.pt ⥤ Mod J (B m)}
    (Gm : Mod J (B m) ⥤ Mod J b.pt) (egm : Gm = res (b.π.app (op m)))
    (am : Fm ⊣ Gm)
    {Fn : Mod J b.pt ⥤ Mod J (B n)}
    (Gn : Mod J (B n) ⥤ Mod J b.pt) (egn : Gn = res (b.π.app (op n)))
    (an : Fn ⊣ Gn)
    (g : ring J (B m) ⟶ ring J (B n))
    (R : Mod J (B n) ⥤ Mod J (B m))
    (er : R = SheafOfModules.restrictScalars g)
    (e : R ⋙ Gm = Gn)
    (Xm : Mod J b.pt ⥤ Mod J (B m)) (Xn : Mod J b.pt ⥤ Mod J (B n))
    (exm : Xm = seqExtension J B τ b ⋙ evaluation J B τ m)
    (exn : Xn = seqExtension J B τ b ⋙ evaluation J B τ n)
    (xm : Mod J (B m)) (xn : Mod J (B n))
    (eam : xm = Xm.obj M) (ean : xn = Xn.obj M)
    (δ : xm ⟶ R.obj xn)
    (hδ : ∀ (V : Cᵒᵖ),
      HEq (fun x : xm.val.obj V ↦
        δ.val.app V x)
        (fun x : ((seqExtension J B τ b).obj M).val.obj (op (m, V.unop)) ↦
          ((seqExtension J B τ b).obj M).val.map
            (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    (tm : Xm ≅ Fm)
    (tn : Xn ≅ Fn)
    (htm : tm = eqToIso exm ≪≫ seqOrdinaryEvaluation J B τ b m ≪≫
      (seqScalar J B τ b m).ordinaryAdj.leftAdjointUniq
        (Eq.mp (congrArg (fun G ↦ Fm ⊣ G) egm) am))
    (htn : tn = eqToIso exn ≪≫ seqOrdinaryEvaluation J B τ b n ≪≫
      (seqScalar J B τ b n).ordinaryAdj.leftAdjointUniq
        (Eq.mp (congrArg (fun G ↦ Fn ⊣ G) egn) an))
    (fm : xm ⟶ Fm.obj M) (fn : xn ⟶ Fn.obj M)
    (hfm : HEq fm (tm.hom.app M)) (hfn : HEq fn (tn.hom.app M))
    (q : Fm ⟶ Fn ⋙ R)
    (hq : q = coefficientQuotientNatTrans am an R (eqToIso e))
    {α β : Type (max c r)} (L : α) (Q : β)
    (hL : HEq L (δ ≫ R.map fn)) (hQ : HEq Q (fm ≫ evaluatedRightHom Fm Fn R q M)) : HEq L Q := by
  refine hL.trans ((heq_of_eq ?_).trans hQ.symm)
  clear hL hQ L Q
  subst q
  cases eam
  cases ean
  have hm := eq_of_heq hfm
  have hn := eq_of_heq hfn
  subst fm
  subst fn
  cases egm
  cases egn
  cases er
  cases exm
  cases exn
  simp only [eqToIso_refl, Iso.refl_trans] at htm htn
  subst tm
  subst tn
  change δ ≫ (SheafOfModules.restrictScalars g).map
      (((seqOrdinaryEvaluation J B τ b n) ≪≫
        (seqScalar J B τ b n).ordinaryAdj.leftAdjointUniq an).hom.app M) =
    (((seqOrdinaryEvaluation J B τ b m) ≪≫
      (seqScalar J B τ b m).ordinaryAdj.leftAdjointUniq am).hom.app M) ≫
        (coefficientQuotientNatTrans am an
          (SheafOfModules.restrictScalars g) (eqToIso e)).app M
  exact generic_ordinary_transition J B τ b M m n h am an g e δ hδ

end WeilConjectures.OrdinaryQuotient
end Generic

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Exact restriction of a system complex to its completed-coefficient tower.
Source: Stacks 0941. -/
abbrev tower := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- The ordinary sequence direct image: restriction of rings followed by inverse limit.
Source: Stacks 07A6, 0941. -/
abbrev ordinaryLimit := coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

/-- The quotient-system tensor functor with its ordinary adjunction and actual tensor
unit. The evaluation isomorphisms identify its components with the recorded scalar
extension, and `transition` fixes the strict quotient maps at all levels.
`unit_tensor` fixes the adjunction itself on sections.
Source: Stacks 03EK, 07A6, 0941. -/
structure OrdinaryModel where
  tensor : scalarReductionSource l E W ⥤ coefficientSequenceModules l E W
  [additive : tensor.Additive]
  evaluation : ∀ n : ℕ, tensor ⋙ coefficientSequenceEvaluation l E W n ≅
    scalarReductionExtension l E W n
  transition : ∀ (M : scalarReductionSource l E W) {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app (tensor.obj M) ≫
        (normalizedDVRModuleRes l E W h).map ((evaluation n).hom.app M) =
      (evaluation m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M
  adjunction : tensor ⊣ ordinaryLimit l E W
  unit_tensor : ∀ (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : M.val.obj V),
    ((adjunction.unit.app M ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (tensor.obj M)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          (tensor.obj M) ≫
        (scalarReductionRestriction l E W n).map ((evaluation n).hom.app M)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n M V 1 x
  limitComparison : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ≅
    tower l E W ⋙ roosLimitFunctor
  limitComparison_projection : ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (n : ℕ) (p : ℤ),
    ((limitComparison.hom.app I) ≫
        limit.π ((tower l E W).obj I).asFunctor (op n)).f p =
      limit.π ((coefficientSequenceRestriction l E W).obj (I.X p)) (op n)

attribute [instance] OrdinaryModel.additive

/-- The strict quotient system of a complex is the termwise ordinary tensor functor.
Source: Stacks 06YY, 0941. -/
abbrev OrdinaryModel.quotient (M : OrdinaryModel l E W) :=
  M.tensor.mapHomologicalComplex (.up ℤ)

end WeilConjectures.OrdinaryQuotient

/-! ### The sequence-site construction of the ordinary quotient system -/

section Construction
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures.OrdinaryQuotient

open SemilinearSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The recorded ordinary scalar adjunction at a finite level. -/
private def finiteAdjunction (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)

attribute [local irreducible] CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted normalizedDVRQuotient
  completedIntegralCommRingProjectionUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence scalarReductionExtension
  coefficientFiniteDerivedExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory

private abbrev baseTopology := Scheme.ProEt.topology W
private abbrev finiteRings := fun n ↦ integralCoefficientCommRingSheaf l E W n
private abbrev finiteMaps := coefficientSequenceCommRingTransition l E W

private def completionCone :
    Cone (rings (baseTopology W) (finiteRings l E W) (finiteMaps l E W)) :=
  ⟨completedIntegralCommRingSheafUnrestricted l E W, coefficientCone l E W⟩

open SemilinearSections

private abbrev ordinaryGeometry :=
  seqSetProjection (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W)

private theorem evaluation_eq (n : ℕ) :
    evaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W) n =
      coefficientSequenceEvaluation l E W n := by
  rfl

private theorem restriction_eq :
    seqRestriction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W) = coefficientSequenceRestriction l E W := by
  unfold coefficientSequenceRestriction
  apply (coefficientSequenceRestriction_exists l E W).unique ?_
    (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro M n
    rw [seqRestrictionObjEq, evaluation_eq]
    rfl
  · intro M m n h V
    rfl
  · intro M N f n V
    rfl

private def ordinaryExtension :
    scalarReductionSource l E W ⥤ coefficientSequenceModules l E W :=
  seqExtension (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W)

private def extensionAdjunction :
    ordinaryExtension l E W ⊣ (ordinaryGeometry l E W).π.modules :=
  seqModuleAdjunction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W)

private abbrev levelAdjunction (n : ℕ) :=
  (seqScalar (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W) n).ordinaryAdj

private theorem finiteRestriction_eq (n : ℕ) :
    scalarReductionRestriction l E W n =
      res ((completionCone l E W).π.app (op n)) := by
  rfl

private def ordinaryTensor (n : ℕ) :
    ordinaryExtension l E W ⋙ coefficientSequenceEvaluation l E W n ≅
      scalarReductionExtension l E W n :=
  eqToIso (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T)
    (evaluation_eq l E W n).symm) ≪≫
  seqOrdinaryEvaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W) n ≪≫
    (seqScalar (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W) n).ordinaryAdj.leftAdjointUniq
      (Eq.mp (congrArg (fun G ↦ scalarReductionExtension l E W n ⊣ G)
        (finiteRestriction_eq l E W n)) (finiteAdjunction l E W n))

private def ordinaryProjectionNat (n : ℕ) :
    (ordinaryGeometry l E W).π.modules ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft
    (seqRestriction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W)) (lim.π (op n)) ≫
    (Functor.isoWhiskerRight
      (seqEvaluationIso (baseTopology W) (finiteRings l E W) (finiteMaps l E W) n).symm
      (scalarReductionRestriction l E W n)).hom

private abbrev ordinaryProjection (N : coefficientSequenceModules l E W) (n : ℕ) :=
  (ordinaryProjectionNat l E W n).app N

private theorem ordinary_unit (M : scalarReductionSource l E W) (n : ℕ) :
    (extensionAdjunction l E W).unit.app M ≫
      ordinaryProjection l E W ((ordinaryExtension l E W).obj M) n ≫
        (scalarReductionRestriction l E W n).map ((ordinaryTensor l E W n).hom.app M) =
      (finiteAdjunction l E W n).unit.app M := by
  simp only [ordinaryTensor, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp, ordinaryProjection, ordinaryProjectionNat,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, lim.π_app]
  have h := unit_evaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
    (completionCone l E W) M n
  have h' := congrArg (· ≫ (scalarReductionRestriction l E W n).map
    (((levelAdjunction l E W n).leftAdjointUniq
      (finiteAdjunction l E W n)).hom.app M)) h
  have hu := h'.trans (Adjunction.unit_leftAdjointUniq_hom_app
    (levelAdjunction l E W n) (finiteAdjunction l E W n) M)
  simp only [Category.assoc] at hu ⊢
  exact hu

private theorem ab_function_heq {A B A' B' : AddCommGrpCat.{r}}
    (a : A = A') (b : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom a.symm ≫ f ≫ eqToHom b = g) :
    HEq (fun x : A ↦ f x) (fun x : A' ↦ g x) := by
  subst a
  subst b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact heq_of_eq (congrArg (fun k ↦ fun x ↦ k x) h)

private theorem module_forget_function_eq {R : Type*} [Ring R]
    {M N : ModuleCat.{r} R} (f : M ⟶ N) :
    (fun x : M ↦ ((forget₂ (ModuleCat.{r} R) AddCommGrpCat.{r}).map f) x) =
      (fun x : M ↦ f x) := rfl

private theorem presheaf_function_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules.{r} R)
    {V V' : Cᵒᵖ} (f : V ⟶ V') :
    (fun x : N.obj V ↦ N.presheaf.map f x) = (fun x : N.obj V ↦ N.map f x) := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual horizontal map, retaining the two literal section carriers.
Source: Stacks 0941 (blueprint: lem-pur-sequence-ordinary-factorization).
Proof: remove the source and target additive-group transports in the defining
transition equation. Forgetting linearity does not change the underlying function. -/
private theorem coefficientSequenceTransition_function_heq (N : coefficientSequenceModules l E W)
    {m n : ℕ} (h : n ≤ m) (V : W.ProEtᵒᵖ) :
    HEq (fun x : ((coefficientSequenceEvaluation l E W m).obj N).val.obj V ↦
      ((coefficientSequenceTransition l E W h).app N).val.app V x)
      (fun x : N.val.obj (op (m, V.unop)) ↦
        N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  have hc := (coefficientSequenceTransition_exists l E W h).exists.choose_spec N V
  have he := ab_function_heq
    (coefficientSequenceEvaluationAb_eq l E W N m V)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W N h V) _ _ hc
  exact (heq_of_eq (module_forget_function_eq _)).symm.trans
    (he.trans (heq_of_eq (presheaf_function_eq N.val _)))

attribute [local irreducible] coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
  coefficientQuotientNatTrans

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryTensor_eq (n : ℕ) :
    ordinaryTensor l E W n =
      eqToIso (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T)
        (evaluation_eq l E W n).symm) ≪≫
      seqOrdinaryEvaluation (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
        (completionCone l E W) n ≪≫
        (seqScalar (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
          (completionCone l E W) n).ordinaryAdj.leftAdjointUniq
          (Eq.mp (congrArg (fun G ↦ scalarReductionExtension l E W n ⊣ G)
            (finiteRestriction_eq l E W n)) (finiteAdjunction l E W n)) := by
  rfl

private theorem quotient_mate_nat_eq {m n : ℕ} (h : n ≤ m) :
    coefficientOrdinaryQuotient l E W h =
      coefficientQuotientNatTrans (finiteAdjunction l E W m)
        (finiteAdjunction l E W n) (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h)) := by
  unfold coefficientOrdinaryQuotient
  apply (coefficientOrdinaryQuotient_exists l E W h).unique
    (coefficientOrdinaryQuotient_exists l E W h).choose_spec.1
  intro M
  unfold coefficientOrdinaryQuotientComponent finiteAdjunction
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinary_transition_model
    (M : scalarReductionSource l E W) (m n : ℕ) (h : n ≤ m) :
    HEq
      ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M) ≫
        (normalizedDVRModuleRes l E W h).map ((ordinaryTensor l E W n).hom.app M))
      ((ordinaryTensor l E W m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M) := by
  exact generic_ordinary_transition_comparisons (baseTopology W) (finiteRings l E W)
    (finiteMaps l E W) (completionCone l E W) M m n h
    (scalarReductionRestriction l E W m) (finiteRestriction_eq l E W m)
    (finiteAdjunction l E W m)
    (scalarReductionRestriction l E W n) (finiteRestriction_eq l E W n)
    (finiteAdjunction l E W n)
    (normalizedDVRQuotient l E W h) (normalizedDVRModuleRes l E W h) rfl
    (coefficientRestrictionComp l E W h)
    (ordinaryExtension l E W ⋙ coefficientSequenceEvaluation l E W m)
    (ordinaryExtension l E W ⋙ coefficientSequenceEvaluation l E W n)
    (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T) (evaluation_eq l E W m).symm)
    (congrArg (fun T ↦ ordinaryExtension l E W ⋙ T) (evaluation_eq l E W n).symm)
    ((coefficientSequenceEvaluation l E W m).obj ((ordinaryExtension l E W).obj M))
    ((coefficientSequenceEvaluation l E W n).obj ((ordinaryExtension l E W).obj M))
    (Functor.comp_obj (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m) M).symm
    (Functor.comp_obj (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n) M).symm
    ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M))
    (fun V ↦ coefficientSequenceTransition_function_heq l E W
      ((ordinaryExtension l E W).obj M) h V)
    (ordinaryTensor l E W m) (ordinaryTensor l E W n)
    (ordinaryTensor_eq l E W m) (ordinaryTensor_eq l E W n)
    (evaluatedIsoHom (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m)
      (ordinaryTensor l E W m) M)
    (evaluatedIsoHom (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W n)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n)
      (ordinaryTensor l E W n) M)
    (evaluatedIsoHom_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m)
      (ordinaryTensor l E W m) M)
    (evaluatedIsoHom_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W n)
      (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n)
      (ordinaryTensor l E W n) M)
    (coefficientOrdinaryQuotient l E W h)
    (quotient_mate_nat_eq l E W h)
    ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M) ≫
      (normalizedDVRModuleRes l E W h).map ((ordinaryTensor l E W n).hom.app M))
    ((ordinaryTensor l E W m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M)
    (evaluatedIsoHom_precomp_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W n)
      (D' := normalizedDVRModules l E W m) (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W n) (ordinaryTensor l E W n) M
      (normalizedDVRModuleRes l E W h)
      ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M)))
    (evaluatedIsoHom_compRight_heq (A := scalarReductionSource l E W)
      (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
      (D' := scalarReductionTarget l E W n) (ordinaryExtension l E W)
      (coefficientSequenceEvaluation l E W m) (ordinaryTensor l E W m) M
      (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
      (coefficientOrdinaryQuotient l E W h))

private theorem ordinary_transition (M : scalarReductionSource l E W)
    (m n : ℕ) (h : n ≤ m) :
    (coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M) ≫
      (normalizedDVRModuleRes l E W h).map ((ordinaryTensor l E W n).hom.app M) =
        (ordinaryTensor l E W m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M := by
  exact evaluatedIsoHom_transition_eq (A := scalarReductionSource l E W)
    (B := coefficientSequenceModules l E W) (D := normalizedDVRModules l E W m)
    (D' := normalizedDVRModules l E W n) (ordinaryExtension l E W)
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (ordinaryTensor l E W m) (ordinaryTensor l E W n) M
    (normalizedDVRModuleRes l E W h)
    ((coefficientSequenceTransition l E W h).app ((ordinaryExtension l E W).obj M))
    (coefficientOrdinaryQuotient l E W h) (ordinary_transition_model l E W M m n h)

private def ordinaryLimitIso : (ordinaryGeometry l E W).π.modules ≅
    coefficientSequenceRestriction l E W ⋙
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) :=
  Functor.isoWhiskerRight (eqToIso (restriction_eq l E W)) lim

private theorem ordinaryProjection_limit (N : coefficientSequenceModules l E W) (n : ℕ) :
    ordinaryProjection l E W N n = (ordinaryLimitIso l E W).hom.app N ≫
      limit.π ((coefficientSequenceRestriction l E W).obj N) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app N := by
  dsimp only [ordinaryProjection, ordinaryProjectionNat, ordinaryLimitIso,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, lim.π_app]
  erw [limMap_π_assoc]
  apply congrArg (fun f ↦ limit.π
    ((seqRestriction (baseTopology W) (finiteRings l E W) (finiteMaps l E W)
      (completionCone l E W)).obj N) (op n) ≫ f)
  rw [evaluation_comparison_eq]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]

private theorem ordinary_transpose (M : scalarReductionSource l E W)
    (N : coefficientSequenceModules l E W)
    (h : M ⟶ (ordinaryGeometry l E W).π.modules.obj N) (n : ℕ) :
    (finiteAdjunction l E W n).homEquiv M
      ((coefficientSequenceEvaluation l E W n).obj N)
      ((ordinaryTensor l E W n).inv.app M ≫
        (coefficientSequenceEvaluation l E W n).map
          (((extensionAdjunction l E W).homEquiv M N).symm h)) =
      h ≫ ordinaryProjection l E W N n :=
  transpose_of_unit (extensionAdjunction l E W) (finiteAdjunction l E W n)
    (ordinaryTensor l E W n) (ordinaryProjectionNat l E W n)
    (fun M ↦ ordinary_unit l E W M n) M N h
end WeilConjectures.OrdinaryQuotient
end Construction

/-! ### The ordinary model -/

section Model
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section OrdinaryConstruction
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf

private theorem ordinary_projection_unit (M : scalarReductionSource l E W) (n : ℕ) :
    (extensionAdjunction l E W).unit.app M ≫ ordinaryProjection l E W
      ((ordinaryExtension l E W).obj M) n ≫
      (scalarReductionRestriction l E W n).map ((ordinaryTensor l E W n).hom.app M) =
      (finiteAdjunction l E W n).unit.app M := by
  have ht := ordinary_transpose l E W M ((ordinaryExtension l E W).obj M)
    ((extensionAdjunction l E W).unit.app M) n
  rw [Adjunction.homEquiv_symm_unit, CategoryTheory.Functor.map_id] at ht
  erw [Category.comp_id] at ht
  rw [← Category.assoc, ← ht, Adjunction.homEquiv_unit]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private def limitAdjunction :
    ordinaryExtension l E W ⊣ ordinaryLimit l E W :=
  (extensionAdjunction l E W).ofNatIsoRight (ordinaryLimitIso l E W)

private theorem ordinary_projection_unit_fixed (M : scalarReductionSource l E W) (n : ℕ) :
    (limitAdjunction l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj ((ordinaryExtension l E W).obj M))
        (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        ((ordinaryExtension l E W).obj M) ≫
      (scalarReductionRestriction l E W n).map ((ordinaryTensor l E W n).hom.app M) =
    (finiteAdjunction l E W n).unit.app M := by
  have hu := ordinary_projection_unit l E W M n
  rw [ordinaryProjection_limit] at hu
  simp only [Category.assoc] at hu
  simpa only [limitAdjunction, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] using hu

end OrdinaryConstruction

private theorem finite_unit_tensor (M : scalarReductionSource l E W) (n : ℕ)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((finiteAdjunction l E W n).unit.app M).val.app V x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  have hu := (scalarReductionExtension_adjunction.{t, u} l E W n).choose_spec M V x
  dsimp only [finiteAdjunction, unrestrictedIntegralTensorSection,
    unrestrictedIntegralReductionFunctor, unrestrictedIntegralReductionExistence,
    scalarReductionExistence] at hu ⊢
  exact hu

private theorem ordinary_unit_tensor
    (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    (((limitAdjunction l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj ((ordinaryExtension l E W).obj M))
        (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        ((ordinaryExtension l E W).obj M) ≫
      (scalarReductionRestriction l E W n).map ((ordinaryTensor l E W n).hom.app M)).val.app V)
        x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  exact (congrArg (fun f ↦ f.val.app V x)
    (ordinary_projection_unit_fixed l E W M n)).trans (finite_unit_tensor l E W M n V x)

section CanonicalComparisons

/-- The cone of ordinary inverse-limit projections in each degree. Source: Stacks 0941. -/
def termwiseLimitCone
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) : Cone Z.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app Z
      naturality := by
        intro n m f
        ext p : 1
        change 𝟙 _ ≫ limit.π (Z.X p) m =
          limit.π (Z.X p) n ≫ (Z.X p).map f
        exact (Category.id_comp _).trans (limit.w (Z.X p) f).symm }

/-- Limits of complexes are computed degreewise. Source: Stacks 0941. -/
def termwiseLimitConeIsLimit
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    IsLimit (termwiseLimitCone l E W Z) :=
  HomologicalComplex.isLimitOfEval Z.asFunctor (termwiseLimitCone l E W Z)
    (fun p ↦ limit.isLimit (Z.X p))

/-- The degreewise limit comparison at one complex. Source: Stacks 0941. -/
def termwiseLimitComparisonComponent
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z ≅
        limit Z.asFunctor :=
  (termwiseLimitConeIsLimit l E W Z).conePointUniqueUpToIso (limit.isLimit _)

/-- Projections of the degreewise limit comparison. Source: Stacks 0941. -/
theorem termwiseLimitComparisonComponent_projection
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    (termwiseLimitComparisonComponent l E W Z).hom ≫ limit.π Z.asFunctor (op n) =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- The termwise inverse limit of a complex of towers is the limit of complexes.
Source: Stacks 0941. -/
def termwiseLimitComparison :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅
        roosLimitFunctor (A := scalarReductionSource l E W) :=
  NatIso.ofComponents (termwiseLimitComparisonComponent l E W) (by
    intro X Y f
    apply limit.hom_ext
    intro n
    change ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map f ≫
        ((termwiseLimitComparisonComponent l E W Y).hom ≫ limit.π Y.asFunctor n) =
      (termwiseLimitComparisonComponent l E W X).hom ≫
        (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) ≫
          limit.π Y.asFunctor n)
    erw [termwiseLimitComparisonComponent_projection l E W Y n.unop]
    erw [limMap_π]
    erw [← Category.assoc,
      termwiseLimitComparisonComponent_projection l E W X n.unop]
    ext p : 1
    exact limMap_π (f.f p) n)

/-- The termwise limit comparison has the ordinary limit projections in each degree.
Source: Stacks 0941. -/
theorem termwiseLimitComparison_projection
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) (p : ℤ) :
    ((termwiseLimitComparison l E W).hom.app Z ≫ limit.π Z.asFunctor (op n)).f p =
      limit.π (Z.X p) (op n) :=
  congrArg (fun f ↦ f.f p) (termwiseLimitComparisonComponent_projection l E W Z n)

end CanonicalComparisons

/-- The ordinary quotient tensor and limit admit the prescribed sectionwise adjunction.
This statement involves no derived coefficient calculus or derived comparison.

Source: Stacks 03D7 and 0941.

Proof: apply the sequence-site constant/limit construction to the completed ring and
its tower of quotients. Identify the level tensors with the recorded scalar extension
by uniqueness of left adjoints; this preserves units and hence the quotient mates.
Limits of complexes are computed degreewise. -/
theorem ordinaryModel_exists : Nonempty (OrdinaryModel l E W) := by
  refine ⟨{
    tensor := ordinaryExtension l E W
    additive := SemilinearSections.seqExtension_additive (baseTopology W) (finiteRings l E W)
      (finiteMaps l E W) (completionCone l E W)
    evaluation := ordinaryTensor l E W
    transition := fun M {m n} h ↦ ordinary_transition l E W M m n h
    adjunction := limitAdjunction l E W
    unit_tensor := ordinary_unit_tensor l E W
    limitComparison := Functor.isoWhiskerLeft (tower l E W) (termwiseLimitComparison l E W)
    limitComparison_projection := ?_
  }⟩
  intro I n p
  exact termwiseLimitComparison_projection l E W ((tower l E W).obj I) n p

end WeilConjectures.OrdinaryQuotient
end Model

-- Restore the incoming instance registration after using compact local sheaf instances.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
