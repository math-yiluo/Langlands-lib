/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingOrdinaryBraiding

/-! # Ambient signed currying under normalized reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 2 and 4;
Stacks 07A4, 08J9, 099B and 099M (blueprint: lem-pod-reindexing-ordinary-currying).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local instance 1000001] cachedCompose
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem transport_currying
    {C : Type a} [Category.{b} C] {D : Type v} [Category.{w} D]
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (HC : Cᵒᵖ × C ⥤ C) (HD : Dᵒᵖ × D ⥤ D)
    (F G : C ⥤ D) (h : F = G)
    (t : TC ⋙ F ≅ (F.prod F) ⋙ TD)
    (c : HC ⋙ F ≅ (F.op.prod F) ⋙ HD)
    (τC : ∀ M L N : C, (TC.obj (M, L) ⟶ N) → (L ⟶ HC.obj (op M, N)))
    (τD : ∀ M L N : D, (TD.obj (M, L) ⟶ N) → (L ⟶ HD.obj (op M, N)))
    (ht : ∀ (M L N : C) (f : TC.obj (M, L) ⟶ N),
      τD (F.obj M) (F.obj L) (F.obj N) (t.inv.app (M, L) ≫ F.map f) =
        F.map (τC M L N f) ≫ c.hom.app (op M, N)) :
    ∀ (M L N : C) (f : TC.obj (M, L) ⟶ N),
      τD (G.obj M) (G.obj L) (G.obj N)
          ((((eqToIso h).app (TC.obj (M, L))).symm ≪≫ t.app (M, L) ≪≫
            TD.mapIso (((eqToIso h).app M).prod ((eqToIso h).app L))).inv ≫ G.map f) =
        G.map (τC M L N f) ≫
          (((eqToIso h).app (HC.obj (op M, N))).symm ≪≫ c.app (op M, N) ≪≫
            HD.mapIso ((((eqToIso h).app M).symm.op).prod ((eqToIso h).app N))).hom := by
  subst G
  intro M L N f
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, Category.assoc,
    eqToIso_refl, Iso.app_inv, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.mapIso_inv, Iso.prod_inv, ← CategoryTheory.prod_id,
    op_id, Functor.comp_obj, Functor.prod_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [HD.map_id, Category.comp_id]
  exact ht M L N f

/-- The ordinary signed M-first currying comparison on all ambient derived objects.
Source: blueprint dual-Tate compatibility, Step 2; Stacks 08J9 and 07A4
(blueprint: lem-pod-reindexing-ordinary-currying).

Proof: the ordinary evaluation lemma gives Hom-first transposition for c. The
signed braiding changes Hom-first order to M-first order: on a homogeneous
summand the two reindexing paths both multiply Fy tensor Fx by (-1)^(pq).
The pure tensor formula of c.tensorChain therefore identifies these paths;
K-flat localization and the recorded tensor model extend the equality to all
unbounded derived objects. Compose this braiding square with the Hom-first
transpose equation. Finally transport from F to the equal projection-normalized
functor G using eqToIso h: equality induction makes every transport the identity,
after which the preceding M-first equation applies. The inverse source component
in the displayed formula enters the contravariant Hom variable. The argument is
ambient: it uses neither constructibility nor completion. -/
theorem podReindexing_ordinary_currying
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SX : PodReindexingCoherence.Closed l E X none)
    (SY : PodReindexingCoherence.Closed l E Y none)
    (TX : PodReindexingCoherence.Models l E X none SX)
    (TY : PodReindexingCoherence.Models l E Y none SY)
    (c : PodReindexingCoherence.Comparison l E g none SX SY TX TY)
    (G : podReindexingDerived l E Y none ⥤ podReindexingDerived l E X none)
    (h : podReindexingDerivedFunctor l E g none = G) :
    let τX := fun M L N ↦
      ((pullbackTensorBraiding (ProEt.topology X) (podReindexingRing l E X none)
        SX TX).app (M, L)).homFromEquiv.trans (SX.transpose L M N)
    let τY := fun M L N ↦
      ((pullbackTensorBraiding (ProEt.topology Y) (podReindexingRing l E Y none)
        SY TY).app (M, L)).homFromEquiv.trans (SY.transpose L M N)
    ∀ (M L N : podReindexingDerived l E Y none) (b : SY.tensor.obj (M, L) ⟶ N),
      τX (G.obj M) (G.obj L) (G.obj N)
          ((((eqToIso h).app (SY.tensor.obj (M, L))).symm ≪≫ c.tensor.app (M, L) ≪≫
            SX.tensor.mapIso (((eqToIso h).app M).prod ((eqToIso h).app L))).inv ≫
              G.map b) =
        G.map (τY M L N b) ≫
          (((eqToIso h).app ((podReindexingDerivedHom l E Y none).obj (op M, N))).symm ≪≫
            c.derived.app (op M, N) ≪≫ (podReindexingDerivedHom l E X none).mapIso
              ((((eqToIso h).app M).symm.op).prod ((eqToIso h).app N))).hom := by
  let F := podReindexingDerivedFunctor l E g none
  let βY := pullbackTensorBraiding (ProEt.topology Y) (podReindexingRing l E Y none) SY TY
  let βX := pullbackTensorBraiding (ProEt.topology X) (podReindexingRing l E X none) SX TX
  let τX := fun M L N ↦ (βX.app (M, L)).homFromEquiv.trans (SX.transpose L M N)
  let τY := fun M L N ↦ (βY.app (M, L)).homFromEquiv.trans (SY.transpose L M N)
  have ht (M L N : podReindexingDerived l E Y none) (b : SY.tensor.obj (M, L) ⟶ N) :
      τX (F.obj M) (F.obj L) (F.obj N) (c.tensor.inv.app (M, L) ≫ F.map b) =
        F.map (τY M L N b) ≫ c.derived.hom.app (op M, N) := by
    have hs := PodReindexingCoherence.podReindexingOrdinaryBraiding
      l E g none SX SY TX TY c M L
    have he : F.mapIso (βY.app (M, L)) ≪≫ c.tensor.app (L, M) =
        c.tensor.app (M, L) ≪≫ βX.app (F.obj M, F.obj L) := Iso.ext hs
    have hi := congrArg Iso.inv he
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hi
    have hc := (PodReindexingCoherence.evaluation_laws l E g none SX SY TX TY c).transpose
      L M N ((βY.app (M, L)).inv ≫ b)
    change SX.transpose (F.obj L) (F.obj M) (F.obj N)
        ((βX.app (F.obj M, F.obj L)).inv ≫ c.tensor.inv.app (M, L) ≫ F.map b) = _
    have hb : (βX.app (F.obj M, F.obj L)).inv ≫ c.tensor.inv.app (M, L) ≫ F.map b =
        c.tensor.inv.app (L, M) ≫ F.map ((βY.app (M, L)).inv ≫ b) := by
      calc
        _ = ((βX.app (F.obj M, F.obj L)).inv ≫ c.tensor.inv.app (M, L)) ≫
            F.map b := (Category.assoc _ _ _).symm
        _ = (c.tensor.inv.app (L, M) ≫ F.map (βY.app (M, L)).inv) ≫ F.map b :=
          congrArg (· ≫ F.map b) hi.symm
        _ = c.tensor.inv.app (L, M) ≫ (F.map (βY.app (M, L)).inv ≫ F.map b) :=
          Category.assoc _ _ _
        _ = _ := congrArg (c.tensor.inv.app (L, M) ≫ ·) (F.map_comp _ _).symm
    exact (congrArg (SX.transpose (F.obj L) (F.obj M) (F.obj N)) hb).trans hc.symm
  exact transport_currying SY.tensor SX.tensor
    (podReindexingDerivedHom l E Y none) (podReindexingDerivedHom l E X none)
    F G h c.tensor c.derived
    (fun M L N b ↦ τY M L N b) (fun M L N b ↦ τX M L N b) ht

end WeilConjectures
