/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! # Descent of a coefficient-compatible pullback square

Source: the Weil-structures paragraph of the open-closed localization proof.
(blueprint: lem-sf-common-stage-pullback-square-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
open AlgebraicallyClosedCoefficients (Index Coefficient)
attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  commonStagePullbackTransition

private theorem automorphism_descend_composite_square
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A B D V : I → Type*}
    [∀ i, Category (A i)] [∀ i, Category (B i)]
    [∀ i, Category (D i)] [∀ i, Category (V i)]
    {SA : StageSystem A} {SB : StageSystem B}
    {SD : StageSystem D} {SV : StageSystem V}
    (F : SA.Morphism SB) (G : SB.Morphism SD)
    (H : SA.Morphism SV) (J : SV.Morphism SD)
    (τ : (F.comp G).Hom (H.comp J)) (hτ : ∀ i, IsIso (τ.τ i)) :
    ∃! d : F.functor ⋙ G.functor ≅ H.functor ⋙ J.functor,
      ∀ K : SA.PairCategory,
        d.hom.app K = (SD.ι K.stage).map ((τ.τ K.stage).app K.obj) := by
  let := StageSystem.Morphism.isIso_descNatTrans τ hτ
  let d : F.functor ⋙ G.functor ≅ H.functor ⋙ J.functor :=
    (StageSystem.Morphism.functorCompIso F G).symm ≪≫
      asIso (StageSystem.Morphism.descNatTrans τ) ≪≫
        StageSystem.Morphism.functorCompIso H J
  have hd (K : SA.PairCategory) :
      d.hom.app K = (SD.ι K.stage).map ((τ.τ K.stage).app K.obj) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, NatTrans.comp_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
  refine ⟨d, hd, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (ha K).trans (hd K).symm

private theorem automorphism_iso_existsUnique_transport
    {A B : Type*} [Category A] [Category B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    {R : A → Type*} (r : ∀ K, R K)
    (hb : ∃! d : F' ≅ G', ∀ K, HEq (d.hom.app K) (r K)) :
    ∃! d : F ≅ G, ∀ K, HEq (d.hom.app K) (r K) := by
  subst F'
  subst G'
  exact hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible isomorphisms of finite-stage pullback composites descend uniquely.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph: common-stage b and d.
(blueprint: lem-sf-common-stage-pullback-square-descent).

Proof: use commonStagePullbackNormalizedDescent for each of the three maps.
The hypothesis hb is precisely the compatibility equation for a Hom between the
two composite stage morphisms. Descend that Hom by descNatTrans. It is invertible
because each finite component is invertible. Conjugate by the two functorCompIso
comparisons to obtain an isomorphism of the composite descended functors. Their
components are identity arrows, so the component at a literal pair is the inclusion
of b at that pair's stage. Extensionality of natural transformations proves
uniqueness. Identity inclusions and empty schemes use the same construction. -/
theorem commonStagePullbackSquare_existsUnique
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (b : ∀ E : Index l Ω,
      rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⋙
        rationalDerivedPullback l (Coefficient.{u} l Ω E) eY.asIso.hom ≅
      rationalDerivedPullback l (Coefficient.{u} l Ω E) eX.asIso.hom ⋙
        rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (hb : ∀ {E L : Index l Ω} (w : E ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E),
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T w).map
          ((b E).hom.app K) ≫
        (commonStagePullbackTransition l Ω f w).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) eX.asIso.hom).obj K) ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackTransition l Ω eX.asIso.hom w).hom.app K) =
      ((commonStagePullbackTransition l Ω eY.asIso.hom w).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj K) ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω L) eY.asIso.hom).map
          ((commonStagePullbackTransition l Ω f w).hom.app K)) ≫
        (b L).hom.app (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T w).obj K)) :
    ∃! d : commonStageDerivedPullback l Ω f ⋙ commonStageDerivedPullback l Ω eY.asIso.hom ≅
        commonStageDerivedPullback l Ω eX.asIso.hom ⋙ commonStageDerivedPullback l Ω f,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        HEq (d.hom.app K)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) K.stage).map ((b K.stage).hom.app K.obj)) := by
  classical
  obtain ⟨hf, ef⟩ := commonStagePullbackNormalizedDescent l Ω f
  obtain ⟨hx, ex⟩ := commonStagePullbackNormalizedDescent l Ω eX.asIso.hom
  obtain ⟨hy, ey⟩ := commonStagePullbackNormalizedDescent l Ω eY.asIso.hom
  let Mf : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y) :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f,
      commonStagePullbackTransition l Ω f, hf⟩
  let Mx : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) eX.asIso.hom,
      commonStagePullbackTransition l Ω eX.asIso.hom, hx⟩
  let My : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y) :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) eY.asIso.hom,
      commonStagePullbackTransition l Ω eY.asIso.hom, hy⟩
  let τ : (Mf.comp My).Hom (Mx.comp Mf) := {
    τ := fun E ↦ (b E).hom
    comm := by
      intro E L w K
      simp only [StageSystem.Morphism.comp_β_hom_app]
      dsimp only [Mf, Mx, My]
      exact hb w K }
  obtain ⟨d, hd, hu⟩ := automorphism_descend_composite_square Mf My Mx Mf τ (fun E ↦ by
    change IsIso (b E).hom
    infer_instance)
  exact automorphism_iso_existsUnique_transport
    (congrArg₂ Functor.comp ef ey) (congrArg₂ Functor.comp ex ef)
    (fun K : generalAlgebraicallyClosedConstructibleCategory l Ω X ↦
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Y) K.stage).map ((b K.stage).hom.app K.obj))
    ⟨d, fun K ↦ heq_of_eq (hd K), fun a ha ↦ hu a (fun K ↦ eq_of_heq (ha K))⟩

end WeilConjectures
