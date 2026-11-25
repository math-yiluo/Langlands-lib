/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # The evaluation-preserving comparison of closed tensor presentations

Source: Stacks 08J9; uniqueness of adjoints applied in both tensor variables.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b
open CategoryTheory Opposite
namespace WeilConjectures.CoefficientClosedStructure
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}

/-- Transposing a tensor map is natural in both arguments.
Source: tensor-Hom adjunction naturality; Stacks 08J9.
(blueprint: lem-coef-closed-tensor-comparison). -/
theorem transpose_tensor (S : CoefficientClosedStructure H)
    {A A' P P' Q : D} (f : A ⟶ A') (g : P ⟶ P')
    (h : S.tensor.obj (A', P') ⟶ Q) :
    S.transpose A P Q (S.tensor.map (Prod.mkHom f g) ≫ h) =
      f ≫ S.transpose A' P' Q h ≫ H.map (Prod.mkHom g.op (𝟙 Q)) := by
  have ht : S.tensor.map (Prod.mkHom f g) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ S.tensor.map (Prod.mkHom (𝟙 A') g) := by
    rw [← Functor.map_comp]
    congr 1
    ext <;> simp
  rw [ht, Category.assoc, ringedSiteTranspose_left, ringedSiteTranspose_source]

/-- Two closed tensors for the same internal Hom have a canonical comparison,
fixed by their adjunction units and counits. It is natural in both tensor arguments.
Source: the uniqueness of adjoints, applied parametrically; Stacks 08J9.
(blueprint: lem-coef-closed-tensor-comparison). -/
def comparison (S T : CoefficientClosedStructure H) : S.tensor ≅ T.tensor :=
  NatIso.ofComponents
    (fun X ↦ (Adjunction.leftAdjointUniq (S.adjunction X.2) (T.adjunction X.2)).app X.1)
    (by
      intro X Y f
      apply (S.transpose X.1 X.2 (T.tensor.obj Y)).injective
      change S.transpose X.1 X.2 (T.tensor.obj Y)
          (S.tensor.map (Prod.mkHom f.1 f.2) ≫ _) = _
      simp only [Iso.app_hom]
      rw [transpose_tensor]
      rw [show S.transpose Y.1 Y.2 (T.tensor.obj Y)
          ((Adjunction.leftAdjointUniq (S.adjunction Y.2) (T.adjunction Y.2)).hom.app Y.1) =
          (T.adjunction Y.2).unit.app Y.1 from
            Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _]
      rw [show S.transpose X.1 X.2 (T.tensor.obj Y)
          ((Adjunction.leftAdjointUniq (S.adjunction X.2) (T.adjunction X.2)).hom.app X.1 ≫
            T.tensor.map f) =
          (T.adjunction X.2).unit.app X.1 ≫ H.map (Prod.mkHom (𝟙 (op X.2)) (T.tensor.map f)) by
        exact ((S.adjunction X.2).homEquiv_naturality_right _ _).trans
          (congrArg (fun h ↦ h ≫ H.map (Prod.mkHom (𝟙 (op X.2)) (T.tensor.map f)))
            (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _))]
      have h := transpose_tensor T f.1 f.2 (𝟙 (T.tensor.obj Y))
      change (T.adjunction X.2).homEquiv X.1 (T.tensor.obj Y)
          (T.tensor.map f ≫ 𝟙 (T.tensor.obj Y)) =
        f.1 ≫ (T.adjunction Y.2).homEquiv Y.1 (T.tensor.obj Y)
          (𝟙 (T.tensor.obj Y)) ≫ H.map (Prod.mkHom f.2.op (𝟙 _)) at h
      have hy : (T.adjunction Y.2).homEquiv Y.1 (T.tensor.obj Y)
          (𝟙 (T.tensor.obj Y)) = (T.adjunction Y.2).unit.app Y.1 :=
        (T.adjunction Y.2).homEquiv_id Y.1
      rw [hy, Category.comp_id, Adjunction.homEquiv_unit] at h
      exact h.symm)

/-- On equal presentations the canonical comparison is the equality transport.
Source: uniqueness of adjoints; Stacks 08J9.
(blueprint: lem-coef-closed-tensor-comparison). -/
theorem comparison_eqToIso (S T : CoefficientClosedStructure H) (h : S = T) :
    comparison S T = eqToIso (congrArg CoefficientClosedStructure.tensor h) := by
  subst T
  ext X
  simp only [comparison, NatIso.ofComponents_hom_app, Iso.app_hom,
    Adjunction.leftAdjointUniq_refl, Iso.refl_hom, NatTrans.id_app, eqToIso_refl]
  rfl

/-- The canonical comparison intertwines evaluation in the entire derived category.
Source: adjunction uniqueness; Stacks 08J9.
(blueprint: lem-coef-closed-tensor-comparison). -/
theorem comparison_evaluation (S T : CoefficientClosedStructure H) (P Q : D) :
    (comparison S T).hom.app (H.obj (op P, Q), P) ≫ T.evaluation P Q =
      S.evaluation P Q :=
  Adjunction.leftAdjointUniq_hom_app_counit (S.adjunction P) (T.adjunction P) Q

/-- The comparison preserves the entire tensor-Hom bijection.
Source: uniqueness of adjoints; Stacks 08J9.
(blueprint: lem-coef-closed-tensor-comparison). -/
theorem comparison_transpose (S T : CoefficientClosedStructure H)
    (A P Q : D) (f : T.tensor.obj (A, P) ⟶ Q) :
    S.transpose A P Q ((comparison S T).hom.app (A, P) ≫ f) =
      T.transpose A P Q f := by
  change (S.adjunction P).homEquiv A Q
    ((Adjunction.leftAdjointUniq (S.adjunction P) (T.adjunction P)).hom.app A ≫ f) = _
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact ((T.adjunction P).homEquiv_unit _ _ _).symm

/-- Inverse transport preserves the same tensor-Hom bijection.
Source: uniqueness of adjoints; Stacks 08J9.
(blueprint: lem-coef-closed-tensor-comparison). -/
theorem comparison_inv_transpose (S T : CoefficientClosedStructure H)
    (A P Q : D) (f : S.tensor.obj (A, P) ⟶ Q) :
    T.transpose A P Q ((comparison S T).inv.app (A, P) ≫ f) =
      S.transpose A P Q f := by
  rw [← comparison_transpose S T]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end WeilConjectures.CoefficientClosedStructure
