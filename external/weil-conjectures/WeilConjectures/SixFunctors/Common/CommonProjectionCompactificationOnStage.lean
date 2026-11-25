/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionCoherence
import WeilConjectures.SixFunctors.Common.CommonProjectionTensorCompatibility

/-! # Projection comparison equations on finite coefficient models

Source: thm-sf-pf-field.proof.md, Compatibility and the common finite coefficient
field paragraph, and fix-prop-projection-formula.proof.md, final coherence sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

open ProjectionCoefficientTransport

namespace CommonProjectionCompactificationTransport

section
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
  (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
    (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))

private theorem tensor_first (X : SixFunctorSpace D) {K K' : B X}
    (a : K ⟶ K') (L : B X) :
    (V X).map (((T X).map a).app L) ≫ (t X).hom.app (K', L) =
      (t X).hom.app (K, L) ≫ ((T' X).map ((V X).map a)).app ((V X).obj L) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, Category.comp_id] using
    (t X).hom.naturality (Prod.mkHom a (𝟙 L))

private theorem source_refinement {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map (((T Y).map ((S.comparison f c d).hom.app K)).app L) ≫
        (source C t f d K L).hom =
      (source C t f c K L).hom ≫
        ((T' Y).map ((S'.comparison f c d).hom.app ((V X).obj K))).app ((V Y).obj L) := by
  simp only [source, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← Category.assoc, tensor_first t, Category.assoc]
  rw [← NatTrans.comp_app, ← Functor.map_comp, C.compactification f c d K,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem target_refinement {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map ((S.comparison f c d).hom.app
        (((T X).obj K).obj ((S.pull f).obj L))) ≫ (target C t f d K L).hom =
      (target C t f c K L).hom ≫ (S'.comparison f c d).hom.app
        (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  simp only [target, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, C.compactification f c d, Category.assoc,
    ← (S'.comparison f c d).hom.naturality]
  simp only [Category.assoc]

private theorem refinement_transfer
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (hp : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (c : Compactification f.hom.left) (K : B X) (L : B Y),
      (V Y).map (compactSupportProjectionComponent A f c K L) ≫
          (target C t f c K L).hom =
        (source C t f c K L).hom ≫
          compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : B X) (L : B Y)
    (h : ((T Y).map ((S.comparison f c d).hom.app K)).app L ≫
        compactSupportProjectionComponent A f d K L =
      compactSupportProjectionComponent A f c K L ≫
        (S.comparison f c d).hom.app (((T X).obj K).obj ((S.pull f).obj L))) :
    ((T' Y).map ((S'.comparison f c d).hom.app ((V X).obj K))).app ((V Y).obj L) ≫
        compactSupportProjectionComponent A' f d ((V X).obj K) ((V Y).obj L) =
      compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L) ≫
        (S'.comparison f c d).hom.app
          (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  apply (cancel_epi (source C t f c K L).hom).1
  calc
    _ = (V Y).map (((T Y).map ((S.comparison f c d).hom.app K)).app L) ≫
        (V Y).map (compactSupportProjectionComponent A f d K L) ≫
        (target C t f d K L).hom := by
      rw [← Category.assoc, ← source_refinement C t, Category.assoc, hp]
    _ = (V Y).map (compactSupportProjectionComponent A f c K L) ≫
        (V Y).map ((S.comparison f c d).hom.app
          (((T X).obj K).obj ((S.pull f).obj L))) ≫
        (target C t f d K L).hom := by
      rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [target_refinement C t, ← Category.assoc, hp, Category.assoc]

end

end CommonProjectionCompactificationTransport

set_option backward.isDefEq.respectTransparency false in
/-- The compactification equation on two models included from one finite field.
Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient-field
paragraph, and fix-prop-projection-formula.proof.md, final coherence sentence.
(blueprint: lem-sf-common-projection-compactification-on-stage).
Proof: Apply inclusion to the finite-stage compactification equation. Use the canonical
common-stage tensor comparison on the two finite models, rather than an independently
chosen tensor isomorphism. The tensor normalizations and the canonical pullback-tensor
normalization identify the proper counit and open projection mates with the specified
common-stage projection. The support comparison is normalized on these models.
Naturality moves the tensor comparisons through the refinement components, and
commonStageComparison.compactification identifies the two refinement maps. The
resulting equation has the same invertible tensor/support comparison at both ends;
cancel these comparisons. This proves the displayed equation on the included models.
The calculation uses only forward functoriality, and includes equal compactifications,
zero objects and empty schemes. -/
theorem commonProjectionCompactification_onStage
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (hH : CompactSupportProjectionCoherence (H.coefficientStages E₀).rational
      (H.coefficientStages E₀).rationalTensor (H.coefficientStages E₀).rationalExchange
      (fun _ _ ↦ True))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left)
    (K₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
    (L₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀) :
    let K := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀;
    let L := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L₀;
      ((H.commonStageTensor Y).map ((H.commonStage.comparison f c d).hom.app K)).app L ≫
          compactSupportProjectionComponent H.commonStageExchange f d K L =
        compactSupportProjectionComponent H.commonStageExchange f c K L ≫
          (H.commonStage.comparison f c d).hom.app
            (((H.commonStageTensor X).obj K).obj ((H.commonStage.pull f).obj L)) := by
  obtain ⟨t, ht⟩ := commonProjectionTensorCompatibility H E₀
  exact CommonProjectionCompactificationTransport.refinement_transfer
    (H.commonStageComparison E₀) t (H.coefficientStages E₀).rationalExchange
    H.commonStageExchange ht f c d K₀ L₀
    (hH.compactification f c d K₀ L₀ trivial)

end WeilConjectures
