/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionCoherence
import WeilConjectures.SixFunctors.Common.CommonProjectionProperTensorCompatibility

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

namespace CommonProjectionProperTransport

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

private theorem proper_identification {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) (K : B X) :
    (V Y).map ((S.properIdentification f c).hom.app K) ≫
        (C.directAdjunction f).right.hom.app K =
      (C.supportAdjunction f c).left.hom.app K ≫
        (S'.properIdentification f c).hom.app ((V X).obj K) := by
  simp only [SixFunctorPushStage.properIdentification, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [C.properIdentity, ← Category.assoc, C.compactification, Category.assoc]

private theorem source_proper {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map (((T Y).map ((S.properIdentification f c).hom.app K)).app L) ≫
        (properSource C t f K L).hom =
      (source C t f c K L).hom ≫
        ((T' Y).map ((S'.properIdentification f c).hom.app ((V X).obj K))).app
          ((V Y).obj L) := by
  simp only [source, properSource, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.refl_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← Category.assoc, tensor_first t, Category.assoc]
  rw [← NatTrans.comp_app, ← Functor.map_comp, proper_identification C,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem target_proper {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsProper f.hom.left] (c : Compactification f.hom.left) (K : B X) (L : B Y) :
    (V Y).map ((S.properIdentification f c).hom.app
        (((T X).obj K).obj ((S.pull f).obj L))) ≫ (properTarget C t f K L).hom =
      (target C t f c K L).hom ≫ (S'.properIdentification f c).hom.app
        (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  simp only [target, properTarget, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, proper_identification C, Category.assoc,
    ← (S'.properIdentification f c).hom.naturality]
  simp only [Category.assoc]

private theorem proper_transfer
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (A' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' T' Q)
    (hp : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
      (c : Compactification f.hom.left) (K : B X) (L : B Y),
      (V Y).map (compactSupportProjectionComponent A f c K L) ≫
          (target C t f c K L).hom =
        (source C t f c K L).hom ≫
          compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L))
    (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
      (K : B X) (L : B Y),
      (V Y).map (compactSupportProperProjection A f K L) ≫
          (properTarget C t f K L).hom =
        (properSource C t f K L).hom ≫
          compactSupportProperProjection A' f ((V X).obj K) ((V Y).obj L))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y)
    (h : ((T Y).map ((S.properIdentification f c).hom.app K)).app L ≫
        compactSupportProperProjection A f K L =
      compactSupportProjectionComponent A f c K L ≫
        (S.properIdentification f c).hom.app (((T X).obj K).obj ((S.pull f).obj L))) :
    ((T' Y).map ((S'.properIdentification f c).hom.app ((V X).obj K))).app ((V Y).obj L) ≫
        compactSupportProperProjection A' f ((V X).obj K) ((V Y).obj L) =
      compactSupportProjectionComponent A' f c ((V X).obj K) ((V Y).obj L) ≫
        (S'.properIdentification f c).hom.app
          (((T' X).obj ((V X).obj K)).obj ((S'.pull f).obj ((V Y).obj L))) := by
  apply (cancel_epi (source C t f c K L).hom).1
  calc
    _ = (V Y).map (((T Y).map ((S.properIdentification f c).hom.app K)).app L) ≫
        (V Y).map (compactSupportProperProjection A f K L) ≫
        (properTarget C t f K L).hom := by
      rw [← Category.assoc, ← source_proper C t, Category.assoc, hq]
    _ = (V Y).map (compactSupportProjectionComponent A f c K L) ≫
        (V Y).map ((S.properIdentification f c).hom.app
          (((T X).obj K).obj ((S.pull f).obj L))) ≫
        (properTarget C t f K L).hom := by
      rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [target_proper C t, ← Category.assoc, hp, Category.assoc]

end

end CommonProjectionProperTransport

set_option backward.isDefEq.respectTransparency false in
/-- The proper equation on two models included from one finite field.
Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient-field
paragraph, and fix-prop-projection-formula.proof.md, final coherence sentence.
(blueprint: lem-sf-common-projection-proper-on-stage).
Proof: Apply inclusion to the finite-stage proper equation. The compactification square
and properIdentity square of commonStageComparison carry properIdentification to its
specified common-stage counterpart. The comparison of direct adjunctions preserves
the counit, so the normalized canonical tensor/pullback comparisons carry the proper
projection mate itself to the common-stage proper projection. The same comparison
for the compactification square carries its proper-then-open projection mate to the
common-stage component. Naturality moves the tensor comparisons past the proper
identification; cancel the common invertible endpoint comparisons. This is exactly
the displayed equation. Identity-open compactifications, zero inputs and empty
schemes use the same adjunction identities and require no separate assumption. -/
theorem commonProjectionProper_onStage
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (hH : CompactSupportProjectionCoherence (H.coefficientStages E₀).rational
      (H.coefficientStages E₀).rationalTensor (H.coefficientStages E₀).rationalExchange
      (fun _ _ ↦ True))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left)
    (K₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
    (L₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀) :
    let K := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀;
    let L := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L₀;
      ((H.commonStageTensor Y).map ((H.commonStage.properIdentification f c).hom.app K)).app L ≫
          compactSupportProperProjection H.commonStageExchange f K L =
        compactSupportProjectionComponent H.commonStageExchange f c K L ≫
          (H.commonStage.properIdentification f c).hom.app
            (((H.commonStageTensor X).obj K).obj ((H.commonStage.pull f).obj L)) := by
  obtain ⟨t, hp, hq⟩ := commonProjectionProperTensorCompatibility H E₀
  exact CommonProjectionProperTransport.proper_transfer (H.commonStageComparison E₀) t
    (H.coefficientStages E₀).rationalExchange H.commonStageExchange
    (fun f _ c K L ↦ hp f c K L) hq f c K₀ L₀
    (hH.proper f c K₀ L₀ trivial)

end WeilConjectures
