/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMatesData

/-! # Canonical finite evaluation of an integral scalar functor

Source: Zheng, Construction 4.1 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-reduction-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Lift the canonical ambient reduction comparison through the full finite inclusion.
Source: Zheng, Construction 4.1 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-reduction-evaluation). -/
def integralReductionEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) (side : Bool)
    (R : Reconstruction l E (endpoint X Y side)) :
    (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side).functor ≅
      R.equivalence.functor ⋙ R.evaluation n :=
  Functor.fullyFaithfulCancelRight
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
      (endpoint X Y side)).ι
    (eqToIso (d.finiteScalar_eq (s := .integral E) E ⟨n + 1, Nat.succ_pos n⟩
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side) ≪≫
      isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier (endpoint X Y side)).ι
        (PurCompactSupport.finiteReductionIso l E.carrier (endpoint X Y side) n) ≪≫
      (R.evaluationRealization l E (endpoint X Y side) n).symm)

/-- The lifted evaluation has exactly the prescribed ambient normalization.
Source: Zheng, Construction 4.1 and Proposition 5.26.
Proof: the inclusion maps its preimage to the given ambient map. Expanding the inverse
of the three-factor comparison gives reconstruction evaluation, the inverse canonical
comparison of derived quotient tensors, and the inverse scalar equality realization.
(blueprint: lem-sf-exceptional-integral-reduction-evaluation). -/
theorem integralReductionEvaluation_normalized {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) (side : Bool)
    (R : Reconstruction l E (endpoint X Y side))
    (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
      (endpoint X Y side)).ι.map
        ((integralReductionEvaluation l Ω d E n side R).inv.app K) =
      (R.evaluationRealization l E (endpoint X Y side) n).hom.app K ≫
        (PurCompactSupport.finiteReductionIso l E.carrier (endpoint X Y side) n).inv.app K.obj ≫
        (eqToIso (d.finiteScalar_eq (s := .integral E) E ⟨n + 1, Nat.succ_pos n⟩
          (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
          (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side)).inv.app K := by
  simp only [integralReductionEvaluation, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage, Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv,
    whiskerLeft_app, Iso.symm_inv, Category.assoc, ObjectProperty.ι_obj]

end WeilConjectures.ExceptionalIntegralScalar
