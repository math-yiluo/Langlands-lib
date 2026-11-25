/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData

/-! # The opposite compact-support mate for a regular quotient

Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-regular-quotient-opposite-compact-support-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The opposite mate of the prescribed left scalar comparison is invertible
under reverse regular-quotient adjunctions. No exceptional right mate appears here.
Source: Zheng, Lemma 5.22 and Proposition 5.26; Stacks Tags 07A6, 0A70, 0A71 and 0GL6.
Proof: identify both reverse adjunctions with shifted restriction using the regular
Koszul resolution of the actual quotient coefficient sheaf. The algebra-valued dual
of the quotient is its shift by [-1]; its augmentation and trace fix the reverse
unit and counit. Left-adjoint uniqueness transports these identifications to ax
and ay, so changing either presentation conjugates the mate by isomorphisms.
Transpose the normalized scalar-extension comparison in these Koszul coordinates.
Its forward scalar transpose is the actual proper/open restriction square, by
d.q_normalized and the left and scalar realization equations. In the opposite
transpose, the Koszul tensor/coinduction triangle identities cancel the duality
identifications. What remains is the inverse restriction square followed by [-1].
For the open factor this equation is fixed by the open adjunction unit. For the
proper factor it is fixed on K-injective representatives by the derived unit and
its ordinary sectionwise identity comparison. Naturality pastes the two equations;
shift compatibility identifies their composite with the shifted compact-support
restriction comparison. Each factor is invertible. Faithfulness of the finite-Tor
full inclusions reflects this invertibility on the restricted categories. Transport
by left-adjoint uniqueness then proves it for the specified ax and ay. Positivity
of n+1 ensures the regular resolution also covers n=0; zero objects and empty
schemes obey the same unit, trace and pasting identities.
(blueprint: lem-sf-regular-quotient-opposite-compact-support-mate). -/
theorem regularQuotientOppositeCompactSupportMate
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ)
    (RX : C.{u} l Ω X (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⥤
          C.{u} l Ω X (.integral E))
      (RY : C.{u} l Ω Y (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⥤
          C.{u} l Ω Y (.integral E))
      (ax : RX ⊣ (d.scalar (s := .integral E)
        (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) true).functor)
      (ay : RY ⊣ (d.scalar (s := .integral E)
        (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) false).functor) :
      IsIso ((mateEquiv ax ay).symm
        (d.q (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
          (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
          (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).inv) := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
