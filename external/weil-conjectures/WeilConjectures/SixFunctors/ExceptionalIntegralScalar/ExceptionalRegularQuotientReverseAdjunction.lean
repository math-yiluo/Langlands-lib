/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.RegularQuotientScalarRightAdjoint
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.RegularQuotientOppositeCompactSupportMate

/-! # Reverse scalar adjunction for a regular finite quotient

Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-regular-quotient-reverse-adjunction)
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

/-- Derived extension along the regular quotient has a reverse adjunction, and
its opposite compact-support mate is invertible.
Source: Zheng, Lemma 5.22 and Proposition 5.26; Stacks Tags 0A70, 0A71, 06YY and 07A6.
Proof: let A be the completed integral coefficient sheaf and let B be its
quotient by pi^(n+1), identified with the finite constant coefficient sheaf. The Koszul resolution
[A --pi^(n+1)--> A] of B has dual canonically B[-1]. Consequently derived
coinduction is derived extension followed by [-1], with the trace induced by the
Koszul augmentation. Restriction followed by [-1] is therefore left adjoint to
derived extension. Restriction sends a finite-Tor constructible B-complex to a
finite-Tor constructible A-complex: tensor the two-term finite-free resolution,
so its Tor interval enlarges by at most one; finite reduction and constructibility
are preserved. A bounded complex annihilated by pi^(n+1) is derived complete,
so the restricted object belongs to the integral category. Both reverse adjunctions
consequently restrict to the stated
categories. The proper/open restriction square is sectionwise identity before
deriving. Open extension is exact, and the separately derived proper square is
fixed by its K-injective unit normalization. Both commute with the shift.
Transpose the normalized scalar extension comparison under the two reverse
adjunctions. The Koszul tensor/coinduction adjunctions use the same augmentation
and trace; their two triangle identities cancel the duality identifications.
Thus its transpose is precisely the shifted proper/open restriction square.
This square is invertible. The normalized scalar realizations and faithful full
inclusions transport this equation to the specified left comparisons. No choice
of system evaluation or faithfulness of evaluation is needed. The zero object,
empty schemes and n = 0 use the same resolution and the same equations.
(blueprint: lem-sf-exceptional-regular-quotient-reverse-adjunction). -/
theorem exceptionalRegularQuotientReverseAdjunction
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
    (d : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) :
    ∃ (RX : C.{u} l Ω X (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⥤
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
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) false).functor),
      IsIso ((mateEquiv ax ay).symm
        (d.q (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
          (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
          (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).inv) := by
  let a := PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)
  let h := Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩
  obtain ⟨RX, ⟨ax⟩⟩ :=
    (regularQuotientScalarRightAdjoint l Ω E n X (d.scalar (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩) a h true)).exists_leftAdjoint
  obtain ⟨RY, ⟨ay⟩⟩ :=
    (regularQuotientScalarRightAdjoint l Ω E n Y (d.scalar (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩) a h false)).exists_leftAdjoint
  exact ⟨RX, RY, ax, ay,
    regularQuotientOppositeCompactSupportMate l Ω D hl c operation left d E n RX RY ax ay⟩

end WeilConjectures.ExceptionalIntegralScalar
