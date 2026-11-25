/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData

/-! Finite-stage component of ambient coefficient pullback.
Source: Stacks 03CB and 03D3.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-finite).

The proof compares the chosen ringed-site adjunction with the constant-sheaf
adjunction on the pro-etale terminal object.  The two left adjoints are uniquely
isomorphic, and the defining constant-section equation identifies that comparison
with `ringMap`; its component is therefore invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Finite coefficient pullback is invertible.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-finite) -/
theorem coefficientPullback_some_isIso {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    IsIso (ringMap ell E f (some n)) := by
  let A := CommRingCat.of (ULift.{t + 1}
    (Padic.coefficientExtensionRing ell E (n + 1)))
  let T : Y.ProEt := Scheme.ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT := hT.isTerminalObj (Scheme.proEtaleBaseChange f) _
  let aY := constantSheafAdj (Scheme.ProEt.topology Y)
    CommRingCat.{max u (t + 1)} hT
  let aX := constantSheafAdj (Scheme.ProEt.topology X)
    CommRingCat.{max u (t + 1)} hGT
  let a : ((constantSheaf (Scheme.ProEt.topology Y)
      CommRingCat.{max u (t + 1)}) ⋙ ringPull.{t, u} f (some n)) ⊣
      (sheafSections (Scheme.ProEt.topology X)
        CommRingCat.{max u (t + 1)}).obj
        (op ((Scheme.proEtaleBaseChange f).obj T)) :=
    (aY.comp (Adjunction.ofIsRightAdjoint (ringPush.{t, u} f (some n)))).ofNatIsoRight
      (Iso.refl _)
  let e := a.leftAdjointUniq aX
  have he : ringMap ell E f (some n) = e.hom.app A := by
    apply (a.homEquiv _ _).injective
    apply Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app a aX A).symm
    change (aY.homEquiv _ _)
      (((Adjunction.ofIsRightAdjoint (ringPush.{t, u} f (some n))).homEquiv _ _)
        (((Adjunction.ofIsRightAdjoint (ringPush.{t, u} f (some n))).homEquiv
          _ _).symm (ringUnit ell E f (some n)))) =
      aX.unit.app A
    rw [Equiv.apply_symm_apply]
    dsimp [aY, aX, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantSheafAdj (Scheme.ProEt.topology Y)
      CommRingCat.{max u (t + 1)} hT).homEquiv _ _
      (ringUnit ell E f (some n)) = _
    dsimp [ringUnit, ringComponent, coefficients]
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{max u (t + 1)} hT).homEquiv _ _
      (((sheafificationAdjunction (Scheme.ProEt.topology Y)
        CommRingCat.{max u (t + 1)}).homEquiv _ _)
        (((sheafificationAdjunction (Scheme.ProEt.topology Y)
          CommRingCat.{max u (t + 1)}).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

end WeilConjectures.AmbientPullbackTensor
