/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTensorLevel
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTransitionSquare

/-! Existence of the normalized coherent tensor tower comparison.

Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-iso-existence).
Proof: use the prescribed finite component at every natural-number level.  The
adjacent transition square packages these components with `NatTrans.ofOpSequence`;
`NatIso.ofComponents` then supplies the levelwise inverses and all remaining
naturality squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] pullbackTensorTensorTowerLevel pullbackTensorRestrictedTower
  integralOperationsTensorTowerFunctor in
/-- The prescribed finite components extend to a tower isomorphism.
Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-iso-existence).
Proof: `NatTrans.ofOpSequence` uses the adjacent transition square; the
levelwise isomorphisms are assembled by `NatIso.ofComponents`. -/
theorem pullbackTensorTensorTower_exists (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ∃ e : pullbackTensorRestrictedTower l E W
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q))) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P,Q),
      ∀ n : ℕ, e.app (op n) = pullbackTensorTensorTowerLevel l E W P Q n := by
  classical
  let F := pullbackTensorRestrictedTower l E W
    ((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj
      ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)))
  let G := (integralOperationsTensorTowerFunctor l E W).obj (P,Q)
  let L : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n) :=
    fun n ↦ pullbackTensorTensorTowerLevel l E W P Q n
  change ∃ e : F ≅ G, ∀ n : ℕ, e.app (op n) = L n
  let h : F ⟶ G :=
    NatTrans.ofOpSequence (fun n ↦ (L n).hom) (by
      intro n
      dsimp only [F, G, L]
      exact (pullbackTensorTensorTowerLevel_transition l E W P Q n).symm)
  let e : F ≅ G :=
    NatIso.ofComponents (fun n ↦ L n.unop) (fun f ↦ h.naturality f)
  have he (n : ℕ) : e.app (op n) = L n := by
    apply Iso.ext
    dsimp only [e]
    simpa only [Iso.app_hom, op_unop] using
      (NatIso.ofComponents_hom_app
        (fun n ↦ L n.unop) (fun f ↦ h.naturality f) (op n))
  exact ⟨e, he⟩

end WeilConjectures
