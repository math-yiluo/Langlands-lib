/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
import WeilConjectures.RingTheory.ProEtale.SpanIdempotents

/-! # Global bases of geometric coefficient Tate lines -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open WeilConjectures

namespace WeilConjectures.GeometricTateLine

private theorem fieldContractible (k : Type u) [Field k] [IsAlgClosed k] :
    IsWContractibleRing k := by
  apply IsWContractibleRing.of_forall_mem_span_isIdempotentElem (K := k)
    (E := {1})
  · intro e he
    simpa only [Set.mem_singleton_iff] using he ▸ IsIdempotentElem.one
  · intro x
    simpa only [smul_eq_mul, mul_one] using
      Submodule.smul_mem (Submodule.span k ({1} : Set k)) x
        (Submodule.subset_span (Set.mem_singleton 1))

/-- A global compatible root basis on a scheme over an algebraically closed field.
Source: the root tower construction in the Tate twist unit, geometric-field case.
(blueprint: lem-sf-geometric-tate-line-trivialization)

Proof: the field is weakly contractible. Choose a primitive root of order ell and
successively lift along ell-th power maps. Distinct powers have invertible
differences, including after applying the structure map to global sections.
The existing exponentiation basis therefore gives an isomorphism of the whole
constant residue and root diagrams, including their transition maps. -/
private theorem rootDiagram (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k)) :
    Nonempty (AlgebraicGeometry.ProEtale.tateRootsSystem X l ≅
      AlgebraicGeometry.ProEtale.constantTateResidueSystem X l) := by
  have := fieldContractible k
  obtain ⟨z, _, hstep, hpow, hdiff⟩ :=
    AlgebraicGeometry.ProEtale.exists_primitive_unit_tower k l hl
  let ψ : k →+* Γ(X, ⊤) :=
    (X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let w (n : ℕ) : Γ(X, ⊤)ˣ := Units.map ψ.toMonoidHom (z n)
  have hw (n : ℕ) : w n ^ (l ^ n) = 1 := by
    simpa only [map_pow, map_one] using congrArg (Units.map ψ.toMonoidHom) (hpow n)
  have hs (n : ℕ) : w (n + 1) ^ l = w n := by
    simpa only [map_pow] using congrArg (Units.map ψ.toMonoidHom) (hstep n)
  have hd (n a : ℕ) (ha : a < l ^ n) (b : ℕ) (hb : b < l ^ n) (hab : a ≠ b) :
      IsUnit ((w n : Γ(X, ⊤)) ^ a - (w n : Γ(X, ⊤)) ^ b) := by
    change IsUnit (ψ (z n : k) ^ a - ψ (z n : k) ^ b)
    rw [← map_pow, ← map_pow, ← map_sub]
    exact (hdiff n a ha b hb hab).map ψ
  exact ⟨(AlgebraicGeometry.ProEtale.rootsBasisIso X l w hw hs hd).symm⟩

private def unoverIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (T : C) (hT : IsTerminal T)
    (M N : SheafOfModules.{u + 1} R) (e : M.over T ≅ N.over T) : M ≅ N := by
  let i (V : Cᵒᵖ) : (Over T)ᵒᵖ := op (Over.mk (hT.from V.unop))
  let hom : M ⟶ N :=
    ⟨{ app := fun V ↦ e.hom.val.app (i V)
       naturality := by
         intro V W f
         exact e.hom.val.naturality (Over.homMk (U := (i W).unop) (V := (i V).unop)
           f.unop (hT.hom_ext _ _)).op }⟩
  let inv : N ⟶ M :=
    ⟨{ app := fun V ↦ e.inv.val.app (i V)
       naturality := by
         intro V W f
         exact e.inv.val.naturality (Over.homMk (U := (i W).unop) (V := (i V).unop)
           f.unop (hT.hom_ext _ _)).op }⟩
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        exact congrArg (fun f ↦ f.val.app (i V)) e.hom_inv_id
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        exact congrArg (fun f ↦ f.val.app (i V)) e.inv_hom_id }

/-- Every signed completed coefficient Tate line has a global basis over a
geometric field. The basis need not respect arithmetic Frobenius.
Source: the root-tower construction and scalar extension of a rank-one basis.
(blueprint: lem-sf-geometric-tate-line-trivialization)

Proof: use the global compatible root diagram. Restrict to the terminal object
of the pro-etale site and compare its root and coefficient diagrams. Taking
limits gives a basis of the completed integral root module. Extend scalars to
the given finite coefficient field and take signed powers of the basis. Finally
restriction to the terminal slice loses no sections or arrows, so the slice
isomorphism gives an isomorphism of the original module sheaves. -/
theorem integral_line_trivial (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m : ℤ) : Nonempty (integralTwistLine l E X m ≅
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X)) := by
  let U : X.ProEt := ProEt.mk (𝟙 X)
  let a := (rootDiagram k X l hl).some
  let F := AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1} (𝟙 X)
  let q := AlgebraicGeometry.Scheme.localTowerIso X l U
    (Functor.isoWhiskerRight a F)
  let b := AlgebraicGeometry.Scheme.completedBasis X l U q
  let c := (AlgebraicGeometry.Scheme.tateIntegralTrivial X l E U b).some
  let d := WeilConjectures.lineSignedOverUnit X
    (completedIntegralCommRingSheafUnrestricted l E X) (purTwistIntegralModule X l E)
    U c m
  exact ⟨unoverIso _ U (MorphismProperty.Over.mkIdTerminal @WeaklyEtale X) _ _ d⟩

end WeilConjectures.GeometricTateLine
