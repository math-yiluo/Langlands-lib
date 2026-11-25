/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.AbelianOpenExtensionByZero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension

import WeilConjectures.Topology.ConstantIntegerOpenExtensionComparison
import WeilConjectures.Topology.IrreducibleOpenComplementDimension
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import WeilConjectures.Topology.NoetherianOpenClosedCohomologySequence
import WeilConjectures.Topology.IrreducibleNoetherianConstantAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Integer extension-by-zero generators in the dimension induction

Source: Stacks Project, Cohomology, Proposition 02UZ, irreducible case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

set_option linter.unusedVariables false in
/-- Lower-dimensional vanishing kills the integer extension-by-zero generators
on an irreducible Noetherian space.
Source: Stacks Project, Cohomology, Proposition 02UZ, final two paragraphs
(https://stacks.math.columbia.edu/tag/02UZ).
(blueprint: new-node-irreducible-integer-extension-vanishing).

Proof: If U is empty its extension by zero is zero. Otherwise U is dense by
irreducibility. For d=0 every nonempty open is X: a nonempty proper closed
subset would contain an irreducible closed subset, giving a chain of length one.
Thus the generator is the constant integer sheaf and constant-sheaf acyclicity
kills its degree-p cohomology since p>0. For d>0 put Z = X \ U. It is a closed
Noetherian subspace of dimension at most d-1: append X to any irreducible closed
chain in Z. Use the short exact sequence from the open-closed decomposition of
the constant integer sheaf. The terms are j_!Z_U, Z_X, and i_*Z_Z, since inverse
image of a constant sheaf is constant. Constant-sheaf acyclicity kills H^p(X,Z_X).
Closed-pushforward comparison identifies H^(p-1)(X,i_*Z_Z) with H^(p-1)(Z,Z_Z).
The lower-dimensional hypothesis with e=d-1 kills this term, because p>d implies
p-1>d-1. The exact segment from these two outer terms to H^p(X,j_!Z_U) proves
that the latter is zero. The empty closed complement causes no problem: its
cohomology is zero by the same lower-dimensional hypothesis (or the empty axiom).
Only integer constant extensions are treated here; arbitrary sheaves are handled
separately by Lemma 02UX. -/
theorem irreducible_integer_extension_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hlower : ∀ (e : ℕ), e < d →
      ∀ (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y]
        (hdimY : topologicalKrullDim Y ≤ (e : WithBot ℕ∞))
        (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (r : ℕ), e < r → IsZero (CategoryTheory.Sheaf.H' G r (⊤ : Opens Y)))
    (p : ℕ) (hp : d < p) (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsZero (CategoryTheory.Sheaf.H'
      ((TopCat.Sheaf.abelianOpenExtensionByZero U).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) p
      (⊤ : Opens X)) := by
  let C := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let E := (TopCat.Sheaf.abelianOpenExtensionByZero U).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  let Q := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj (⊤ : Opens X))
  let H := fun n : ℕ ↦ CategoryTheory.Abelian.extFunctorObj.{u, u, u + 1} Q n
  by_cases hEmpty : U = ⊥
  · have hE : IsZero E := by
      apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero E).2
      intro x
      exact (TopCat.Sheaf.abelianOpenExtensionByZero_stalks X U).choose_spec.2.2.1
        _ x (by simp [hEmpty])
    exact (H p).map_isZero hE
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le d) hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp0)
  let Z := TopCat.of ↥((U : Set X)ᶜ)
  let i : Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : Topology.IsClosedEmbedding i := U.isOpen.isClosed_compl.isClosedEmbedding_subtypeVal
  obtain ⟨a, _, ⟨ha, hS⟩, _⟩ := noetherian_open_closed_cohomology_sequence X U C
  let S := ShortComplex.mk a
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app C) ha
  have hSC : S.ShortExact := hS
  have hLast : IsZero (CategoryTheory.Sheaf.H'.{u, u, u} S.X₃ n ⊤) := by
    let G := (TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj C
    have hG : IsZero (CategoryTheory.Sheaf.H'.{u, u, u} G n ⊤) := by
      rcases irreducible_open_complement_dimension X d hdim U hEmpty with hz | ⟨e, he, hdimZ⟩
      · have := hz
        have hzero : IsZero G := by
          apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero G).2
          intro z
          exact isEmptyElim z
        exact (CategoryTheory.Abelian.extFunctorObj _ n).map_isZero hzero
      · exact hlower e he Z hdimZ G n (by omega)
    let eG : (CategoryTheory.Sheaf.H'.{u, u, u} G n ⊤) ≃
        (@CategoryTheory.Sheaf.H' (Opens Z) _ (Opens.grothendieckTopology Z) _
          (HasExt.standard _) G n ⊤) :=
      @CategoryTheory.Abelian.Ext.chgUniv _ _ _ inferInstance (HasExt.standard _) _ _ n
    have := AddCommGrpCat.subsingleton_of_isZero hG
    have := eG.symm.subsingleton
    have hGbig := AddCommGrpCat.isZero_of_subsingleton
      (@CategoryTheory.Sheaf.H' (Opens Z) _ (Opens.grothendieckTopology Z) _
          (HasExt.standard _) G n ⊤)
    obtain ⟨comparison⟩ := cohomology_closed_immersion_pushforward i hi G n
    have hBig := hGbig.of_iso comparison.symm
    have := AddCommGrpCat.subsingleton_of_isZero hBig
    let eLast : (CategoryTheory.Sheaf.H'.{u, u, u} S.X₃ n ⊤) ≃
        (@CategoryTheory.Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _
          (HasExt.standard _) S.X₃ n ⊤) :=
      @CategoryTheory.Abelian.Ext.chgUniv _ _ _ inferInstance (HasExt.standard _) _ _ n
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    exact eLast.subsingleton_congr.mpr (AddCommGrpCat.subsingleton_of_isZero hBig)
  have hMiddle : Subsingleton (CategoryTheory.Sheaf.H'.{u, u, u} S.X₂ (n + 1) ⊤) :=
    irreducible_noetherian_constant_acyclic X (ULift.{u} ℤ) (n + 1) (by omega)
  have hFirst : IsZero (CategoryTheory.Sheaf.H'.{u, u, u} S.X₁ (n + 1) ⊤) := by
    have hM : Subsingleton (CategoryTheory.Abelian.Ext.{u} Q S.X₂ (n + 1)) := hMiddle
    have hL : Subsingleton (CategoryTheory.Abelian.Ext.{u} Q S.X₃ n) :=
      AddCommGrpCat.subsingleton_of_isZero hLast
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ _ hSC x
      (hM.elim _ _) (n₀ := n) rfl
    rw [← hy, hL.elim y 0]
    simp
  obtain ⟨comparison⟩ := constant_integer_open_extension_comparison X U
  exact hFirst.of_iso ((H (n + 1)).mapIso comparison)

end TopCat
