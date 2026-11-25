/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Splitting a complex over a field into its cohomology

Source: Stacks Project, More on Algebra, Tag 0BCC, first paragraph of the proof.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

/-- A zero-differential complex with prescribed finite cohomology dimensions maps
quasi-isomorphically to the original complex over a field.
Source: Stacks Project, More on Algebra, Tag 0BCC, first paragraph of the proof
(blueprint: lem-sc-residue-cohomology-zero-complex).

Proof: In degree i the finite-dimensional term E_i and H^i(C) have equal dimension,
so choose a linear isomorphism e_i between them. Vector spaces are projective;
therefore e_i lifts through the epimorphism Z^i(C) → H^i(C) to a map s_i into
cycles. Compose s_i with the cycle inclusion into C_i. These maps form a chain
map E → C because E has zero differentials and the images lie in cycles.
Naturality of the homology projection identifies its induced cohomology map
with e_i, through the cycle and homology isomorphisms of the zero-differential
complex E. Thus it is a quasi-isomorphism. No boundedness is needed. -/
theorem exists_quasiIso_from_zeroDifferential
    {κ : Type u} [Field κ]
    (C E : CochainComplex (ModuleCat.{max u v} κ) ℤ) (d : ℤ → ℕ)
    (hfinite : ∀ i : ℤ, Module.Finite κ (C.homology i))
    (hd : ∀ i : ℤ, d i = Module.finrank κ (C.homology i))
    (hzero : ∀ i j : ℤ, E.d i j = 0)
    (hterms : ∀ i : ℤ,
      Nonempty (E.X i ≅ ModuleCat.of κ (ULift.{v} (Fin (d i) → κ)))) :
    ∃ φ : E ⟶ C, QuasiIso φ := by
  classical
  have (i : ℤ) : Module.Finite κ (C.homology i) := hfinite i
  have (i : ℤ) : Module.Finite κ (E.X i) :=
    Module.Finite.equiv (hterms i).some.toLinearEquiv.symm
  let e (i : ℤ) : E.X i ≅ C.homology i :=
    (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (show Module.finrank κ (E.X i) = Module.finrank κ (C.homology i) by
        rw [(hterms i).some.toLinearEquiv.finrank_eq, ULift.moduleEquiv.finrank_eq]
        simpa using hd i))).toModuleIso
  let s (i : ℤ) : E.X i ⟶ C.cycles i :=
    Projective.factorThru (e i).hom (C.homologyπ i)
  let φ : E ⟶ C :=
    { f := fun i ↦ s i ≫ C.iCycles i
      comm' := fun i j _ ↦ by simp [hzero, Category.assoc] }
  refine ⟨φ, ?_⟩
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hcycles : HomologicalComplex.cyclesMap φ i = E.iCycles i ≫ s i := by
    rw [← cancel_mono (C.iCycles i), HomologicalComplex.cyclesMap_i]
    rfl
  have hhomology : E.homologyπ i ≫ HomologicalComplex.homologyMap φ i =
      E.iCycles i ≫ (e i).hom := by
    rw [HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc]
    exact congrArg (E.iCycles i ≫ ·) (Projective.factorThru_comp (e i).hom (C.homologyπ i))
  have : IsIso (E.iCycles i) := E.isIso_iCycles i _ rfl (hzero _ _)
  have : IsIso (E.homologyπ i) := E.isIso_homologyπ _ i rfl (hzero _ _)
  have : IsIso (E.homologyπ i ≫ HomologicalComplex.homologyMap φ i) := by
    rw [hhomology]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.homologyπ i) (HomologicalComplex.homologyMap φ i)

end CochainComplex
