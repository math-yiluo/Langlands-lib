/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.Module.Lattice

/-!
# Finite sums of valuation-ring lattices

Source: Stacks Project, Tag 0AUW(3), and the blueprint main-20261015,
`sk-lem-stratified-lattice-trace.proof.md`, Local computation, second paragraph
(blueprint: lem-sfb-finite-sum-lattice).

All topologies in the statement are explicit: the coefficient field carries the metric
topology of its recorded absolute value, its powers carry product topologies, and the
integer ring and lattice submodules carry induced topologies.
-/

@[expose] public section

universe u v

namespace Padic

/-- A finite nonempty sum of full integral lattices has a full integral basis. Every
full integral basis of the sum or any summand gives a homeomorphism from the power of
the valuation ring to that submodule with its induced topology.

Source: Stacks Project, Tag 0AUW(3), and blueprint main-20261015,
`sk-lem-stratified-lattice-trace.proof.md`, Local computation, second paragraph
(blueprint: lem-sfb-finite-sum-lattice).

Proof: By `lem-weil-l-adic-extension-integers-dvr`, the coefficient ring is a DVR with
fraction field E. The finite union of the summand bases generates the sum, which is
torsion-free as a submodule of E^r. Nonemptiness supplies one summand, whose field basis
shows that the sum spans E^r. Apply `lem-sc-dvr-fg-torsionfree-free` to obtain a finite
integral basis. It spans over E, and clearing denominators in a field-linear relation
proves its field-linear independence. Equality of basis cardinalities from
`def-weil-vector-space-dimension` gives exactly r basis vectors.

For any full integral basis of the sum or a summand, its field basis defines an
E-linear automorphism of E^r. The recorded absolute value makes E complete and
nontrivially normed. By `lem-weil-pbc-finite-dimensional-linear-homeomorphism`, this
automorphism and its inverse are continuous. Restrict them to A^r and the lattice;
the basis property identifies the image with the lattice. The product of the subspace
topologies on A is the subspace topology on A^r in E^r, so both restrictions are continuous.
For r = 0, all modules and coordinate spaces are one-point spaces and the bases are empty. -/
theorem finite_sum_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (r : ℕ) (J : Type v) [Finite J] [Nonempty J]
    (Λ : J → Submodule (coefficientExtensionIntegers l E) (Fin r → E))
    (hΛ : ∀ j : J,
      ∃ b : Module.Basis (Fin r) (coefficientExtensionIntegers l E) (Λ j),
        ∃ c : Module.Basis (Fin r) E (Fin r → E),
          ∀ i : Fin r, (b i : Fin r → E) = c i) :
    (∃ b : Module.Basis (Fin r) (coefficientExtensionIntegers l E) ↥(⨆ j : J, Λ j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E),
        ∀ i : Fin r, (b i : Fin r → E) = c i) ∧
    ∀ N : Submodule (coefficientExtensionIntegers l E) (Fin r → E),
      (N = (⨆ j : J, Λ j) ∨ ∃ j : J, N = Λ j) →
      ∀ b : Module.Basis (Fin r) (coefficientExtensionIntegers l E) N,
        (∃ c : Module.Basis (Fin r) E (Fin r → E),
          ∀ i : Fin r, (b i : Fin r → E) = c i) →
        @IsHomeomorph (Fin r → coefficientExtensionIntegers l E) N
          (@Pi.topologicalSpace (Fin r) (fun _ ↦ coefficientExtensionIntegers l E)
            (fun _ ↦ TopologicalSpace.induced
              (fun a : coefficientExtensionIntegers l E ↦ (a : E))
              (@UniformSpace.toTopologicalSpace E
                (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)))
          (TopologicalSpace.induced (fun x : N ↦ (x : Fin r → E))
            (@Pi.topologicalSpace (Fin r) (fun _ ↦ E)
              (fun _ ↦ @UniformSpace.toTopologicalSpace E
                (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)))
          b.equivFun.symm := by
  classical
  let A := coefficientExtensionIntegers l E
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsFractionRing A E := h.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := h.2.2.2.2.2.2.2.2.1
  have hfg (j : J) : (Λ j).FG := by
    obtain ⟨b, _, _⟩ := hΛ j
    let := Module.Finite.of_basis b
    exact Module.Finite.iff_fg.mp inferInstance
  have hspan (j : J) : Submodule.span E (Λ j : Set (Fin r → E)) = ⊤ := by
    obtain ⟨b, c, hc⟩ := hΛ j
    apply top_unique
    rw [← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    rw [← hc i]
    exact (b i).property
  let : Submodule.IsLattice E (⨆ j : J, Λ j) := {
    fg := Submodule.fg_iSup Λ hfg
    span_eq_top := by
      obtain ⟨j⟩ := ‹Nonempty J›
      apply top_unique
      rw [← hspan j]
      exact Submodule.span_mono (le_iSup Λ j) }
  constructor
  · let b := Module.finBasisOfFinrankEq A ↥(⨆ j : J, Λ j)
      (by simpa using Submodule.IsLattice.finrank_of_pi E (⨆ j : J, Λ j))
    exact ⟨b, b.extendOfIsLattice E, fun i ↦
      (Module.Basis.extendOfIsLattice_apply E b i).symm⟩
  · intro N _ b hb
    obtain ⟨c, hc⟩ := hb
    let : NormedField E := (coefficientExtensionAbsoluteValue l E).toNormedField
    let : TopologicalSpace A := TopologicalSpace.induced (fun a : A ↦ (a : E))
      inferInstance
    let : TopologicalSpace N := TopologicalSpace.induced
      (fun x : N ↦ (x : Fin r → E)) inferInstance
    have hcomm (a : Fin r → A) :
        (b.equivFun.symm a : Fin r → E) =
          c.equivFun.symm (fun i ↦ (a i : E)) := by
      simp only [Module.Basis.equivFun_symm_apply]
      simp [hc, Subring.smul_def]
    have hcoords (x : N) :
        (fun i ↦ (b.equivFun x i : E)) = c.equivFun (x : Fin r → E) := by
      apply c.equivFun.symm.injective
      rw [← hcomm, b.equivFun.symm_apply_apply, c.equivFun.symm_apply_apply]
    have hf : Continuous b.equivFun.symm := by
      apply continuous_induced_rng.mpr
      change Continuous (fun a : Fin r → A ↦ (b.equivFun.symm a : Fin r → E))
      simp_rw [hcomm]
      exact c.equivFun.symm.toLinearMap.continuous_on_pi.comp
        (continuous_pi fun i ↦ continuous_induced_dom.comp (continuous_apply i))
    have hg : Continuous b.equivFun := by
      apply continuous_pi
      intro i
      apply continuous_induced_rng.mpr
      change Continuous (fun x : N ↦ (b.equivFun x i : E))
      simp_rw [fun x ↦ congrFun (hcoords x) i]
      exact (continuous_apply i).comp
        (c.equivFun.toLinearMap.continuous_on_pi.comp continuous_induced_dom)
    let e : (Fin r → A) ≃ₜ N :=
      { b.equivFun.symm.toEquiv with continuous_toFun := hf, continuous_invFun := hg }
    exact e.isHomeomorph

end Padic
