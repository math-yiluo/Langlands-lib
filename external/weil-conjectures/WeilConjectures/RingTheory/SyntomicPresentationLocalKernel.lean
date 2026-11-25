/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicFibreKernelGenerators
import WeilConjectures.RingTheory.SyntomicLocalKernelIntersection
import Mathlib.RingTheory.Nakayama

/-!
# Bounded generators of a syntomic presentation kernel at a prime

Source: Stacks Project, Algebra, Tag 00SY,
proof of (3) implies (2), before clearing denominators.
(blueprint: lem-weil-pbc-syntomic-presentation-local-kernel).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

/-- A fixed finite polynomial presentation has at most `n` kernel generators locally
at a syntomic point.
Source: Stacks Project, Tag 00SY, proof of (3) implies (2).
(blueprint: lem-weil-pbc-syntomic-presentation-local-kernel).

Proof: Reduce the presentation to the residue field of the base prime. The conormal
rank theorem 00SC gives a basis of size `c ≤ n` at the fibre prime. Lift its basis
vectors to `c` elements of the original kernel, clearing unit denominators. Nakayama
makes their reductions generate the fibre ideal locally. In the polynomial local ring
at the inverse-image prime, quotient by the lifted elements. The remaining kernel is
finite as a module over the polynomial local ring, since the original kernel is finite.
Coefficient reduction identifies this local ring modulo the base maximal ideal with the
polynomial fibre local ring: coefficients in the base residue field are fractions of
base elements, and clearing their finite sets of denominators gives this identification.
Flatness of the target over the base local ring makes tensoring its defining
exact sequence with the residue field left exact. Its reduction is zero by the chosen
fibre generators. Nakayama therefore kills this remaining kernel. This says precisely
that the two polynomial ideals have equal extensions to the polynomial local ring.
The hypotheses exclude the zero fibre at the chosen prime; `c = 0` is allowed and
then the conclusion says that the localized kernel vanishes. -/
theorem exists_bounded_local_kernel_generators
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ) (hfg : (RingHom.ker φ.toRingHom).FG)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      c ≤ n ∧ Ideal.span (Set.range f) ≤ RingHom.ker φ.toRingHom ∧
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (Ideal.span (Set.range f)) =
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) := by
  obtain ⟨c, f, hcn, hfI, hgen⟩ :=
    exists_bounded_fibre_kernel_generators q n φ hφ hci
  refine ⟨c, f, hcn, hfI, ?_⟩
  let A := Localization.AtPrime (q.asIdeal.comap φ.toRingHom)
  let I : Ideal A := Ideal.map (algebraMap _ A) (RingHom.ker φ.toRingHom)
  let J : Ideal A := Ideal.map (algebraMap _ A) (Ideal.span (Set.range f))
  let m : Ideal A := Ideal.map (algebraMap R A) (q.asIdeal.comap (algebraMap R S))
  have hJI : J ≤ I := Ideal.map_mono hfI
  have hinter : I ⊓ m = m * I := syntomic_local_kernel_intersection q n φ hφ hflat
  have hm : m ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff A
      (q.asIdeal.comap φ.toRingHom) _).mpr
    change φ (algebraMap R (MvPolynomial (Fin n) R) r) ∈ q.asIdeal
    simpa only [φ.commutes] using (show (algebraMap R S) r ∈ q.asIdeal from hr)
  have hsmall : I ≤ J ⊔ m * I := by
    rw [← hinter]
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hgen hx)
    have hzI : z ∈ I := by
      simpa only [add_sub_cancel_left] using I.sub_mem hx (hJI hy)
    exact Submodule.mem_sup.mpr ⟨y, hy, z, ⟨hzI, hz⟩, rfl⟩
  apply le_antisymm hJI
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (hfg.map (algebraMap _ A))
  · exact hm.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  · exact hsmall

end Algebra
