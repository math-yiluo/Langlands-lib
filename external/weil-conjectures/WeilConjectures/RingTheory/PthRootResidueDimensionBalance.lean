/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PthRootResidueDifferentials
import WeilConjectures.RingTheory.PthRootCotangentDimension
import WeilConjectures.RingTheory.ResidueConormalSnakeSequence
import WeilConjectures.AlgebraicGeometry.CartierEquality
import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import WeilConjectures.FieldTheory.PthRootsExtensionDegree
import WeilConjectures.RingTheory.JacobiZariskiConnectingMapNaturality
import WeilConjectures.RingTheory.JacobiZariskiHomologySequence
import WeilConjectures.RingTheory.PurelyInseparableBaseChangeLocalRing
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP
public import Mathlib.Algebra.Exact.Sequence

/-! # Dimension balance for p-root residue differential comparisons

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

private theorem finite_of_exact
    {F M N P : Type*} [Field F]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module F M] [Module F N] [Module F P]
    [Module.Finite F M] [Module.Finite F P]
    (f : M →ₗ[F] N) (g : N →ₗ[F] P) (hex : Function.Exact f g) :
    Module.Finite F N := by
  have hex' : Function.Exact f g.rangeRestrict := by
    intro x
    change (⟨g x, g.mem_range_self x⟩ : g.range) = 0 ↔ _
    simpa only [Subtype.ext_iff, ZeroMemClass.coe_zero] using hex x
  exact Module.Finite.of_exact hex' g.surjective_rangeRestrict

/-- For the p-root extension associated to independent base-field differentials,
geometric regularity balances the kernel and cokernel dimensions of the residue
comparison of absolute differentials.

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), the big
conormal diagram and its snake sequence.
(blueprint: lem-weil-pbc-pth-root-residue-dimension-balance).

Proof: Independence gives degree p^n for the extension of k obtained by adjoining
the roots (07DZ). Compare the monomial spanning family of the polynomial quotient
with this degree to identify the quotient over k with that field. The quotient B
over A is its base change. Geometric regularity makes both A and B regular; to get
regularity of A use the trivial extension, with the universe lift and the tensor
left-unit isomorphism. The finite flat map A → B has zero-dimensional closed fibre,
so the flat height formula gives equal dimensions. The conormal spaces therefore
have equal finite dimensions. The residue field extension L/K is finite.
For each local ring, Jacobi-Zariski, vanishing of prime-field H1 for fields, and the
surjection conormal identification give the short exact conormal row. Extend the
A-row from K to L; this is exact since L is flat over K. Functoriality of the
connecting maps gives the commuting diagram with vertical maps alpha, beta, gamma,
where beta is residueDifferentialComparison. Alpha goes between equally dimensional
conormal spaces. For gamma the field Jacobi-Zariski sequence identifies its kernel
with H1(L/K) and its cokernel with Omega[L/K]; Cartier equality makes these finite
and equally dimensional. The snake sequence is exact and all its terms are finite:
for beta use exactness and the finite conormal and field-homology terms. The
alternating sum of dimensions in
this sequence gives dim ker beta = dim coker beta. This argument includes n = 0,
when beta is an isomorphism. It assumes no finiteness of the absolute differential
modules themselves. -/
theorem pthRoot_residue_dimension_balance
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hA : IsGeometricallyRegular k A) (n : ℕ) (a : Fin n → k) :
    letI := ZMod.algebra k p
    letI := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    let B := pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i))
    ∀ [IsLocalRing B] [IsLocalHom (algebraMap A B)],
    LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) →
    let L := IsLocalRing.ResidueField B
    let β := residueDifferentialComparison p A B
    Module.finrank L β.ker =
      Module.finrank L ((L ⊗[B] KaehlerDifferential (ZMod p) B) ⧸ β.range) := by
  let := ZMod.algebra k p
  let := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
  let B := pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i))
  dsimp only
  intro hlocal hmap hind
  let K := IsLocalRing.ResidueField A
  let L := IsLocalRing.ResidueField B
  obtain ⟨hfinite, hdim⟩ := pthRoot_cotangent_dimension k A p hA n a hind
  let : Module.Finite K L := hfinite
  have : IsNoetherianRing B := inferInstance
  obtain ⟨α, f₀, f₁, f₂, f₃, f₄, hinj, hex₁, hex₂, hex₃, hex₄, hsurj⟩ :=
    residue_conormal_snake_sequence p A B
  obtain ⟨hΩ, hH, _, hcartier⟩ := cartier_equality K L (IntermediateField.fg_top K L)
  let := hΩ
  let := hH
  let β := residueDifferentialComparison p A B
  have : Module.Finite L β.ker := finite_of_exact f₀ f₁ hex₁
  have : Module.Finite L ((L ⊗[B] KaehlerDifferential (ZMod p) B) ⧸ β.range) :=
    Module.Finite.of_exact hex₄ hsurj
  have hα : Module.finrank L α.ker =
      Module.finrank L (IsLocalRing.CotangentSpace B ⧸ α.range) := by
    have hi := LinearMap.index_eq_of_finiteDimensional (f := α)
    rw [LinearMap.index_eq_finrank_sub, hdim] at hi
    dsimp only [L, B] at *
    omega
  have heuler := Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six
    f₀ f₁ f₂ f₃ f₄ hinj hex₁ hex₂ hex₃ hex₄ hsurj
  have hγ := hcartier inferInstance
  change Module.finrank L β.ker = _
  dsimp only [β, L, K, B] at *
  omega

end Algebra
