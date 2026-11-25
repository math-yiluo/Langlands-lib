/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat

/-!
# Descent of normality under scalar field extension

Source: Stacks Project, Algebra, Tag 033G (lemma-descent-normal), specialized to scalar
field extension (blueprint: lem-weil-pbc-normal-ring-field-extension-descent).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem integrallyClosed_of_faithfullyFlat
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [IsDomain A] [IsDomain C] [IsIntegrallyClosed C] :
    IsIntegrallyClosed A := by
  let K := FractionRing A
  let L := FractionRing C
  let g : A →ₐ[A] L := Algebra.ofId A L
  have hg : Function.Injective g :=
    (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective A C)
  let φ : K →ₐ[A] L := IsFractionRing.liftAlgHom (g := g) hg
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  have hy : IsIntegral C (φ x) := (hx.map φ).tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hgb0 : g b ≠ 0 := by
    exact (map_ne_zero_iff g hg).mpr hb0
  have heq : algebraMap C L (algebraMap A C a) =
      algebraMap C L (algebraMap A C b * s) := by
    have hφ : φ (algebraMap A K a / algebraMap A K b) = g a / g b := by
      simp [φ, g]
    have he := (div_eq_iff hgb0).mp (hφ.symm.trans hs.symm)
    simpa [g, IsScalarTower.algebraMap_apply A C L, mul_comm] using he
  have heqC : algebraMap A C a = algebraMap A C b * s :=
    IsFractionRing.injective C L heq
  have ha : a ∈ Ideal.span ({b} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) (Ideal.span ({b} : Set A))]
    change algebraMap A C a ∈ Ideal.map (algebraMap A C) (Ideal.span ({b} : Set A))
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, heqC⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, ?_⟩
  rw [hr, map_mul, mul_div_cancel_left₀]
  exact (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hb0

/-- Normality of a commutative algebra descends along an arbitrary scalar field extension.
Normality means that every prime localization is an integrally closed domain.

Source: Stacks Project, Algebra, Tag 033G (lemma-descent-normal).
(blueprint: lem-weil-pbc-normal-ring-field-extension-descent).

Proof:
1. Set S = B ⊗[F] E. The map i : B → S, b ↦ b ⊗ 1, is faithfully flat by
   lem-weil-pbc-field-extension-base-change-faithfully-flat, hence flat by
   def-weil-pbc-faithfully-flat-ring-map. For any prime p of B, lift p to a prime q of S
   by lem-weil-pbc-faithfully-flat-surjective-spectrum.
2. Put A = B_p and C = S_q. By lem-weil-pbc-flat-local-ring-maps the induced map
   j : A → C is flat and local, so lem-weil-pbc-flat-local-hom-faithfully-flat makes it
   faithfully flat. Normality of S says that C is an integrally closed domain.
3. Apply lem-weil-pbc-faithfully-flat-ideal-contraction to the zero ideal to see that
   j is injective. Since C is a domain, injectivity shows that A is a domain too.
4. An element x = a/b of Frac(A) integral over A maps to j(a)/j(b) in Frac(C).
   Injectivity preserves nonzero denominators and gives an injective fraction-field map.
   Mapping the monic equation shows that this image is integral over C. As C is
   integrally closed, it equals s/1 for some s in C, and j(a) = j(b)s.
5. Thus j(a) belongs to the extension of the principal ideal bA. By
   lem-weil-pbc-faithfully-flat-ideal-contraction, a belongs to bA, so a = br for some
   r in A and x = r/1 in Frac(A).
6. Hence A is integrally closed. Since p was arbitrary, def-weil-pbc-normal-ring says
   that B is normal. For B = 0 there are no primes and the conclusion is vacuous. -/
theorem normal_ring_of_normal_tensor_field
    (F : Type u) (E : Type v) (B : Type w)
    [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
    (h : ∀ (q : Ideal (B ⊗[F] E)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let S := B ⊗[F] E
  let : Module.FaithfullyFlat F E := inferInstance
  let : Module.FaithfullyFlat B S := inferInstance
  let f : B →+* S := algebraMap B S
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) p
  let : q.IsPrime := hq
  have hcomap : p = Ideal.comap f q := by simpa [f, Ideal.under] using hqp.over
  let j := Localization.localRingHom p q f hcomap
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := j.toAlgebra
  have hf : f.Flat := by
    rw [show f = algebraMap B S by rfl, RingHom.flat_algebraMap_iff]
    infer_instance
  have hjflat : j.Flat := RingHom.Flat.localRingHom (f := f) hf q p hcomap
  have hjflat' : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
    change RingHom.Flat j
    exact hjflat
  have hflocal : IsLocalHom j := inferInstance
  let : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    change IsLocalHom j
    exact hflocal
  let : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := hjflat'
  let : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hqnormal := h q
  let : IsDomain (Localization.AtPrime q) := hqnormal.1
  let : IsIntegrallyClosed (Localization.AtPrime q) := hqnormal.2
  have hji := FaithfulSMul.algebraMap_injective
    (Localization.AtPrime p) (Localization.AtPrime q)
  let : IsDomain (Localization.AtPrime p) := Function.Injective.isDomain _ hji
  exact ⟨inferInstance, integrallyClosed_of_faithfullyFlat
    (Localization.AtPrime p) (Localization.AtPrime q)⟩

end Algebra
