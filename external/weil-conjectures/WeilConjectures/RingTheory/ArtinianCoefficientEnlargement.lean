/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.ArtinianSeparableResidueLift
import WeilConjectures.RingTheory.ArtinianTranscendentalLocalization
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Generic Artinian coefficient enlargement

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FI, proof after introducing D.
(blueprint: lem-weil-pbc-artinian-coefficient-enlargement).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

private theorem pow_eq_of_residue_eq
    {S : Type u} [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    (p : ℕ) [Fact p.Prime] [CharP S p] {x y : S}
    (h : IsLocalRing.residue S x = IsLocalRing.residue S y) :
    ∃ e : ℕ, x ^ p ^ e = y ^ p ^ e := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal S).mp inferInstance
  have hmem : x - y ∈ IsLocalRing.maximalIdeal S := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, h, sub_self]
  have hbound : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hz := Ideal.pow_eq_zero_of_mem hN hbound hmem
  rw [sub_pow_char_pow x y N] at hz
  exact ⟨N, sub_eq_zero.mp hz⟩

private theorem exists_separable_pow
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] {a : E} (ha : IsAlgebraic F a) :
    ∃ e : ℕ, IsSeparable F (a ^ p ^ e) := by
  let K := IntermediateField.adjoin F {a}
  have : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional ha.isIntegral
  let aK : K := ⟨a, IntermediateField.mem_adjoin_simple_self F a⟩
  obtain ⟨e, b, hb⟩ := IsPurelyInseparable.pow_mem (separableClosure F K) p aK
  have hsep : IsSeparable F (aK ^ p ^ e) := by
    rw [← hb]
    exact (Algebra.IsSeparable.isSeparable F b).map
      (IsScalarTower.toAlgHom F (separableClosure F K) K)
        (IsScalarTower.toAlgHom F (separableClosure F K) K).injective
  refine ⟨e, ?_⟩
  exact hsep.map K.val K.val.injective

private theorem essentiallySmooth_of_smooth
    {R : Type u} [CommRing R] (S : Type (max u v)) [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] : Algebra.EssentiallySmooth R S := by
  refine ⟨S, inferInstance, inferInstance, inferInstance, ⊥, ?_⟩
  exact ⟨(IsLocalization.atUnits S (⊥ : Submonoid S) (S := Localization (⊥ : Submonoid S))
    (bot_le : (⊥ : Submonoid S) ≤ IsUnit.submonoid S)).restrictScalars R⟩


/-- Capture a power of an element in a flat local Artinian coefficient extension.
Source: Stacks Project, Lemma 07FI, proof after introducing D.
(blueprint: lem-weil-pbc-artinian-coefficient-enlargement).

Proof: Regard S as a D-algebra via g, and write F and E for their residue fields.
If the residue of x is algebraic over F, some p-power is separable over F. Apply the
separable residue lift to get a finite etale local Artinian D-algebra D' with a local
flat map g' to S and an element d whose residue is that of x raised to this power.
The maximal ideal of S is nilpotent. A further p-power therefore annihilates g'(d)
minus that power of x: Frobenius in characteristic p makes the two powers equal.
The resulting positive power of x belongs to g'(D'), and finite etale implies smooth,
hence essentially smooth. If the residue is transcendental, localize D[T] at the
inverse image of the target maximal ideal. The transcendental localization theorem
gives the local Artinian essentially smooth extension and its local flat evaluation
map. The image of T is x itself, so exponent one suffices. The algebraic/transcendental
dichotomy covers every x, including x=0; no invertibility hypothesis is needed. -/
theorem exists_artinian_coefficient_enlargement
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    (p : ℕ) [Fact p.Prime] [CharP S p]
    (g : D →+* S) [IsLocalHom g] (hgflat : g.Flat) (x : S) :
    ∃ (r : ℕ), 0 < r ∧
      ∃ (D' : Type (max u v w)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
        IsLocalRing D' ∧ IsArtinianRing D' ∧
        IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
        EssentiallySmooth D D' ∧ g'.Flat ∧
        g'.comp (algebraMap D D') = g ∧ x ^ r ∈ Set.range g' := by
  classical
  let : Algebra D S := g.toAlgebra
  have : IsLocalHom (algebraMap D S) := ‹IsLocalHom g›
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : CharP (IsLocalRing.ResidueField S) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (IsLocalRing.residue S), CharP.cast_eq_zero, map_zero])
  have : CharP (IsLocalRing.ResidueField D) p :=
    (IsLocalRing.ResidueField.map g).charP (IsLocalRing.ResidueField.map g).injective p
  by_cases ha : IsAlgebraic (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)
  · obtain ⟨e, hsep⟩ := exists_separable_pow p ha
    obtain ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hflat', hcomp,
      d, hd⟩ := exists_finiteEtale_artinian_residue_lift.{u, v, w}
        D S hgflat ((IsLocalRing.residue S x) ^ p ^ e) hsep
    let : CommRing D' := hD'
    let : Algebra D D' := hDD'
    have : IsLocalRing D' := hlocal
    have : IsArtinianRing D' := hart
    have : IsLocalHom (algebraMap D D') := hmap
    have : IsLocalHom g' := hg'
    have : Etale D D' := het
    obtain ⟨f, hf⟩ := pow_eq_of_residue_eq p
      (x := g' d) (y := x ^ p ^ e) (by simpa only [map_pow] using hd)
    refine ⟨p ^ e * p ^ f, Nat.mul_pos (pow_pos hp e) (pow_pos hp f),
      D', hD', hDD', g', hlocal, hart, hmap, hg',
      essentiallySmooth_of_smooth.{u, max v w} D', hflat', hcomp, ?_⟩
    refine ⟨d ^ p ^ f, ?_⟩
    simpa only [map_pow, ← pow_mul] using hf
  · obtain ⟨hlocal, hart, hmap, hsmooth', g', hg', hflat', hcomp, hx⟩ :=
      artinian_transcendental_polynomial_localization.{u, v, w} D S hgflat x ha
    refine ⟨1, Nat.zero_lt_one, _, inferInstance, inferInstance, g',
      hlocal, hart, hmap, hg', hsmooth', hflat', hcomp, ?_⟩
    simpa only [pow_one] using hx

end Algebra
