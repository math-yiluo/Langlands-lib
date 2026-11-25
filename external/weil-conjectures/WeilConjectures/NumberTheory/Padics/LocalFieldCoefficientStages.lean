/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Ramified finite coefficient stages of local fields

Source: Weil blueprint, main-20261015, smooth-purity,
`sk-lem-sp-field-extension-towers.proof.md`, Part (1)
(blueprint: lem-pur-local-field-coefficient-stages).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Padic

private theorem free_finite_of_integral_basis
    {R : Type*} {S : Type*} {E : Type*} {F : Type*}
    [CommRing R] [CommRing S] [Field E] [Field F]
    [Algebra R S] (r : R →+* E) (s : S →+* F) (i : E →+* F)
    (hs : Function.Injective s)
    (hcomm : ∀ a, s (algebraMap R S a) = i (r a))
    {d : ℕ} (b : Fin d → S)
    (hb : ∀ x : S, ∃! a : Fin d → R,
      s x = ∑ j, i (r (a j)) * s (b j)) :
    Module.Free R S ∧ Module.Finite R S := by
  classical
  let L : (Fin d → R) →ₗ[R] S := Fintype.linearCombination R b
  have hL (a : Fin d → R) :
      s (L a) = ∑ j, i (r (a j)) * s (b j) := by
    simp [L, Fintype.linearCombination_apply, Algebra.smul_def, hcomm]
  have hinj : Function.Injective L := by
    intro a c hac
    obtain ⟨z, hz, hu⟩ := hb (L a)
    exact (hu a (hL a)).trans (hu c (by rw [hac]; exact hL c)).symm
  have hsurj : Function.Surjective L := by
    intro x
    obtain ⟨a, ha, _⟩ := hb x
    exact ⟨a, hs ((hL a).trans ha.symm)⟩
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

private theorem quotient_free_finite
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (x : R) (y : S) (hxy : algebraMap R S x = y) :
    ∃ g : (R ⧸ Ideal.span {x}) →+* (S ⧸ Ideal.span {y}),
      (∀ a, g (Ideal.Quotient.mk (Ideal.span {x}) a) =
        Ideal.Quotient.mk (Ideal.span {y}) (algebraMap R S a)) ∧
      @Module.Free _ _ _ _ g.toAlgebra.toModule ∧
      @Module.Finite _ _ _ _ g.toAlgebra.toModule := by
  subst y
  let I := Ideal.span ({x} : Set R)
  have hI : I.map (algebraMap R S) = Ideal.span {algebraMap R S x} := by
    simp [I, Ideal.map_span]
  rw [← hI]
  let : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have hfree : Module.Free (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Free.of_equiv e.symm.toLinearEquiv
  have hfinite : Module.Finite (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  refine ⟨algebraMap _ _, fun _ ↦ rfl, ?_, ?_⟩
  · convert hfree using 1
    exact congrArg (fun a : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) ↦
        a.toModule) (toAlgebra_algebraMap (R := R ⧸ I)
          (S := S ⧸ I.map (algebraMap R S)))
  · convert hfinite using 1
    exact congrArg (fun a : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) ↦
        a.toModule) (toAlgebra_algebraMap (R := R ⧸ I)
          (S := S ⧸ I.map (algebraMap R S)))

private theorem power_transition
    {R : Type*} [CommRing R] (x : R) (m n : ℕ) (hmn : m ≤ n) :
    ∃ q : (R ⧸ Ideal.span {x ^ n}) →+* (R ⧸ Ideal.span {x ^ m}),
      ∀ a, q (Ideal.Quotient.mk (Ideal.span {x ^ n}) a) =
        Ideal.Quotient.mk (Ideal.span {x ^ m}) a := by
  have h : Ideal.span ({x ^ n} : Set R) ≤ Ideal.span {x ^ m} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right hmn
  exact ⟨Ideal.Quotient.factor h, fun _ ↦ rfl⟩

private theorem quotient_local
    {R : Type*} [CommRing R] [IsLocalRing R] (x : R) (hx : ¬ IsUnit x)
    (n : ℕ) (hn : 1 ≤ n) : IsLocalRing (R ⧸ Ideal.span {x ^ n}) := by
  have : Nontrivial (R ⧸ Ideal.span {x ^ n}) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top
      (fun h ↦ hx ((isUnit_pow_iff (by omega : n ≠ 0)).mp h)))
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

private theorem unit_power_span
    {R : Type*} [CommRing R] (a : Rˣ) (x : R) (n : ℕ) :
    Ideal.span ({((a : R) * x) ^ n} : Set R) = Ideal.span {x ^ n} := by
  rw [mul_pow]
  exact Ideal.span_singleton_mul_left_unit (a.isUnit.pow n) _

private theorem quotient_hom_heq
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    {I I' : Ideal R} {J J' : Ideal S} (hI : I' = I) (hJ : J' = J)
    (f : R →+* S) (g : (R ⧸ I) →+* (S ⧸ J)) (g' : (R ⧸ I') →+* (S ⧸ J'))
    (hg : ∀ x, g (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x))
    (hg' : ∀ x, g' (Ideal.Quotient.mk I' x) = Ideal.Quotient.mk J' (f x)) :
    HEq g g' := by
  subst I'
  subst J'
  apply heq_of_eq
  apply Ideal.Quotient.ringHom_ext
  ext x
  exact (hg x).trans (hg' x).symm

private theorem quotient_mk_heq
    {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    HEq (Ideal.Quotient.mk I) (Ideal.Quotient.mk J) := by
  subst J
  rfl

/-- Finite extensions of coefficient fields give finite free integer rings and
finite free ramified coefficient stages, independently of unit changes of uniformizers.

Source: Weil blueprint, main-20261015,
`sk-lem-sp-field-extension-towers.proof.md`, Part (1), and rational/qbar purity,
Steps 1–2 (blueprint: lem-pur-local-field-coefficient-stages).

Proof:
1. The coefficient-extension DVR theorem identifies both integer rings and their
   maximal ideals with the closed and open unit balls. Compatibility of absolute
   values therefore restricts the field inclusion to the ring homomorphism `f`.
2. Apply `lem-sfb-local-field-integral-basis` to obtain a finite integral basis;
   this proves `Module.Free` and `Module.Finite` for the scalar action given by `f`.
3. Apply `lem-weil-pbc-dvr-unit-times-uniformizer-power` in the upper DVR to `f t`.
   It is nonzero; its absolute value is less than one, so the exponent is positive.
   Raising `f t = u * v^e` to the nth power gives equality of the principal ideals.
4. Identify `S/t^n S` with `(R/t^n) ⊗[R] S` by the quotient tensor equivalence.
   Base change preserves finite freeness. The scalar map takes `[r]` to `[f r]`.
5. The finite residue fields and `Ideal.finite_quotient_pow` give finite quotients
   at exponents `n` and `e*n`. A quotient of a local ring by a proper ideal is local.
   The absolute value of `l` is less than one, so `l ∈ (t)` and `f l ∈ (f t)`.
   Taking nth powers shows that `l^n` vanishes in both level-n rings.
6. For a positive `k`, take `n = k` to see `k ≤ e*n`. Quotient transition maps
   for `m ≤ n` are induced by the identity on representatives.
7. Multiplication of either uniformizer by a unit leaves every principal-power
   ideal unchanged. Equal ideals give the canonical identity-on-representatives
   quotient equivalences. The quotient projections are heterogeneously equal,
   as are the scalar maps, which are specified on representatives. Transition
   maps are determined by their composites with these projections, so commute
   with the same identifications. This concerns the rings and maps,
   independently of any integral basis.
-/
theorem local_field_coefficient_stages
    (l : ℕ) [Fact l.Prime] (E : Type u) (F : Type v) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra E F]
    [IsScalarTower (Padic l) E F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (hcompat : ∀ x : E,
      coefficientExtensionAbsoluteValue l F (algebraMap E F x) =
        coefficientExtensionAbsoluteValue l E x)
    (t : coefficientExtensionIntegers l E) (v : coefficientExtensionIntegers l F)
    (ht : Ideal.span ({t} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (hv : Ideal.span ({v} : Set (coefficientExtensionIntegers l F)) =
      coefficientExtensionMaximalIdeal l F) :
    ∃ f : coefficientExtensionIntegers l E →+* coefficientExtensionIntegers l F,
      (∀ x, (f x : F) = algebraMap E F (x : E)) ∧
      @Module.Free _ _ _ _ f.toAlgebra.toModule ∧
      @Module.Finite _ _ _ _ f.toAlgebra.toModule ∧
      ∃ (e : ℕ) (w : (coefficientExtensionIntegers l F)ˣ),
        1 ≤ e ∧ f t = (w : coefficientExtensionIntegers l F) * v ^ e ∧
        (∀ n : ℕ, 1 ≤ n →
          Ideal.span ({f t ^ n} : Set (coefficientExtensionIntegers l F)) =
            Ideal.span ({v ^ (e * n)} : Set (coefficientExtensionIntegers l F)) ∧
          Finite (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) ∧
          IsLocalRing (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) ∧
          Finite (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) ∧
          IsLocalRing (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) ∧
          (∃ N : ℕ, 1 ≤ N ∧
            (l : coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) ^ N = 0 ∧
            (l : coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) ^ N = 0) ∧
          ∃ g : (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) →+*
              (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}),
            (∀ x, g (Ideal.Quotient.mk (Ideal.span {t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f t ^ n}) (f x)) ∧
            @Module.Free _ _ _ _ g.toAlgebra.toModule ∧
            @Module.Finite _ _ _ _ g.toAlgebra.toModule) ∧
        (∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 1 ≤ n ∧ k ≤ e * n) ∧
        (∀ m n : ℕ, 1 ≤ m → m ≤ n →
          ∃ (qR : (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) →+*
                (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ m}))
            (qS : (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ m}))
            (qV : (coefficientExtensionIntegers l F ⧸ Ideal.span {v ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {v ^ m})),
            (∀ x, qR (Ideal.Quotient.mk (Ideal.span {t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {t ^ m}) x) ∧
            (∀ x, qS (Ideal.Quotient.mk (Ideal.span {f t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f t ^ m}) x) ∧
            (∀ x, qV (Ideal.Quotient.mk (Ideal.span {v ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {v ^ m}) x)) ∧
        (∀ (a : (coefficientExtensionIntegers l E)ˣ)
            (b : (coefficientExtensionIntegers l F)ˣ),
          (∀ n : ℕ,
            Ideal.span ({(↑a * t) ^ n} :
                Set (coefficientExtensionIntegers l E)) = Ideal.span {t ^ n} ∧
            Ideal.span ({f (↑a * t) ^ n} :
                Set (coefficientExtensionIntegers l F)) = Ideal.span {f t ^ n} ∧
            Ideal.span ({(↑b * v) ^ n} :
                Set (coefficientExtensionIntegers l F)) = Ideal.span {v ^ n}) ∧
          (∀ (n : ℕ)
              (g : (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}))
              (g' : (coefficientExtensionIntegers l E ⧸ Ideal.span {(↑a * t) ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {f (↑a * t) ^ n})),
            (∀ x, g (Ideal.Quotient.mk (Ideal.span {t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f t ^ n}) (f x)) →
            (∀ x, g' (Ideal.Quotient.mk (Ideal.span {(↑a * t) ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f (↑a * t) ^ n}) (f x)) → HEq g g') ∧
          (∀ n : ℕ,
            HEq (Ideal.Quotient.mk (Ideal.span {(↑a * t) ^ n}))
              (Ideal.Quotient.mk (Ideal.span {t ^ n})) ∧
            HEq (Ideal.Quotient.mk (Ideal.span {f (↑a * t) ^ n}))
              (Ideal.Quotient.mk (Ideal.span {f t ^ n})) ∧
            HEq (Ideal.Quotient.mk (Ideal.span {(↑b * v) ^ n}))
              (Ideal.Quotient.mk (Ideal.span {v ^ n})))) := by
  classical
  let R := coefficientExtensionIntegers l E
  let S := coefficientExtensionIntegers l F
  have hE := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hF := (coefficientExtensionIntegers_dvr l F).choose_spec
  have hmemE : ∀ x : E, x ∈ R ↔ coefficientExtensionAbsoluteValue l E x ≤ 1 := hE.1
  have hmemF : ∀ x : F, x ∈ S ↔ coefficientExtensionAbsoluteValue l F x ≤ 1 := hF.1
  have hmE : ∀ x : R, x ∈ coefficientExtensionMaximalIdeal l E ↔
      coefficientExtensionAbsoluteValue l E (x : E) < 1 := hE.2.1
  have huF : ∀ x : S, IsUnit x ↔
      coefficientExtensionAbsoluteValue l F (x : F) = 1 := hF.2.2.1
  have : IsLocalRing R := hE.2.2.2.1
  have : IsLocalRing S := hF.2.2.2.1
  have : IsDiscreteValuationRing R := hE.2.2.2.2.2.2.2.1
  have : IsDiscreteValuationRing S := hF.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing R := hE.2.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing S := hF.2.2.2.2.2.2.2.2.1
  have hfiniteE : Finite (R ⧸ coefficientExtensionMaximalIdeal l E) :=
    hE.2.2.2.2.2.2.2.2.2.2.2.1
  have hfiniteF : Finite (S ⧸ coefficientExtensionMaximalIdeal l F) :=
    hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hmaxR : IsLocalRing.maximalIdeal R = coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal R)
  have hmaxS : IsLocalRing.maximalIdeal S = coefficientExtensionMaximalIdeal l F :=
    hF.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal S)
  let f : R →+* S := ((algebraMap E F).comp R.subtype).codRestrict S fun x ↦
    (hmemF _).mpr (by
      change coefficientExtensionAbsoluteValue l F (algebraMap E F (x : E)) ≤ 1
      rw [hcompat]
      exact (hmemE _).mp x.property)
  have hf (x : R) : (f x : F) = algebraMap E F (x : E) := rfl
  let : Algebra R S := f.toAlgebra
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite (Padic l) E F
  obtain ⟨b, hb, hex⟩ := exists_integral_basis l E F hcompat
  let bS : Fin (Module.finrank E F) → S := fun j ↦ ⟨b j, hb j⟩
  have hbS (x : S) : ∃! a : Fin (Module.finrank E F) → R,
      (x : F) = ∑ j, algebraMap E F (a j : E) * (bS j : F) := by
    obtain ⟨a, ⟨ha, hax⟩, huniq⟩ := hex x x.property
    refine ⟨fun j ↦ ⟨a j, ha j⟩, hax, ?_⟩
    intro c hc
    have heq := huniq (fun j ↦ (c j : E)) ⟨fun j ↦ (c j).property, hc⟩
    funext j
    exact Subtype.ext (congrFun heq j)
  obtain ⟨hfree, hfinite⟩ := free_finite_of_integral_basis R.subtype S.subtype
    (algebraMap E F) Subtype.val_injective hf bS hbS
  have : Module.Free R S := hfree
  have : Module.Finite R S := hfinite
  have htI : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr (hmaxR.trans ht.symm)
  have hvI : Irreducible v :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer v).mpr (hmaxS.trans hv.symm)
  have hft0 : f t ≠ 0 := by
    intro hz
    have hz' : algebraMap E F (t : E) = 0 := congrArg Subtype.val hz
    exact htI.ne_zero (Subtype.ext ((algebraMap E F).injective (by simpa using hz')))
  have htval : coefficientExtensionAbsoluteValue l E (t : E) < 1 :=
    (hmE t).mp (show t ∈ coefficientExtensionMaximalIdeal l E from
      ht ▸ Ideal.mem_span_singleton_self t)
  have hftunit : ¬ IsUnit (f t) := by
    intro h
    have hv := (huF (f t)).mp h
    rw [hf, hcompat] at hv
    exact (ne_of_lt htval) hv
  obtain ⟨e, w, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hft0 hvI
  have he : 1 ≤ e := by
    by_contra h
    have he0 : e = 0 := by omega
    apply hftunit
    simp only [he0, pow_zero, mul_one] at heq
    exact heq.symm ▸ w.isUnit
  have hpow (n : ℕ) :
      Ideal.span ({f t ^ n} : Set S) = Ideal.span {v ^ (e * n)} := by
    rw [heq, mul_pow, ← pow_mul]
    exact Ideal.span_singleton_mul_left_unit (w.isUnit.pow n) _
  refine ⟨f, hf, hfree, hfinite, e, w, he, heq, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have : Finite (R ⧸ coefficientExtensionMaximalIdeal l E) := hfiniteE
    have : Finite (S ⧸ coefficientExtensionMaximalIdeal l F) := hfiniteF
    have hfinR : Finite (R ⧸ Ideal.span {t ^ n}) := by
      rw [← Ideal.span_singleton_pow, ht]
      exact Ideal.finite_quotient_pow (ht ▸ Submodule.fg_span_singleton t) n
    have hfinS : Finite (S ⧸ Ideal.span {f t ^ n}) := by
      rw [hpow, ← Ideal.span_singleton_pow, hv]
      exact Ideal.finite_quotient_pow (hv ▸ Submodule.fg_span_singleton v) (e * n)
    have hlval : coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      change spectralNorm ℚ_[l] E (l : E) < 1
      rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
      exact Padic.norm_p_lt_one
    have hlR : (l : R) ∈ Ideal.span {t} := by
      rw [ht]
      exact (hmE _).mpr hlval
    have hlS : (l : S) ∈ Ideal.span {f t} := by
      rw [Ideal.mem_span_singleton] at hlR ⊢
      simpa only [map_natCast] using map_dvd f hlR
    obtain ⟨g, hg, hgfree, hgfinite⟩ :=
      quotient_free_finite (R := R) (S := S) (t ^ n) (f t ^ n) (map_pow f t n)
    refine ⟨hpow n, hfinR, quotient_local t htI.not_isUnit n hn,
      hfinS, quotient_local (f t) hftunit n hn, ⟨n, hn, ?_, ?_⟩,
      g, hg, hgfree, hgfinite⟩
    · have hmem : (l : R) ^ n ∈ Ideal.span ({t ^ n} : Set R) := by
        rw [← Ideal.span_singleton_pow]
        exact Ideal.pow_mem_pow hlR n
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simpa only [map_pow, map_natCast] using hz
    · have hmem : (l : S) ^ n ∈ Ideal.span ({f t ^ n} : Set S) := by
        rw [← Ideal.span_singleton_pow]
        exact Ideal.pow_mem_pow hlS n
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simpa only [map_pow, map_natCast] using hz
  · intro k hk
    exact ⟨k, hk, by simpa using Nat.mul_le_mul_right k he⟩
  · intro m n _ hmn
    obtain ⟨qR, hqR⟩ := power_transition t m n hmn
    obtain ⟨qS, hqS⟩ := power_transition (f t) m n hmn
    obtain ⟨qV, hqV⟩ := power_transition v m n hmn
    exact ⟨qR, qS, qV, hqR, hqS, hqV⟩
  · intro a b
    have ha (n : ℕ) := unit_power_span a t n
    have hb (n : ℕ) := unit_power_span b v n
    have haf (n : ℕ) :
        Ideal.span ({f (↑a * t) ^ n} : Set S) = Ideal.span {f t ^ n} := by
      rw [map_mul]
      exact unit_power_span (Units.map f.toMonoidHom a) (f t) n
    refine ⟨fun n ↦ ⟨ha n, haf n, hb n⟩, ?_, ?_⟩
    · intro n g g' hg hg'
      exact quotient_hom_heq (ha n) (haf n) f g g' hg hg'
    · intro n
      exact ⟨quotient_mk_heq (ha n), quotient_mk_heq (haf n), quotient_mk_heq (hb n)⟩

end Padic
