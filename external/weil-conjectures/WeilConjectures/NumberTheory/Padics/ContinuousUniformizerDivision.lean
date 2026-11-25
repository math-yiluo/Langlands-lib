/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Continuous division by a uniformizer power

Source: Hemo–Richarz–Scholbach, proof of Theorem 6.12(2), finite `E` case,
pp. 18–19 (auxiliary; not a blueprint node).

The statement records the continuous integral division and the local unit
inversion used in the continuous Smith elimination argument. The valuation topology
of `E` is the metric topology of the recorded absolute value
`Padic.coefficientExtensionAbsoluteValue` (through `AbsoluteValue.toNormedField`,
as in the project's `coefficientExtensionNormedField`); the integer ring and the
range `π^e A` carry the subspace topologies.
-/

@[expose] public section

universe u v

namespace Padic

/-- Multiplication by a power of the chosen uniformizer is a homeomorphism onto
its image, and divisible continuous functions admit a unique continuous quotient.
If the value at a point is a unit multiple of that power, the quotient is locally
unit-valued and its inverse is continuous there.

Source: Hemo–Richarz–Scholbach, proof of Theorem 6.12(2), finite `E` case,
pp. 18–19 (auxiliary; not a blueprint node).

The quotient is unique among all continuous `q'` with `π^e q' = f`, independently
of the local unit clause.

Proof: multiplication by a nonzero uniformizer power is a homeomorphism of the
ambient valued field, and restriction to the valuation ring gives the first
clause. Compose a continuous divisible function with the inverse restriction to
obtain the unique quotient. Cancellation proves the value at the chosen point.
The unit locus is open in the valuation topology, and inversion is continuous on
the ambient field's nonzero locus, giving the final local assertion.
-/
theorem continuous_uniformizer_division
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (e : ℕ) :
    (∃ h : @Homeomorph (Padic.coefficientExtensionIntegers l E)
        {x : E // x ∈ Set.range
          (fun a : Padic.coefficientExtensionIntegers l E =>
            (Padic.coefficientExtensionUniformizer l E : E) ^ e * (a : E))}
        (TopologicalSpace.induced
          (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
          (@UniformSpace.toTopologicalSpace E
            (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
        (TopologicalSpace.induced Subtype.val
          (@UniformSpace.toTopologicalSpace E
            (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)),
      ∀ a : Padic.coefficientExtensionIntegers l E,
        h a = ⟨(Padic.coefficientExtensionUniformizer l E : E) ^ e * (a : E),
          ⟨a, rfl⟩⟩) ∧
    ∀ {T : Type v} [TopologicalSpace T]
      (f : T → Padic.coefficientExtensionIntegers l E),
      @Continuous T (Padic.coefficientExtensionIntegers l E) _
        (TopologicalSpace.induced
          (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
          (@UniformSpace.toTopologicalSpace E
            (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
        f →
        (∀ t : T, (f t : E) ∈ Set.range
          (fun a : Padic.coefficientExtensionIntegers l E =>
            (Padic.coefficientExtensionUniformizer l E : E) ^ e * (a : E))) →
        ∃ q : T → Padic.coefficientExtensionIntegers l E,
          @Continuous T (Padic.coefficientExtensionIntegers l E) _
            (TopologicalSpace.induced
              (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
              (@UniformSpace.toTopologicalSpace E
                (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
            q ∧
            (∀ t : T,
              (Padic.coefficientExtensionUniformizer l E : E) ^ e * (q t : E) =
                (f t : E)) ∧
            (∀ (t₀ : T),
              (f t₀ : E) ∈ Set.range
                (fun z : (Padic.coefficientExtensionIntegers l E)ˣ =>
                  (Padic.coefficientExtensionUniformizer l E : E) ^ e *
                    ((z : Padic.coefficientExtensionIntegers l E) : E)) →
              ∃ U : Set T, IsOpen U ∧ t₀ ∈ U ∧
                (∀ t : T, t ∈ U → IsUnit (q t)) ∧
                @ContinuousOn T E _
                  (@UniformSpace.toTopologicalSpace E
                    (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)
                  (fun t : T => ((q t : E)⁻¹)) U) ∧
            ∀ q' : T → Padic.coefficientExtensionIntegers l E,
              @Continuous T (Padic.coefficientExtensionIntegers l E) _
                (TopologicalSpace.induced
                  (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
                  (@UniformSpace.toTopologicalSpace E
                    (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
                q' →
              (∀ t : T,
                (Padic.coefficientExtensionUniformizer l E : E) ^ e * (q' t : E) =
                  (f t : E)) →
              q' = q
 := by
  classical
  let A := coefficientExtensionIntegers l E
  let c : E := (coefficientExtensionUniformizer l E : E) ^ e
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  rcases h with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr, hpid, hm0,
    hprime, hfinite, hr, hgen_exists, hassoc, hfactor⟩
  have hO : ∀ x : E, x ∈ A ↔ coefficientExtensionAbsoluteValue l E x ≤ 1 := hO
  have hm : ∀ x : A, x ∈ coefficientExtensionMaximalIdeal l E ↔
      coefficientExtensionAbsoluteValue l E (x : E) < 1 := hm
  have hu : ∀ x : A, IsUnit x ↔ coefficientExtensionAbsoluteValue l E (x : E) = 1 := hu
  have hm0 : coefficientExtensionMaximalIdeal l E ≠ ⊥ := hm0
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} : Set A) =
      coefficientExtensionMaximalIdeal l E := hgen_exists.choose_spec
  have hpi : (coefficientExtensionUniformizer l E : E) ≠ 0 := by
    intro hz
    apply hm0
    rw [← hgen]
    rw [show coefficientExtensionUniformizer l E = 0 from Subtype.ext hz]
    exact Ideal.span_singleton_zero
  have hc : c ≠ 0 := pow_ne_zero _ hpi
  obtain ⟨r, ⟨y, hym, hy0, hyr⟩, hrmax, hrgen⟩ := hr
  have hyr : coefficientExtensionAbsoluteValue l E (y : E) = r := hyr
  have hrlt : r < 1 := by
    rw [← hyr]
    exact (hm y).1 hym
  have hrnonneg : 0 ≤ r := by
    rw [← hyr]
    exact AbsoluteValue.nonneg _ _
  have hrmax : ∀ a : A, a ∈ coefficientExtensionMaximalIdeal l E → a ≠ 0 →
      coefficientExtensionAbsoluteValue l E (a : E) ≤ r := hrmax
  have hunit (a : A) (ha : r < coefficientExtensionAbsoluteValue l E (a : E)) :
      IsUnit a := by
    apply (hu a).2
    apply le_antisymm ((hO _).1 a.property)
    by_contra hn
    have halt : coefficientExtensionAbsoluteValue l E (a : E) < 1 :=
      lt_of_not_ge hn
    have ha0 : a ≠ 0 := by
      intro hz
      have hz' : (a : E) = 0 := congrArg Subtype.val hz
      rw [hz', map_zero] at ha
      exact (not_lt_of_ge hrnonneg) ha
    exact (not_lt_of_ge (hrmax a ((hm a).2 halt) ha0)) ha
  let : NormedField E := (coefficientExtensionAbsoluteValue l E).toNormedField
  let g : A → E := fun a ↦ c * (a : E)
  have hg : Topology.IsEmbedding g := by
    have hmul : Topology.IsEmbedding (fun x : E ↦ c * x) :=
      (Homeomorph.smulOfNeZero c hc).isEmbedding
    have hs : Topology.IsEmbedding ((↑) : A → E) := Topology.IsEmbedding.subtypeVal
    simpa [g, Function.comp_def] using hmul.comp hs
  let H := hg.toHomeomorph
  refine ⟨⟨H, fun _ ↦ rfl⟩, ?_⟩
  intro T _ f hf hdiv
  let k : T → Set.range g := fun t ↦ ⟨(f t : E), hdiv t⟩
  have hk : Continuous k := by
    apply continuous_induced_rng.2
    change Continuous (fun t : T ↦ (f t : E))
    exact continuous_subtype_val.comp hf
  let q : T → A := fun t ↦ H.symm (k t)
  have hqcont : Continuous q := H.symm.continuous.comp hk
  have hq (t : T) : c * (q t : E) = (f t : E) := by
    exact congrArg Subtype.val (H.apply_symm_apply (k t))
  have hqval : Continuous (fun t ↦ (q t : E)) := continuous_subtype_val.comp hqcont
  refine ⟨q, hqcont, hq, ?_, ?_⟩
  · intro t₀ ht₀
    obtain ⟨z, hz⟩ := ht₀
    have hqz : q t₀ = (z : A) := by
      apply Subtype.ext
      exact mul_left_cancel₀ hc ((hq t₀).trans hz.symm)
    have hqt₀ : IsUnit (q t₀) := hqz ▸ z.isUnit
    let U : Set T := {t | r < coefficientExtensionAbsoluteValue l E (q t : E)}
    have hUopen : IsOpen U := by
      change IsOpen {t | r < ‖(q t : E)‖}
      exact isOpen_lt continuous_const hqval.norm
    have hUunit : ∀ t : T, t ∈ U → IsUnit (q t) := fun t ht ↦ hunit (q t) ht
    refine ⟨U, hUopen, ?_, hUunit, ?_⟩
    · change r < coefficientExtensionAbsoluteValue l E (q t₀ : E)
      rw [(hu _).1 hqt₀]
      exact hrlt
    · apply hqval.continuousOn.inv₀
      intro t ht
      exact isUnit_iff_ne_zero.1 ((hUunit t ht).map A.subtype)
  · intro q' _ hq'
    funext t
    apply Subtype.ext
    exact mul_left_cancel₀ hc ((hq' t).trans (hq t).symm)

end Padic
