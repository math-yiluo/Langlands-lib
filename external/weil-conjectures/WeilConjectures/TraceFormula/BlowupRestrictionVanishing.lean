/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BlowupRestrictionChart
public import WeilConjectures.TraceFormula.BlowupChartLimit
public import WeilConjectures.RingTheory.TangentConeRegular

/-!
# Blowup restriction vanishing

Let `T` be the strict localization of a smooth surface over an algebraically closed field `k` at a
closed point `t`, `H` a regular curve through `t` and `D, B` curves through `t` whose tangent cones
satisfy `C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`. Let `i : T - (D ∪ H) ⟶ T - D` and let `E`
be a bounded complex on `T - (D ∪ H)` with finite locally constant cohomology and finite
`ℓ`-group monodromy. Then the restriction map
```
RΓ(T - D, i_! E) ⟶ RΓ(B - t, (i_! E)|_{B - t})
```
is zero (blueprint `lemma-vanishing-restrictions-after-blowing-up--1`).

The curves are given by equations `f, g, h ∈ R = 𝒪^{sh}_{S,t}` (`T = Spec R` is the spectrum of a
two-dimensional regular local ring, a factorial ring, so every curve through `t` is principal),
with `h ∈ 𝔪 ∖ 𝔪²`; `T - D` and `T - (D ∪ H)` are the basic opens of `f` and `fh`, and `B - t` is
the punctured spectrum of `R/(g)` (`AlgebraicGeometry.Scheme.puncturedCurveMap`).

Following the blueprint proof, `t` is blown up: in a chart of the blow-up containing all the
relevant points of the exceptional divisor (`AlgebraicGeometry.nonempty_blowupChartData`), the
complement `Z` of the strict transform of `D` is an étale limit of smooth surfaces
(`AlgebraicGeometry.Scheme.exists_isEtaleLimitOfSmoothSurfaces_blowupChart`), the exceptional
divisor `Y` and the strict transform `X` of `H` form a transverse boundary configuration, and the
strict transform of `B` is a finite disjoint union of strictly local curves centred on `Y`;
the restriction then vanishes by the punctured restriction lemma
(`AlgebraicGeometry.Etale.blowupRestriction_eq_zero_of_chartData`).

## Main results

- `AlgebraicGeometry.Etale.blowupRestriction_eq_zero`: the blowup restriction vanishing.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Etale

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 2 S.hom] (t : Spec (.of k) ⟶ S.left)

/-- On the strict localization of a smooth surface, if the tangent cones of `V(f)` and `V(g)` meet
only at the origin, then `V(f) ∩ V(g)` is the closed point. -/
lemma maximalIdeal_le_radical_of_smooth (ht : t ≫ S.hom = 𝟙 _)
    {f g : Scheme.strictHenselization t}
    (hfg : TangentConesMeetAtOrigin _ (Ideal.span {f}) (Ideal.span {g})) :
    maximalIdeal (Scheme.strictHenselization t) ≤ (Ideal.span {f, g}).radical := by
  have := Scheme.isRegularLocalRing_strictHenselization_of_smooth S t ht
  rw [Ideal.span_insert]
  exact hfg.maximalIdeal_le_radical

/-- **Blowup restriction vanishing** (blueprint `lemma-vanishing-restrictions-after-blowing-up--1`).
Let `T = Spec R` be the strict localization of a smooth surface `S` over the algebraically closed
field `k` at a `k`-point `t`, `ℓ` a prime invertible in `k` and `Λ` a finite `ℓ`-primary ring. Let
`D = V(f)`, `B = V(g)` be curves through `t` (`f, g ≠ 0`, `g ∈ 𝔪`) and `H = V(h)` a regular
curve through `t` (`h ∈ 𝔪 ∖ 𝔪²`) such that `C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`.
For every complex `E` on `T - (D ∪ H)` with finite `ℓ`-group monodromy, the restriction map
`RΓ(T - D, i_! E) ⟶ RΓ(B - t, (i_! E)|_{B - t})` is zero. -/
theorem blowupRestriction_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : IsNilpotent (ℓ : Λ))
    (ht : t ≫ S.hom = 𝟙 _) {f g h : Scheme.strictHenselization t}
    [Fact (g ∈ maximalIdeal (Scheme.strictHenselization t))]
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : HasOrder h 1)
    (hDB : TangentConesMeetAtOrigin _ (Ideal.span {f}) (Ideal.span {g}))
    (hDH : TangentConesMeetAtOrigin _ (Ideal.span {f}) (Ideal.span {h}))
    (E : DerivedCategory (Sheaf (Scheme.specBasicOpen (f * h)).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) :
    globalSectionsRestriction
      (Scheme.puncturedCurveMap (maximalIdeal_le_radical_of_smooth S t ht hDB))
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        ((Spec (.of (Scheme.strictHenselization t))).homOfLE
          (PrimeSpectrum.basicOpen_mul_le_left f h))).mapDerivedCategory.obj E) = 0 := by
  let := Scheme.strictHenselizationAlgebra S t
  have := Scheme.isRegularLocalRing_strictHenselization_of_smooth S t ht
  have hres := Scheme.bijective_residue_algebraMap_strictHenselization S t ht
  have : IsAlgClosed (ResidueField (Scheme.strictHenselization t)) :=
    IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective
      ((residue (Scheme.strictHenselization t)).comp
        (algebraMap k (Scheme.strictHenselization t))) hres)
  obtain ⟨x₀, y₀, hm, hlim⟩ := Scheme.exists_isEtaleLimitOfSmoothSurfaces_blowupChart S t ht
  obtain ⟨D⟩ := nonempty_blowupChartData
    (Scheme.ringKrullDim_strictHenselization_of_smooth S t ht) hm
    (algebraMap k (Scheme.strictHenselization t)) hres.1
    (.of_tangentConesMeetAtOrigin hf hg hDB)
    (.of_tangentConesMeetAtOrigin hf (fun h0 ↦ hh.2 (by simp [h0])) hDH) hh
  have hx : D.x ∈ maximalIdeal (Scheme.strictHenselization t) := by
    rw [hm]
    exact add_mem (Ideal.subset_span (Set.mem_insert _ _))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  have hm' : maximalIdeal (Scheme.strictHenselization t) = Ideal.span {D.x, y₀} := by
    rw [BlowupChart.span_pair_add_mul]
    exact hm
  exact blowupRestriction_eq_zero_of_chartData hℓ hΛ _ D hx hm' (hlim D.i D.f') E hE

end AlgebraicGeometry.Etale
