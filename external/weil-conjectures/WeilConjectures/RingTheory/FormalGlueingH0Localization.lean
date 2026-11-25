/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingH0
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import WeilConjectures.RingTheory.FormalGlueingH0ChartPowerLift

/-!
# Localization of compatible sections of formal glueing data

Source: Stacks Project, More on Algebra, proof of Proposition 05ER, second paragraph,
using Lemmas 05EQ and 05EP (blueprint: lem-weil-pbc-formal-glueing-H0-localization).
-/

@[expose] public section

universe uL vL wL

namespace FormalGlueing

variable {R : Type uL} {S : Type vL} [CommRing R] [CommRing S]

/-- Membership in `h0` gives the two families of compatibility equations.
Source: Stacks Project, Remark 05EL
(blueprint: lem-weil-pbc-formal-glueing-H0-localization). -/
private theorem h0_equations {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (X : Data.{uL, vL, wL} φ f) (h : h0 φ f X) :
    let : Algebra R S := φ.toAlgebra
    (∀ j, X.alpha j (LocalizedModule.mk h.val.1 1) = TensorProduct.tmul R (1 : S) (h.val.2 j)) ∧
    (∀ j k, X.alpha_overlap j k (LocalizedModule.mk (h.val.2 j) 1) =
      LocalizedModule.mk (h.val.2 k) 1) := by
  let : Algebra R S := φ.toAlgebra
  have hh := h.property
  change h.val ∈ _ ⊓ _ at hh
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
    LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe] at hh
  exact hh

/-- A compatible section with zero `i` coordinate is killed by a power of `f i`.
Source: Stacks Project, Proposition 05ER, second paragraph
(blueprint: lem-weil-pbc-formal-glueing-H0-localization). -/
private theorem h0_projection_kernel {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (X : Data.{uL, vL, wL} φ f) (i : Fin t) (h : h0 φ f X)
    (hz : h.val.2 i = 0) : ∃ s : Submonoid.powers (f i), s • h = 0 := by
  let T := Submonoid.powers (f i)
  let a := LocalizedModule.mkLinearMap T (restrict φ X.M')
  let b : (∀ j, piece (f j) (X.M j)) →ₗ[R]
      (∀ j, LocalizedModule.Away (f i) (piece (f j) (X.M j))) :=
    LinearMap.pi fun j ↦ (LocalizedModule.mkLinearMap T _).comp (LinearMap.proj j)
  let d := a.prodMap b
  have hp : a h.val.1 = 0 := by
    apply (X.alpha i).injective
    have he := (h0_equations φ f X h).1 i
    simpa [a, hz] using he
  have hc : b h.val.2 = 0 := by
    funext j
    change LocalizedModule.mk (h.val.2 j) 1 = 0
    have he := (h0_equations φ f X h).2 i j
    simpa [hz, LocalizedModule.zero_mk] using he.symm
  have hd : d h.val = d 0 := by
    change (a h.val.1, b h.val.2) = _
    simp [hp, hc]
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := d) hd
  refine ⟨s, Subtype.ext ?_⟩
  simpa using hs

/-- The projection to a chart extends uniquely across localization and is bijective.
Source: Stacks Project, More on Algebra, proof of Proposition 05ER, second paragraph,
using Lemmas 05EQ and 05EP (blueprint: lem-weil-pbc-formal-glueing-H0-localization).

Proof:
1. Extract the prime/chart and overlap equations from membership in the
   intersection of kernels defining `h0`.
2. If a compatible section has zero `i` coordinate, its prime coordinate vanishes
   after localization at `f i`, by injectivity of `alpha i`. All its chart
   coordinates vanish there by the `(i,j)` overlap equations. Mathlib's finite
   product localization instances give one power killing the entire section.
3. The power-lifting lemma constructs, for every chart element `x`, a compatible
   section whose `i` coordinate is `(f i)^n • x`
   [lem-weil-pbc-formal-glueing-H0-chart-power-lift].
4. Multiplication by powers of `f i` is invertible on the chart. Step 3 gives the
   denominator-surjectivity axiom for the chart projection. Step 2, applied to
   a difference of sections, gives the equality-clearing axiom. Thus the chart
   projection is an `IsLocalizedModule` map.
5. Mathlib's canonical linear equivalence between two localizations gives the
   desired bijective map. Its formula on sections and uniqueness are precisely
   the localization universal property. -/
theorem exists_unique_bijective_h0_localization {t : ℕ} (φ : R →+* S)
    (hflat : φ.Flat) (f : Fin t → R) (X : Data.{uL, vL, wL} φ f) (i : Fin t) :
    ∃ π : LocalizedModule.Away (f i) (h0 φ f X) →ₗ[R] piece (f i) (X.M i),
      (∀ h : h0 φ f X, π (LocalizedModule.mk h 1) = h.val.2 i) ∧
      (∀ π' : LocalizedModule.Away (f i) (h0 φ f X) →ₗ[R] piece (f i) (X.M i),
        (∀ h : h0 φ f X, π' (LocalizedModule.mk h 1) = h.val.2 i) → π' = π) ∧
      Function.Bijective π := by
  let T := Submonoid.powers (f i)
  let p : h0 φ f X →ₗ[R] piece (f i) (X.M i) :=
    ((LinearMap.proj i).comp (LinearMap.snd R _ _)).comp (h0 φ f X).subtype
  let : IsScalarTower R (Localization.Away (f i)) (piece (f i) (X.M i)) :=
    ⟨fun r a x ↦ by
      simpa only [Algebra.smul_def, ModuleCat.restrictScalars.smul_def] using
        mul_smul (algebraMap R (Localization.Away (f i)) r) a (show X.M i from x)⟩
  let : IsLocalizedModule T (LinearMap.id : piece (f i) (X.M i) →ₗ[R] _) :=
    isLocalizedModule_id T (piece (f i) (X.M i)) (Localization.Away (f i))
  let : IsLocalizedModule T p :=
    { map_units := IsLocalizedModule.map_units
        (LinearMap.id : piece (f i) (X.M i) →ₗ[R] _)
      surj := fun x ↦ by
        obtain ⟨n, h, hh⟩ := h0_chart_power_lift φ hflat f X i x
        exact ⟨(h, ⟨(f i) ^ n, ⟨n, rfl⟩⟩), hh.symm⟩
      exists_of_eq := fun {h k} hh ↦ by
        have hz : (h - k).val.2 i = 0 := by
          change p h - p k = 0
          exact sub_eq_zero.mpr hh
        obtain ⟨s, hs⟩ := h0_projection_kernel φ f X i (h - k) hz
        exact ⟨s, sub_eq_zero.mp (by simpa only [smul_sub] using hs)⟩ }
  let e := IsLocalizedModule.linearEquiv T
    (LocalizedModule.mkLinearMap T (h0 φ f X)) p
  have he (h : h0 φ f X) : e (LocalizedModule.mk h 1) = p h :=
    IsLocalizedModule.linearEquiv_apply T (LocalizedModule.mkLinearMap T (h0 φ f X)) p h
  refine ⟨e.toLinearMap, ?_, ?_, e.bijective⟩
  · intro h
    exact he h
  · intro π' hπ'
    apply IsLocalizedModule.ext T (LocalizedModule.mkLinearMap T (h0 φ f X))
      (IsLocalizedModule.map_units p)
    ext h
    exact (hπ' h).trans (he h).symm

end FormalGlueing
