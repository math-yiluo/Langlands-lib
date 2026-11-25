/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingH0
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FormalGlueingLocalizedChartTuple
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import WeilConjectures.RingTheory.FormalGlueingData

/-!
# Clearing denominators of a formal glueing chart section

Source: Stacks Project, More on Algebra, Lemmas 05EQ and 05EP in the proof of
Proposition 05ER (blueprint: lem-weil-pbc-formal-glueing-H0-chart-power-lift).
-/

@[expose] public section

universe u v w

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private theorem clear_family {ι : Type*} [Finite ι]
    (T : Submonoid R) (A : ModuleCat.{_} R) (B : ι → ModuleCat.{_} R)
    (d : ∀ j, A →ₗ[R] B j) (m : A)
    (hm : ∀ j, LocalizedModule.mk (S := T) (d j m) 1 = 0) :
    ∃ s : T, ∀ j, d j ((s : R) • m) = 0 := by
  let ell : (∀ j, B j) →ₗ[R] (∀ j, LocalizedModule T (B j)) :=
    LinearMap.pi fun j ↦ (LocalizedModule.mkLinearMap T (B j)).comp (LinearMap.proj j)
  have he : ell (fun j ↦ d j m) = ell 0 := by
    ext j
    exact (hm j).trans (by simp [ell])
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := ell) he
  refine ⟨s, fun j ↦ ?_⟩
  have hj := congrFun hs j
  simpa only [Pi.smul_apply, Pi.zero_apply, Submonoid.smul_def, smul_zero,
    map_smul] using hj

private theorem numerator_vanish (u : R) (A : ModuleCat.{_} R)
    (N : ModuleCat.{_} R) (d : A →ₗ[R] N) (z : localize u A)
    (m : A) (s : Submonoid.powers u)
    (hs : (s : R) • z = LocalizedModule.mk m 1)
    (hd : localMap u d z = 0) :
    LocalizedModule.mk (S := Submonoid.powers u) (d m) 1 = 0 := by
  have he := congrArg (localMap u d) hs
  rw [map_smul, hd, smul_zero] at he
  simpa only [localMap, IsLocalizedModule.map_LocalizedModules] using he.symm

private theorem swap_self (u : R) (P : ModuleCat.{w} R) :
    swap u u P = LinearMap.id := by
  exact ((exists_swap u u P).unique (fun _ ↦ rfl)
    (exists_swap u u P).exists.choose_spec).symm

set_option backward.isDefEq.respectTransparency false in
private theorem self_overlap {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (X : Data.{u, v, w} φ f) (i : Fin t)
    (y : localize (f i) (piece (f i) (X.M i))) : X.alpha_overlap i i y = y := by
  let T := Submonoid.powers (f i)
  let P := piece (f i) (X.M i)
  let d := (X.alpha_overlap i i).toLinearMap
  have hc := X.cocycle i i i
  simp only [swap_self, LinearMap.id_comp, LinearMap.comp_id] at hc
  have hi : Function.Injective (localMap (f i) d) :=
    IsLocalizedModule.map_injective T (LocalizedModule.mkLinearMap T _)
      (LocalizedModule.mkLinearMap T _) d (X.alpha_overlap i i).injective
  have he := hi (LinearMap.congr_fun hc (LocalizedModule.mk y 1))
  have hm : Function.Injective (LocalizedModule.mkLinearMap T (localize (f i) P)) :=
    (IsLocalizedModule.injective_iff_isRegular T
      (LocalizedModule.mkLinearMap T (localize (f i) P))).mpr
      (fun c ↦ IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap T P) c)
  apply hm
  simpa only [localMap, T, P, d, LinearEquiv.coe_coe, IsLocalizedModule.map_LocalizedModules,
    LocalizedModule.mkLinearMap_apply] using he

set_option backward.isDefEq.respectTransparency false in
/-- A chart section becomes the projection of a global compatible section after
multiplication by a power of the chart parameter.
Source: Stacks Project, More on Algebra, Remark 05EL, Lemmas 05EQ and 05EP,
and Proposition 05ER, second paragraph
(blueprint: lem-weil-pbc-formal-glueing-H0-chart-power-lift).

Proof:
Put `u = f i`. In the localization of the ambient product of the prime module and
all chart modules at `u`, form a tuple with prime coordinate
`(X.alpha i).symm (1 ⊗ x)` and chart coordinate `j` equal to
`X.alpha_overlap i j (x/1)`. The `i` chart coordinate is `x/1`: the cocycle with
all indices `i` implies that the invertible self-overlap is idempotent, hence the
identity, under the canonical identifications of repeated localization. The square
condition, evaluated on the prime coordinate, proves each localized prime/chart
compatibility equation. The cocycle, evaluated on `(x/1)/1`, proves each localized
chart/chart equation. Use the canonical swap and tensor comparison fraction
formulas of the canonical-maps lemma for these identifications.
There are only finitely many coordinates, so write the tuple with one common
power `u^a` as denominator, taking the maximum of the individual exponents. Its
numerator is a tuple in the original ambient product. Each of the finitely many
compatibility differences is zero after localization at `u`, so some power of `u`
kills it. Take one exponent `b` at least as large as all these exponents and multiply
the numerator by `u^b`. All the original compatibility equations now hold, so this
numerator defines an element `h` of `h0`. Its localized `i` coordinate is
`u^(a+b) • (x/1)`. The map from the `i` chart to its own localization is injective,
because `u` is already a unit on that chart. Consequently the original coordinate
of `h` is `u^(a+b) • x`; choose `n = a+b`.
This works also when `u = 0`: its chart is the zero module. The presence of `i`
excludes the empty index set; zero modules and zero rings cause no exception. -/
theorem h0_chart_power_lift {t : ℕ} (φ : R →+* S) (hflat : φ.Flat)
    (f : Fin t → R) (X : Data.{u, v, w} φ f) (i : Fin t)
    (x : piece (f i) (X.M i)) :
    ∃ (n : ℕ) (h : h0 φ f X), h.val.2 i = (f i) ^ n • x := by
  have _hflat := hflat
  let : Algebra R S := φ.toAlgebra
  let A := ModuleCat.of R (restrict φ X.M' × ∀ j : Fin t, piece (f j) (X.M j))
  let p : ∀ j : Fin t, A →ₗ[R] piece (f j) (X.M j) :=
    fun j ↦ (LinearMap.proj j).comp (LinearMap.snd R _ _)
  let a := fun j : Fin t ↦
    (((X.alpha j).toLinearMap.comp
      (LocalizedModule.mkLinearMap _ (restrict φ X.M'))).comp
        (LinearMap.fst R _ _) -
      (TensorProduct.mk R S (piece (f j) (X.M j)) 1).comp (p j))
  let b := fun j k : Fin t ↦
    (((X.alpha_overlap j k).toLinearMap.comp
      (LocalizedModule.mkLinearMap _ (piece (f j) (X.M j)))).comp (p j) -
      (LocalizedModule.mkLinearMap _ (piece (f k) (X.M k))).comp (p k))
  let T := Submonoid.powers (f i)
  let ell₀ := LocalizedModule.mkLinearMap T (restrict φ X.M')
  let ell₁ : (∀ j, piece (f j) (X.M j)) →ₗ[R]
      (∀ j, LocalizedModule T (piece (f j) (X.M j))) :=
    LinearMap.pi fun j ↦ (LocalizedModule.mkLinearMap T _).comp (LinearMap.proj j)
  let e₀ := IsLocalizedModule.linearEquiv T (ell₀.prodMap ell₁)
    (LocalizedModule.mkLinearMap T A)
  let z := e₀ ((X.alpha i).symm (TensorProduct.tmul R (1 : S) x),
    fun j ↦ X.alpha_overlap i j (LocalizedModule.mk x 1))
  obtain ⟨ha, hb⟩ := localized_chart_tuple_compatible φ f X i x
  have hz : localMap (f i) (p i) z = LocalizedModule.mk x 1 := by
    let proj : (localize (f i) (restrict φ X.M') ×
        ∀ j, localize (f i) (piece (f j) (X.M j))) →ₗ[R]
        localize (f i) (piece (f i) (X.M i)) :=
      (LinearMap.proj i).comp (LinearMap.snd R _ _)
    have hp : localMap (f i) (p i) = proj.comp e₀.symm.toLinearMap := by
      apply IsLocalizedModule.ext T (LocalizedModule.mkLinearMap T A)
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T (piece (f i) (X.M i))))
      apply LinearMap.ext
      intro m
      change localMap (f i) (p i) (LocalizedModule.mk m 1) =
        proj (e₀.symm (LocalizedModule.mk m 1))
      have he : e₀.symm (LocalizedModule.mk m 1) = (ell₀.prodMap ell₁) m :=
        IsLocalizedModule.linearEquiv_symm_apply T _ _ m
      rw [he]
      simp only [localMap, IsLocalizedModule.map_LocalizedModules]
      rfl
    rw [hp]
    change proj (e₀.symm (e₀ _)) = _
    rw [LinearEquiv.symm_apply_apply]
    exact self_overlap φ f X i _
  change ∀ j, localMap (f i) (a j) z = 0 at ha
  change ∀ j k, localMap (f i) (b j k) z = 0 at hb
  obtain ⟨⟨m, s⟩, hs⟩ :=
    IsLocalizedModule.surj T (LocalizedModule.mkLinearMap T A) z
  change (s : R) • z = LocalizedModule.mk m 1 at hs
  obtain ⟨r, hr⟩ := clear_family T A
    (fun j ↦ restrict φ (extend φ (piece (f j) (X.M j)))) a m
    (fun j ↦ numerator_vanish (f i) A _ _ z m s hs (ha j))
  obtain ⟨q, hq⟩ := clear_family T A
    (fun jk : Fin t × Fin t ↦ localize (f jk.1) (piece (f jk.2) (X.M jk.2)))
    (fun jk ↦ b jk.1 jk.2) m
    (fun jk ↦ numerator_vanish (f i) A _ _ z m s hs (hb jk.1 jk.2))
  let y : A := (q : R) • (r : R) • m
  have hy : y ∈ h0 φ f X := by
    change y ∈ _ ⊓ _
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro j
      change a j y = 0
      rw [show y = (q : R) • ((r : R) • m) from rfl, map_smul, hr j, smul_zero]
    · intro j k
      change b j k y = 0
      rw [show y = (r : R) • (q : R) • m from smul_comm _ _ _]
      rw [map_smul, hq (j, k), smul_zero]
  have hp : LocalizedModule.mk (S := T) (p i m) 1 = (s : R) •
      LocalizedModule.mk (S := T) x 1 := by
    have he := congrArg (localMap (f i) (p i)) hs
    rw [map_smul, hz] at he
    simpa only [localMap, IsLocalizedModule.map_LocalizedModules] using he.symm
  let : IsScalarTower R (Localization.Away (f i)) (piece (f i) (X.M i)) :=
    ⟨fun r a x ↦ by
      simpa only [Algebra.smul_def, ModuleCat.restrictScalars.smul_def] using
        mul_smul (algebraMap R (Localization.Away (f i)) r) a (show X.M i from x)⟩
  let : IsLocalizedModule T (LinearMap.id : piece (f i) (X.M i) →ₗ[R] _) :=
    isLocalizedModule_id T (piece (f i) (X.M i)) (Localization.Away (f i))
  let e := IsLocalizedModule.linearEquiv T
    (LocalizedModule.mkLinearMap T (piece (f i) (X.M i)))
    (LinearMap.id : piece (f i) (X.M i) →ₗ[R] _)
  have pe : p i m = (s : R) • x := by
    have he := congrArg e hp
    have base (a : piece (f i) (X.M i)) : e (LocalizedModule.mk a 1) = a :=
      IsLocalizedModule.linearEquiv_apply T _ _ a
    rw [map_smul, base, base] at he
    exact he
  obtain ⟨n, hn⟩ := (q * r * s).property
  refine ⟨n, ⟨y, hy⟩, ?_⟩
  change p i y = (f i) ^ n • x
  dsimp only [y]
  rw [map_smul, map_smul, pe, ← mul_smul, ← mul_smul]
  exact congrArg (fun c : R ↦ c • x) hn.symm


end FormalGlueing
