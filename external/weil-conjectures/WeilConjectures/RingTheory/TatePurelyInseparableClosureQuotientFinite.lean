/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.RingTheory.TateRootClosureQuotientFinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# The closed fibre of a purely inseparable integral closure

Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese).
(blueprint: lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite).
-/

@[expose] public section

universe u v

set_option autoImplicit false

private theorem finite_quotient_powers
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (y : A) (n : ℕ) [Module.Finite R (A ⧸ Ideal.span ({y} : Set A))] :
    Module.Finite R (A ⧸ Ideal.span ({y ^ n} : Set A)) := by
  induction n with
  | zero =>
    have h : Ideal.span ({y ^ 0} : Set A) = ⊤ := by simp
    let e := Ideal.quotientEquivAlgOfEq R h
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  | succ n ih =>
    let I : Ideal A := Ideal.span {y ^ n}
    let J : Ideal A := Ideal.span {y ^ (n + 1)}
    let P : Ideal A := Ideal.span {y}
    have hJP : J ≤ P := by
      apply Ideal.span_le.mpr
      rintro a (rfl : a = y ^ (n + 1))
      exact Ideal.mem_span_singleton.mpr (dvd_pow_self y (Nat.succ_ne_zero n))
    let f : (A ⧸ I) →ₗ[A] A ⧸ J :=
      I.liftQ (J.mkQ.comp (LinearMap.mulLeft A y)) (by
        intro a ha
        change Ideal.Quotient.mk J (y * a) = 0
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
        apply Ideal.mem_span_singleton.mpr
        exact ⟨b, by rw [pow_succ']; ring⟩)
    let g : (A ⧸ J) →ₐ[R] A ⧸ P := Ideal.Quotient.factorₐ R hJP
    have hexact : Function.Exact (f.restrictScalars R) g.toLinearMap := by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      constructor
      · intro ha
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
          (Ideal.Quotient.eq_zero_iff_mem.mp ha)
        refine ⟨Ideal.Quotient.mk I b, ?_⟩
        change Ideal.Quotient.mk J (y * b) = Ideal.Quotient.mk J a
        rw [hb]
      · rintro ⟨b, hb⟩
        rw [← hb]
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        change Ideal.Quotient.mk P (y * b) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton.mpr ⟨b, rfl⟩)
    exact Module.Finite.of_exact hexact (Ideal.Quotient.factor_surjective hJP)

private theorem finite_closure_quotient_of_extension
    (R L E : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field L] [Field E] [Algebra R L] [Algebra R E] [Algebra L E]
    [IsScalarTower R L E] (x : R)
    [Module.Finite R ((integralClosure R E) ⧸
      Ideal.span ({algebraMap R (integralClosure R E) x} : Set (integralClosure R E)))] :
    Module.Finite R ((integralClosure R L) ⧸
      (Ideal.span ({x} : Set R) • ⊤ : Submodule R (integralClosure R L))) := by
  let S := integralClosure R L
  let T := integralClosure R E
  let g := IsScalarTower.toAlgHom R L E
  let f : S →ₐ[R] T := (g.comp S.val).codRestrict T (fun a ↦ a.property.map g)
  have hf : Function.Injective f := fun a b h ↦
    Subtype.ext (g.injective (congrArg (fun t : T ↦ (t : E)) h))
  let I : Ideal S := Ideal.span {algebraMap R S x}
  let J : Ideal T := Ideal.span {algebraMap R T x}
  have hcomap : J.comap f = I := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      by_cases hxL : algebraMap R L x = 0
      · have hxT : algebraMap R T x = 0 := by
          apply Subtype.ext
          change algebraMap R E x = 0
          rw [IsScalarTower.algebraMap_apply R L E, hxL, map_zero]
        have ha : a = 0 := hf (by simpa only [hxT, zero_mul, map_zero] using hb)
        exact ⟨0, by simp [ha]⟩
      · have hxE : algebraMap L E (algebraMap R L x) ≠ 0 :=
          (map_ne_zero (algebraMap L E)).mpr hxL
        let cL := (a : L) / algebraMap R L x
        have hc : g cL = (b : E) := by
          change algebraMap L E ((a : L) / algebraMap R L x) = (b : E)
          rw [map_div₀]
          apply (div_eq_iff hxE).mpr
          have hb' := congrArg (fun t : T ↦ (t : E)) hb
          change g (a : L) = algebraMap R E x * (b : E) at hb'
          rw [← IsScalarTower.algebraMap_apply R L E, mul_comm]
          exact hb'
        have hcint : IsIntegral R cL :=
          (isIntegral_algHom_iff g g.injective).mp (hc ▸ b.property)
        refine ⟨⟨cL, hcint⟩, ?_⟩
        apply hf
        apply Subtype.ext
        change g (a : L) = g (algebraMap R L x * cL)
        rw [map_mul, hc, g.commutes]
        exact congrArg (fun t : T ↦ (t : E)) hb
    · rintro ⟨b, rfl⟩
      exact ⟨f b, by rw [map_mul, f.commutes]⟩
  let Q : (S ⧸ I) →ₐ[R] T ⧸ J := Ideal.quotientMapₐ J f hcomap.ge
  have hQ : Function.Injective Q := by
    exact Ideal.quotientMap_injective' (H := hcomap.ge) hcomap.le
  have : Module.Finite R (S ⧸ I) := Module.Finite.of_injective Q.toLinearMap hQ
  have hI : (Ideal.span ({x} : Set R) • ⊤ : Submodule R S) = I.restrictScalars R := by
    rw [Ideal.smul_top_eq_map, Ideal.map_span, Set.image_singleton]
  let e₁ := Submodule.quotEquivOfEq _ _ hI
  let e₂ := Submodule.Quotient.restrictScalarsEquiv R I
  exact Module.Finite.of_surjective (e₁.trans e₂).symm.toLinearMap
    (e₁.trans e₂).symm.surjective

/-- The reduction of a purely inseparable integral closure modulo a prime principal
ideal is finite. Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese),
proof before the application of Tag 031D.
(blueprint: lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite).

Proof:
If x = 0, R/xR is R; transport its N-2 hypothesis to its fraction field K and
apply it to L. Assume x is nonzero. Choose a common exponent q = p^e by taking
the maximum of exponents for a finite K-basis of L. Adjoin a q-th root y of x
inside an algebraic closure to get a finite extension L'/K with (L')^q in K.
The integral closure S in L embeds in the closure T in L'. For every a in T,
a^q belongs to R by normality. Also xT intersect R equals xR, by dividing
by the nonzero x in K and using normality. More generally S intersect xT = xS:
if a = xb in T and a is in L, then b = a/x is in L and integral over R.
Consequently S/xS injects R-linearly into T/xT. Since R is Noetherian, it
suffices to prove that T/xT is finite.

The root y is integral over R. The ideal yT consists exactly of those a in T
with a^q in xR: the converse follows because (a/y)^q belongs to R and hence
a/y is integral. This makes yT a prime lying over xR. Localize at xR; the
principal-ideal height bound gives a one-dimensional Noetherian local domain.
Tag 031F (lem-weil-pbc-dim-one-residue-field-extensions-finite) gives a finite
extension of residue fields at yT over xR. Its base is the fraction field of
R/xR. Every element of T/yT is integral over R/xR and this domain embeds in
the residue field at yT. Thus it embeds in the integral closure of R/xR in
that finite field extension. N-2 makes this latter closure finite, and
Noetherianity makes T/yT finite. Multiplication by y^i identifies T/yT with
y^i T/y^(i+1) T, because T is a domain and y is nonzero. The finite filtration
therefore makes T/y^q T = T/xT finite over R. The injection above gives
finiteness of S/xS over R. Its action factors through R/xR, so it is finite
over that quotient as asserted. No completeness assumption is needed. -/
theorem tate_purely_inseparable_closure_quotient_finite
    (R : Type u) (K L : Type v) [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsNoetherianRing R] (x : R) (hnormal : IsIntegrallyClosed R)
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L]
    [IsPurelyInseparable K L]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    (hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
      (FractionRing (R ⧸ Ideal.span ({x} : Set R)))) :
    Module.Finite (R ⧸ Ideal.span ({x} : Set R))
      ((integralClosure R L) ⧸
        (Ideal.span ({x} : Set R) • ⊤ : Submodule R (integralClosure R L))) := by
  classical
  let Ω := AlgebraicClosure L
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
  let e := IsPurelyInseparable.exponent K L
  let q := p ^ e
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R Ω x) hq
  let E := IntermediateField.adjoin L ({z} : Set Ω)
  have : FiniteDimensional L E := IntermediateField.finiteDimensional_adjoin <| by
    intro a ha
    have ha := Set.mem_singleton_iff.mp ha
    subst a
    apply IsIntegral.of_pow hq
    rw [hz]
    change IsIntegral L (algebraMap L Ω (algebraMap R L x))
    exact isIntegral_algebraMap
  have : FiniteDimensional K E := Module.Finite.trans L E
  let U : IntermediateField L Ω :=
    ((algebraMap K Ω).fieldRange.comap (iterateFrobenius Ω p e)).toIntermediateField
      (fun a ↦ by
        change (algebraMap L Ω a) ^ q ∈ (algebraMap K Ω).fieldRange
        obtain ⟨b, hb⟩ := IsPurelyInseparable.exponent_def' K p a
        refine ⟨b, ?_⟩
        change algebraMap L Ω (algebraMap K L b) = _
        rw [hb, map_pow])
  have hEU : E ≤ U := IntermediateField.adjoin_le_iff.mpr <| by
    intro a ha
    have ha := Set.mem_singleton_iff.mp ha
    subst a
    change z ^ q ∈ (algebraMap K Ω).fieldRange
    exact ⟨algebraMap R K x, by
      rw [← IsScalarTower.algebraMap_apply R K Ω, hz]⟩
  have : IsScalarTower R E Ω := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R Ω r = algebraMap L Ω (algebraMap R L r)
    rfl
  have : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq fun r ↦ by
    apply (algebraMap E Ω).injective
    change algebraMap R Ω r = algebraMap K Ω (algebraMap R K r)
    exact IsScalarTower.algebraMap_apply R K Ω r
  have hpow : ∀ a : E, a ^ q ∈ (algebraMap K E).range := by
    intro a
    obtain ⟨b, hb⟩ := hEU a.property
    refine ⟨b, (algebraMap E Ω).injective ?_⟩
    change algebraMap K Ω b = _
    change algebraMap K Ω b = (a : Ω) ^ q at hb
    simpa only [map_pow, IntermediateField.algebraMap_apply] using hb
  let yE : E := ⟨z, IntermediateField.subset_adjoin L _ (Set.mem_singleton z)⟩
  have hyE : yE ^ q = algebraMap R E x := by
    apply (algebraMap E Ω).injective
    simpa only [map_pow, IntermediateField.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply R E Ω] using hz
  let y : integralClosure R E :=
    ⟨yE, IsIntegral.of_pow hq (hyE ▸ isIntegral_algebraMap)⟩
  have hy : y ^ q = algebraMap R (integralClosure R E) x := Subtype.ext hyE
  have hfibre : Module.Finite R
      ((integralClosure R E) ⧸ Ideal.span ({y} : Set (integralClosure R E))) :=
    tate_root_closure_quotient_finite R K E x hnormal p hquot e hpow y hy
  have hpower : Module.Finite R
      ((integralClosure R E) ⧸ Ideal.span ({y ^ q} : Set (integralClosure R E))) :=
    finite_quotient_powers R (integralClosure R E) y q
  have : Module.Finite R ((integralClosure R E) ⧸
      Ideal.span ({algebraMap R (integralClosure R E) x} : Set (integralClosure R E))) := by
    let e' := Ideal.quotientEquivAlgOfEq R (congrArg (fun a ↦ Ideal.span ({a} :
      Set (integralClosure R E))) hy)
    exact Module.Finite.of_surjective e'.toLinearMap e'.surjective
  have : Module.Finite R ((integralClosure R L) ⧸
      (Ideal.span ({x} : Set R) • ⊤ : Submodule R (integralClosure R L))) :=
    finite_closure_quotient_of_extension R L E x
  exact Module.Finite.of_restrictScalars_finite R _ _
