/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.Ring.Idempotent
import WeilConjectures.RingTheory.CompletionFiniteExtensionDecomposition
import WeilConjectures.RingTheory.PairHenselizationCompletionData

/-!
# The idempotent selecting a finite-algebra completion factor

Source: Stacks Project, Tag 07NC, the finite product decomposition and its selected factor.
-/

@[expose] public section

universe u v

namespace Algebra

private theorem completion_equiv_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (L : A ≃+* B) (h : I.map L.toRingHom = J) :
    ∃ α : AdicCompletion I A ≃+* AdicCompletion J B,
      ∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
        AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
        AdicCompletion.evalₐ J n (α x) = Ideal.Quotient.mk (J ^ n) (L a) := by
  subst J
  obtain ⟨α, hα, _⟩ := RingTheory.pair_henselization_completion_data A B I L.toRingHom
    (by
      intro n hn
      exact (Ideal.quotientEquiv (I ^ n) ((I ^ n).map L.toRingHom) L rfl).bijective)
  exact ⟨α, hα⟩

private theorem factor_idempotent
    {A : Type*} {C : Type*} {ι : Type*} {D : ι → Type*}
    [CommRing A] [CommRing C] [∀ i, CommRing (D i)]
    (E : A ≃+* (∀ i, D i)) (i : ι) (α : D i ≃+* C)
    (F : A →+* C) (hF : ∀ a, F a = α (E a i)) (γ : A)
    (hunit : IsUnit (E γ i)) :
    ∃ e v : A, IsIdempotentElem e ∧ v * γ = e ∧ F e = 1 ∧
      Function.Surjective F ∧ (∀ t, F t = 0 → e * t = 0) := by
  classical
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hunit
  let e : A := E.symm (Pi.single i (1 : D i))
  let v : A := E.symm (Pi.single i c)
  have he : E e = Pi.single i 1 := E.apply_symm_apply _
  have hv : E v = Pi.single i c := E.apply_symm_apply _
  refine ⟨e, v, ?_, ?_, ?_, ?_, ?_⟩
  · change e * e = e
    apply E.injective
    ext a
    rw [E.map_mul, he]
    by_cases ha : a = i
    · subst a
      simp only [Pi.mul_apply, Pi.single_eq_same, one_mul]
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne ha, zero_mul]
  · apply E.injective
    ext a
    rw [E.map_mul, hv, he]
    by_cases ha : a = i
    · subst a
      simpa only [Pi.mul_apply, Pi.single_eq_same, mul_comm] using hc
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne ha, zero_mul]
  · rw [hF, he, Pi.single_eq_same, α.map_one]
  · intro b
    refine ⟨E.symm (Pi.single i (α.symm b)), ?_⟩
    rw [hF, E.apply_symm_apply, Pi.single_eq_same, α.apply_symm_apply]
  · intro t ht
    have ht₀ : E t i = 0 := α.injective (by rw [← hF, ht, α.map_zero])
    apply E.injective
    ext a
    rw [E.map_mul, E.map_zero, he]
    by_cases ha : a = i
    · subst a
      simp only [Pi.mul_apply, Pi.single_eq_same, ht₀, mul_zero, Pi.zero_apply]
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne ha, zero_mul, Pi.zero_apply]

private theorem tensor_factor_idempotent
    {R A B C : Type*} {ι : Type*} {D : ι → Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [∀ i, CommRing (D i)]
    [Algebra R A] [Algebra R B]
    (E : TensorProduct R A B ≃+* (∀ i, D i)) (i : ι) [Algebra B (D i)]
    (α : D i ≃+* C) (F : TensorProduct R A B →+* C)
    (θ : A →+* D i) (ψ : A →+* C) (f : B →+* C)
    (hleft : ∀ x, E (TensorProduct.tmul R x 1) i = θ x)
    (hright : ∀ y, E (TensorProduct.tmul R 1 y) i = algebraMap B (D i) y)
    (hθψ : ∀ x, α (θ x) = ψ x) (hα : ∀ y, α (algebraMap B (D i) y) = f y)
    (hF : ∀ x y, F (TensorProduct.tmul R x y) = ψ x * f y)
    (g : B) (hunit : IsUnit (algebraMap B (D i) g)) :
    ∃ e v : TensorProduct R A B, IsIdempotentElem e ∧
      v * TensorProduct.tmul R 1 g = e ∧ F e = 1 ∧
      Function.Surjective F ∧ (∀ t, F t = 0 → e * t = 0) := by
  have hEtmul (x : A) (y : B) :
      E (TensorProduct.tmul R x y) i = θ x * algebraMap B (D i) y := by
    rw [show TensorProduct.tmul R x y =
      TensorProduct.tmul R x 1 * TensorProduct.tmul R 1 y by
        rw [TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    rw [E.map_mul, Pi.mul_apply, hleft, hright]
  have hproj (t : TensorProduct R A B) : F t = α (E t i) := by
    induction t using _root_.TensorProduct.inductionOn with
    | tmul x y => rw [hF, hEtmul, α.map_mul, hθψ, hα]
    | add x y hx hy => rw [F.map_add, E.map_add, Pi.add_apply, α.map_add, hx, hy]
  apply factor_idempotent E i α F hproj (TensorProduct.tmul R 1 g)
  rwa [hright]

/-- Select the finite completion factor before transferring it to the larger tensor.

Source: Stacks Project, Algebra, proof of Lemma Tag 07NC, the finite-algebra product
and the unit on the selected factor
(blueprint: lem-weil-pbc-finite-completion-factor-idempotent).

Proof: put q' = q contracted to S'. Clearing powers of g identifies S' localized
at q' with S localized at q, since g lies outside the primes. The isomorphism
identifies maximal ideals and their powers. The quotient isomorphisms commute
with reduction and give an isomorphism alpha of completions. This isomorphism
agrees on the images of S' with the natural map to the completion of S_q.
Apply completion_finite_extension_decomposition to S' at p. The ideal q' is prime and lies
over p, so it indexes one of the product factors. Compare the factor's map theta
from the completion of R_p with psi: on each nth quotient represent the coordinate
of x by a in R_p, apply the levelwise formulas and the local-ring square. Their
coordinates agree after alpha, hence alpha(theta(x)) = psi(x). Consequently the
specified phi composed with the tensor inclusion j is alpha composed with this
factor projection: check on x tensor y by multiplying x tensor 1 and 1 tensor y.
Let e be the inverse image of the tuple equal to 1 at q' and 0 elsewhere under
the finite product equivalence. It is idempotent, maps to 1 under phi j, and its
multiplication kills exactly the kernel of that factor projection. The image of
gamma at q' is a unit: g is outside q', hence is a unit in the local ring and
in its completion. Let v be the inverse image of the tuple equal to its inverse
at q' and 0 elsewhere. Then v gamma = e. The factor projection is surjective:
for c in the target, take the tuple supported at q' with value alpha inverse(c).
This also proves the asserted surjectivity of phi j. The complementary product
can be empty, and the formulas remain valid in that case. -/
theorem finite_completion_factor_idempotent
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (q : PrimeSpectrum S)
    (S' : Subalgebra R S) [Module.Finite R S']
    (g : S') (hg : g.1 ∉ q.asIdeal)
    (haway : Function.Bijective (Localization.awayMap S'.val.toRingHom g)) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    let T := TensorProduct R Rph S'
    let U := TensorProduct R Rph S
    let j := (TensorProduct.map (AlgHom.id R Rph) S'.val).toRingHom
    let γ := TensorProduct.tmul R (1 : Rph) g
    ∀ (ψ : Rph →+* Sqh),
      (∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a)) →
      ∀ (φ : U →+* Sqh),
        (∀ (x : Rph) (y : S), φ (TensorProduct.tmul R x y) =
          ψ x * algebraMap Sq Sqh (algebraMap S Sq y)) →
        ∃ e v : T, IsIdempotentElem e ∧ v * γ = e ∧ φ (j e) = 1 ∧
          Function.Surjective (φ.comp j) ∧ (∀ t, φ (j t) = 0 → e * t = 0) := by
  classical
  intro p Rp Sq Ip Iq Rph Sqh f T U j γ ψ hψ φ hφ
  let q' : Ideal S' := q.asIdeal.comap S'.val.toRingHom
  have : q'.IsPrime := Ideal.comap_isPrime _ _
  have : q.asIdeal.LiesOver q' := ⟨rfl⟩
  have hsat : S'.saturation (q.asIdeal.primeCompl ⊓ S'.toSubmonoid) (by simp) = ⊤ := by
    apply top_unique
    intro y hy
    obtain ⟨z, n, hz⟩ := Localization.awayMap_surjective_iff.mp haway.2 y
    change z.1 = g.1 ^ n * y at hz
    refine ⟨g.1 ^ n, ⟨?_, ?_⟩, ?_⟩
    · exact q.asIdeal.primeCompl.pow_mem hg n
    · exact S'.pow_mem g.2 n
    · rw [← hz]
      exact z.2
  let l : Localization.AtPrime q' →+* Sq :=
    Localization.localRingHom q' q.asIdeal S'.val.toRingHom rfl
  have hl : Function.Bijective l :=
    Localization.localRingHom_bijective_of_saturated_inf_eq_top S hsat q'
  let L : Localization.AtPrime q' ≃+* Sq := RingEquiv.ofBijective l hl
  let I' := IsLocalRing.maximalIdeal (Localization.AtPrime q')
  have hI : I'.map l = Iq := IsLocalRing.map_maximalIdeal_of_surjective l hl.2
  obtain ⟨α, hα⟩ := completion_equiv_of_ringEquiv I' Iq L hI
  have : q'.LiesOver p := ⟨rfl⟩
  let q₀ : p.primesOver S' := ⟨q', inferInstance, inferInstance⟩
  let D := fun a : p.primesOver S' ↦
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime a.1))
      (Localization.AtPrime a.1)
  let := TensorProduct.rightAlgebra (R := R) (A := Rph) (B := S')
  obtain ⟨_, E, θ, hθ, hE⟩ :=
    AdicCompletion.completion_finite_extension_decomposition R S' p
  have hsquare : l.comp
      (Localization.localRingHom p q' (algebraMap R S')
        (Ideal.LiesOver.over (P := q') (p := p))) = f := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    dsimp only [RingHom.comp_apply, l, f, Rp, Sq]
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map,
      Localization.localRingHom_to_map]
    rfl
  have hθψ (x : Rph) : α (θ q₀ x) = ψ x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ Ip n x)
    rw [hα n _ _ (hθ q₀ n x a ha.symm), hψ n x a ha.symm]
    congr 1
    exact DFunLike.congr_fun hsquare a
  have hαbase (y : S') :
      α (algebraMap (Localization.AtPrime q') (D q₀)
        (algebraMap S' (Localization.AtPrime q') y)) =
      algebraMap Sq Sqh (algebraMap S Sq y.1) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ Iq n
      (α (AdicCompletion.of I' (Localization.AtPrime q')
        (algebraMap S' (Localization.AtPrime q') y))) =
      AdicCompletion.evalₐ Iq n (AdicCompletion.of Iq Sq (algebraMap S Sq y.1))
    rw [hα n _ _ (AdicCompletion.evalₐ_of I' n _)]
    rw [AdicCompletion.evalₐ_of]
    congr 1
    exact Localization.localRingHom_to_map q' q.asIdeal S'.val.toRingHom rfl y
  apply tensor_factor_idempotent E.toRingEquiv q₀ α (φ.comp j) (θ q₀) ψ
    ((algebraMap Sq Sqh).comp ((algebraMap S Sq).comp S'.val.toRingHom))
    (fun x ↦ hE x q₀) (fun y ↦ congrFun (E.commutes y) q₀) hθψ hαbase
    (fun x y ↦ hφ x y.1) g
  exact (IsLocalization.map_units (Localization.AtPrime q')
    (⟨g, hg⟩ : q'.primeCompl)).map (algebraMap (Localization.AtPrime q') (D q₀))

end Algebra
