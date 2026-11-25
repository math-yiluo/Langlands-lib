/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.RingTheory.CyclicExtensionFlatDescent
import WeilConjectures.RingTheory.DirectSumExtensionAssembly
import WeilConjectures.RingTheory.TorsionCyclicPresentation
import WeilConjectures.RingTheory.TorsionHomFlatComparison

/-!
# Descent of extensions with an ideal-power torsion quotient

Source: Stacks Project, Dualizing Complexes, Lemma 05EH (blueprint:
lem-weil-pbc-torsion-extension-flat-descent).

Base change is written `S ⊗[R] M`, as in Mathlib's tensor product API; this is
canonically the source's `M ⊗[R] S`. Exactness is expressed by injectivity,
`Function.Exact`, and surjectivity of the two linear maps.
-/

@[expose] public section

universe u v w x y

open TensorProduct

namespace LinearMap

/--
Source: Stacks Project, Dualizing Complexes, Lemma 05EH, in the form used in
the proof of More on Algebra, Proposition 05ER
(blueprint: lem-weil-pbc-torsion-extension-flat-descent).

The hypotheses say that `S` is flat over `R`, that `R/I → S/IS` is an
isomorphism, and that `Q` is `I`-power torsion.  The conclusion constructs an
extension of `Q` by `N` whose base change is the given extension, together
with an isomorphism preserving both end maps.

Proof:
1. Choose a surjection `P = ⨁ j, R/I^(n j) → Q` with torsion kernel `K`
   (lem-weil-pbc-torsion-cyclic-presentation). Flat tensor exactness and tensor
   right exactness identify `K_S` with the kernel of `P_S → Q_S`.
2. Pull back the given extension to `P_S`: its middle module is the pairs
   `(m,x)` with `π(m) = p_S(x)`. Its injection sends `n` to `(ι(n),0)`.
   Descend each cyclic summand by lem-weil-pbc-cyclic-extension-flat-descent,
   then assemble them by lem-weil-pbc-direct-sum-extension-assembly. Obtain
   an extension `N → E_P → P` and an extension isomorphism `α : (E_P)_S ≃ T`.
3. The kernel has the canonical lift `z ↦ (0,k_S(z))` into `T`. Transport
   this through `α`. Torsion Hom comparison (lem-weil-pbc-torsion-hom-flat-comparison)
   descends it to `s : K → E_P`; injectivity of the same comparison gives
   `b s = k`. Thus `s` is injective and its image meets the image of `N` trivially.
4. Put `E = E_P/s(K)` (def-weil-pbc-quotient-module). The injection of `N`
   stays injective by step 3. The map `p b` kills `s(K)` and induces `q`.
   Surjectivity follows from that of `p` and `b`. If `q([e]) = 0`, write
   `b(e) = k(z)`; then `e-s(z)` lies in the image of `N`, proving exactness.
5. Flat tensor exactness and tensor right exactness identify `E_S` with
   `(E_P)_S/s_S(K_S)`. Under `α` the submodule being quotiented is precisely
   the kernel of the surjective projection `T → M'`. This gives `θ`.
   The formula `α(a_S(n)) = (ι(n),0)` gives `θ j_S = ι`; the defining
   equation of `T` gives `π θ = q_S`, as required. -/
theorem exists_torsion_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map))
    {N : Type w} [AddCommGroup N] [Module R N]
    {Q : Type x} [AddCommGroup Q] [Module R Q]
    (hQ : ∀ x : Q, ∃ n : ℕ, 1 ≤ n ∧ ∀ r ∈ I ^ n, r • x = 0)
    {M' : Type y} [AddCommGroup M'] [Module S M']
    (ι : S ⊗[R] N →ₗ[S] M')
    (π : M' →ₗ[S] S ⊗[R] Q)
    (_hι : Function.Injective ι) (_hιπ : Function.Exact ι π)
    (_hπ : Function.Surjective π) :
    ∃ (E : Type (max u w x)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] Q),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] M',
        θ.toLinearMap.comp (j.baseChange S) = ι ∧
        π.comp θ.toLinearMap = q.baseChange S := by
  classical
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  -- Step 1: lift only the presentation universe, preserving the requested universe of E.
  let eQ : ULift.{u} Q ≃ₗ[R] Q := ULift.moduleEquiv
  obtain ⟨J, n, hn, p₀, hp₀, hK₀, _⟩ :=
    I.exists_torsion_cyclic_presentation (ULift.{u} Q) (by
      intro z
      obtain ⟨m, hm, hz⟩ := hQ z.down
      exact ⟨m, hm, fun r hr => ULift.down_injective (hz r hr)⟩)
  let P := DirectSum J (fun j => R ⧸ I ^ n j)
  let p : P →ₗ[R] Q := eQ.toLinearMap.comp p₀
  have hp : Function.Surjective p := eQ.surjective.comp hp₀
  have hK : ∀ z : ker p, ∃ m : ℕ, ∀ r ∈ I ^ m, r • z = 0 := by
    intro z
    have hz : p₀ z.val = 0 := eQ.injective (by simpa [p] using z.property)
    obtain ⟨m, _, hm⟩ := hK₀ ⟨z.val, hz⟩
    refine ⟨m, fun r hr => ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : ker p₀ => z.val) (hm r hr)
  let k : ker p →ₗ[R] P := (ker p).subtype
  have hkp : Function.Exact k p := exact_subtype_ker_map p
  have hkSp : Function.Exact (k.baseChange S) (p.baseChange S) :=
    Module.Flat.lTensor_exact S hkp
  have hpS : Function.Surjective (p.baseChange S) := p.baseChange_surjective S hp
  -- Step 2: pull back to the cyclic presentation and descend summand by summand.
  let T : Submodule S (M' × (S ⊗[R] P)) :=
    { carrier := {z | π z.1 = p.baseChange S z.2}
      zero_mem' := by simp
      add_mem' := by intro z t hz ht; simpa using congrArg₂ (· + ·) hz ht
      smul_mem' := by intro r z hz; simpa using congrArg (r • ·) hz }
  let a : S ⊗[R] N →ₗ[S] T :=
    { toFun := fun z => ⟨(ι z, 0), by
        change π (ι z) = p.baseChange S 0
        simpa using (_hιπ (ι z)).mpr ⟨z, rfl⟩⟩
      map_add' := by intro z t; apply Subtype.ext; simp
      map_smul' := by intro r z; apply Subtype.ext; simp }
  let b : T →ₗ[S] S ⊗[R] P := (snd S M' (S ⊗[R] P)).comp T.subtype
  let c : T →ₗ[S] M' := (fst S M' (S ⊗[R] P)).comp T.subtype
  have ha : Function.Injective a := by
    intro z t h
    apply _hι
    exact congrArg (fun v : T => v.val.1) h
  have hab : Function.Exact a b := by
    intro z
    change z.val.2 = 0 ↔ ∃ t, a t = z
    constructor
    · intro hz
      have hzπ : π z.val.1 = 0 := by
        have h := z.property
        change π z.val.1 = p.baseChange S z.val.2 at h
        simpa [hz] using h
      obtain ⟨t, ht⟩ := (_hιπ z.val.1).mp hzπ
      refine ⟨t, Subtype.ext ?_⟩
      exact Prod.ext ht hz.symm
    · rintro ⟨t, rfl⟩
      rfl
  have hb : Function.Surjective b := by
    intro x
    obtain ⟨m, hm⟩ := _hπ (p.baseChange S x)
    exact ⟨⟨(m, x), hm⟩, rfl⟩
  obtain ⟨E₀, _, _, j₀, q₀, hj₀, hjq₀, hq₀, α, hαj, hqα⟩ :=
    extension_descends_of_summands hflat (fun j : J => R ⧸ I ^ n j)
      (fun j T _ _ a b ha hab hb =>
        exists_cyclic_extension_flat_descent hflat I hI hquot (n j) (hn j)
          a b ha hab hb) a b ha hab hb
  -- Step 3: descend the canonical kernel lift and reflect its projection identity.
  let t : S ⊗[R] ker p →ₗ[S] T :=
    { toFun := fun z => ⟨(0, k.baseChange S z), by
        change π 0 = p.baseChange S (k.baseChange S z)
        simpa using ((hkSp (k.baseChange S z)).mpr ⟨z, rfl⟩).symm⟩
      map_add' := by intro z z'; apply Subtype.ext; simp
      map_smul' := by intro r z; apply Subtype.ext; simp }
  obtain ⟨s, hs⟩ :=
    (baseChange_bijective_of_ideal_power_torsion hflat I hI hquot hK).surjective
      (α.symm.toLinearMap.comp t)
  have hqs : q₀.comp s = k := by
    apply (baseChange_bijective_of_ideal_power_torsion hflat I hI hquot hK).injective
    rw [baseChange_comp, hs]
    apply LinearMap.ext
    intro z
    have h := congrArg (fun f => f (α.symm (t z))) hqα
    change (α (α.symm (t z))).val.2 = q₀.baseChange S (α.symm (t z)) at h
    change q₀.baseChange S (α.symm (t z)) = k.baseChange S z
    rw [α.apply_symm_apply] at h
    exact h.symm
  have hqs_apply (z : ker p) : q₀ (s z) = z.val :=
    congrArg (fun f => f z) hqs
  -- Step 4: quotient by the lifted kernel and verify the descended exact sequence.
  let U : Submodule R E₀ := range s
  let E := E₀ ⧸ U
  let d : E₀ →ₗ[R] E := U.mkQ
  let j : N →ₗ[R] E := d.comp j₀
  have hU : U ≤ ker (p.comp q₀) := by
    rintro z ⟨k', rfl⟩
    change p (q₀ (s k')) = 0
    rw [hqs_apply]
    exact k'.property
  let q : E →ₗ[R] Q := U.liftQ (p.comp q₀) hU
  have hqd : q.comp d = p.comp q₀ := Submodule.liftQ_mkQ _ _ _
  have hqd_apply (e : E₀) : q (d e) = p (q₀ e) :=
    congrArg (fun f => f e) hqd
  have hd : Function.Surjective d := U.mkQ_surjective
  have hsd : Function.Exact s d := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ U
  have hj : Function.Injective j := by
    apply (injective_iff_map_eq_zero j).mpr
    intro z hz
    obtain ⟨k', hk'⟩ := (hsd (j₀ z)).mp hz
    have hzq : q₀ (j₀ z) = 0 := (hjq₀ (j₀ z)).mpr ⟨z, rfl⟩
    have hkzero : k' = 0 := by
      apply Subtype.ext
      have h := congrArg q₀ hk'
      simpa only [hqs_apply, hzq, Submodule.coe_zero] using h
    have hjzero : j₀ z = 0 := by simpa [hkzero] using hk'.symm
    exact hj₀ (by simpa using hjzero)
  have hjq : Function.Exact j q := by
    intro z
    obtain ⟨e, rfl⟩ := hd z
    change p (q₀ e) = 0 ↔ ∃ n', d (j₀ n') = d e
    constructor
    · intro he
      let k' : ker p := ⟨q₀ e, he⟩
      have hqe : q₀ (e - s k') = 0 := by
        rw [map_sub, hqs_apply]
        exact sub_self _
      obtain ⟨n', hn'⟩ := (hjq₀ (e - s k')).mp hqe
      refine ⟨n', ?_⟩
      rw [hn', map_sub]
      have hs0 : d (s k') = 0 := (hsd (s k')).mpr ⟨k', rfl⟩
      simp [hs0]
    · rintro ⟨n', hn'⟩
      have h := congrArg q hn'
      have hn0 : q₀ (j₀ n') = 0 := (hjq₀ (j₀ n')).mpr ⟨n', rfl⟩
      simpa only [hqd_apply, hn0, map_zero] using h.symm
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨v, rfl⟩ := hp z
    obtain ⟨e, rfl⟩ := hq₀ v
    exact ⟨d e, rfl⟩
  -- Step 5: the two surjections have the same kernel after base change.
  let f : S ⊗[R] E₀ →ₗ[S] M' := c.comp α.toLinearMap
  have hf : Function.Surjective f := by
    intro m
    obtain ⟨x, hx⟩ := hpS (π m)
    exact ⟨α.symm ⟨(m, x), hx.symm⟩, by simp [f, c, comp_apply]⟩
  have hsf : Function.Exact (s.baseChange S) f := by
    intro x
    constructor
    · intro hx
      have hx₁ : (α x).val.1 = 0 := hx
      have hx₂ : p.baseChange S (α x).val.2 = 0 := by
        have h := (α x).property
        change π (α x).val.1 = p.baseChange S (α x).val.2 at h
        simpa [hx₁] using h.symm
      obtain ⟨z, hz⟩ := (hkSp (α x).val.2).mp hx₂
      refine ⟨z, α.injective ?_⟩
      rw [hs]
      change α (α.symm (t z)) = α x
      rw [α.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext hx₁.symm hz
    · rintro ⟨z, rfl⟩
      rw [hs]
      change (α (α.symm (t z))).val.1 = 0
      rw [α.apply_symm_apply]
      rfl
  have hsdS : Function.Exact (s.baseChange S) (d.baseChange S) :=
    Module.Flat.lTensor_exact S hsd
  have hdS : Function.Surjective (d.baseChange S) := d.baseChange_surjective S hd
  have hker : ker (d.baseChange S) = ker f :=
    (LinearMap.exact_iff.mp hsdS).trans (LinearMap.exact_iff.mp hsf).symm
  let θ : S ⊗[R] E ≃ₗ[S] M' :=
    ((d.baseChange S).quotKerEquivOfSurjective hdS).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf))
  have hθd (x : S ⊗[R] E₀) : θ (d.baseChange S x) = f x := by
    have h : ((d.baseChange S).quotKerEquivOfSurjective hdS).symm
        (d.baseChange S x) = (ker (d.baseChange S)).mkQ x := by
      apply ((d.baseChange S).quotKerEquivOfSurjective hdS).injective
      simp
    simp [θ, h]
  refine ⟨E, inferInstance, inferInstance, j, q, hj, hjq, hq, θ, ?_, ?_⟩
  · apply LinearMap.ext
    intro z
    change θ ((d.comp j₀).baseChange S z) = ι z
    rw [baseChange_comp, comp_apply, hθd]
    have h := congrArg (fun g => g z) hαj
    change α (j₀.baseChange S z) = a z at h
    change (α (j₀.baseChange S z)).val.1 = ι z
    rw [h]
    rfl
  · apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := hdS z
    change π (θ (d.baseChange S x)) = q.baseChange S (d.baseChange S x)
    rw [hθd]
    have hqS : (q.baseChange S).comp (d.baseChange S) =
        (p.baseChange S).comp (q₀.baseChange S) := by
      rw [← baseChange_comp, hqd, baseChange_comp]
    have h := congrArg (fun g => g x) hqS
    change q.baseChange S (d.baseChange S x) =
      p.baseChange S (q₀.baseChange S x) at h
    rw [h]
    have hα := congrArg (fun g => g x) hqα
    change (α x).val.2 = q₀.baseChange S x at hα
    change π (α x).val.1 = p.baseChange S (q₀.baseChange S x)
    rw [← hα]
    exact (α x).property

end LinearMap
