/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Nakayama

/-! # Kernel rigidity for a flat closed-fibre presentation

Source: Stacks Project, Tag 07NQ, proof of (2) implies (3), the Nakayama argument
for the map from the base change of the presentation to the target.
-/

@[expose] public section

universe u v w x

open IsLocalRing

namespace RingHom

private theorem injective_of_flat_target_of_ker_le
    {A : Type u} {D : Type v} {B : Type w}
    [CommRing A] [CommRing D] [CommRing B]
    [IsLocalRing A] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Algebra A B] [Module.Flat A B]
    [IsLocalHom (algebraMap A D)]
    (g : D →ₐ[A] B) (hg : Function.Surjective g)
    (hk : RingHom.ker g.toRingHom ≤ (maximalIdeal A).map (algebraMap A D)) :
    Function.Injective g := by
  let K := RingHom.ker g.toRingHom
  have hlin : g.toLinearMap.ker = K.restrictScalars A := rfl
  have hle : g.toLinearMap.ker ≤ (maximalIdeal A) • (⊤ : Submodule A D) := by
    rw [Ideal.smul_top_eq_map]
    exact hk
  have heq := LinearMap.ker_inf_smul_top_eq_smul_of_flat (maximalIdeal A)
    g.toLinearMap hg
  rw [inf_eq_left.mpr hle, hlin, ← Ideal.smul_restrictScalars] at heq
  have hK : K ≤ (maximalIdeal A).map (algebraMap A D) • K := by
    intro d hd
    exact (SetLike.ext_iff.mp heq d).mp hd
  have hm : (maximalIdeal A).map (algebraMap A D) ≤ (⊥ : Ideal D).jacobson := by
    rw [Ideal.jacobson_bot, IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Ideal.map_le_iff_le_comap.mpr (by
      intro a ha
      exact map_nonunit (algebraMap A D) a ha)
  have hzero : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    _ K (IsNoetherian.noetherian K) hK hm
  exact (RingHom.injective_iff_ker_eq_bot g.toRingHom).mpr hzero

/-- A surjective presentation with no extra closed-fibre kernel has only the equations
coming from the base, provided the target is flat over the base.

Source: Stacks Project, Tag 07NQ, proof of (2) implies (3), the isomorphism
`T tensor_R A -> B` and its Nakayama proof.
(blueprint: lem-weil-pbc-flat-closed-fibre-kernel-rigidity)

Proof: Commutativity gives `(ker q)T ≤ ker v`. Put `D = T/(ker q)T` and use the
surjection q to identify `R/ker q` with A, giving D its A-algebra structure.
The descended map D -> B is surjective and its kernel is contained in m_A D.
Flatness of B gives `ker(D -> B) intersect m_A D = m_A ker(D -> B)`.
Thus the kernel equals its product with m_A D. It is finitely generated over D,
and m_A D lies in the maximal ideal of the Noetherian local ring D. Nakayama
kills it. Pulling back along T -> D gives the required kernel equality.
This does not require flatness of R -> T or completeness of any ring. -/
theorem ker_eq_map_of_flat_of_ker_le_maximal
    {R : Type u} {A : Type v} {T : Type w} {B : Type x}
    [CommRing R] [CommRing A] [CommRing T] [CommRing B]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing T] [IsNoetherianRing T]
    (q : R →+* A) [IsLocalHom q] (f : A →+* B) (hf : f.Flat)
    (j : R →+* T) [IsLocalHom j] (v : T →+* B)
    (hq : Function.Surjective q) (hv : Function.Surjective v)
    (hcomm : v.comp j = f.comp q)
    (hk : RingHom.ker v ≤ (maximalIdeal R).map j) :
    RingHom.ker v = (RingHom.ker q).map j := by
  let K := (RingHom.ker q).map j
  have hK : K ≤ RingHom.ker v := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change v (j r) = 0
    rw [show v (j r) = f (q r) from RingHom.congr_fun hcomm r]
    rw [show q r = 0 from hr, map_zero]
  have hKm : K ≤ maximalIdeal T := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    apply map_nonunit j r
    exact mem_nonunits_iff.mpr (by
      intro hu
      have : IsUnit (0 : A) := (show q r = 0 from hr) ▸ hu.map q
      exact this.ne_zero rfl)
  have hKne : K ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top hKm
  let D := T ⧸ K
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hKne
  have : IsLocalRing D := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let π := Ideal.Quotient.mk K
  let e := q.quotientKerEquivOfSurjective hq
  let j' : (R ⧸ RingHom.ker q) →+* D := Ideal.quotientMap K j Ideal.le_comap_map
  let a : A →+* D := j'.comp e.symm.toRingHom
  have haq : a.comp q = π.comp j := by
    ext r
    change j' (e.symm (q r)) = π (j r)
    rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hq r, e.symm_apply_apply]
    rfl
  let g : D →+* B := Ideal.Quotient.lift K v hK
  have hga : g.comp a = f := by
    apply RingHom.ext
    intro a0
    obtain ⟨r, rfl⟩ := hq a0
    change g (a (q r)) = f (q r)
    rw [show a (q r) = π (j r) from RingHom.congr_fun haq r]
    exact RingHom.congr_fun hcomm r
  let : Algebra A D := a.toAlgebra
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := hf
  have : IsLocalHom π := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom a := by
    constructor
    intro a0 ha0
    obtain ⟨r, rfl⟩ := hq a0
    apply q.isUnit_map
    apply isUnit_of_map_unit j r
    apply isUnit_of_map_unit π (j r)
    rw [← show a (q r) = π (j r) from RingHom.congr_fun haq r]
    exact ha0
  let gₐ : D →ₐ[A] B := { g with commutes' := RingHom.congr_fun hga }
  have hg : Function.Surjective gₐ :=
    Ideal.Quotient.lift_surjective_of_surjective K hK hv
  have hgm : RingHom.ker gₐ.toRingHom ≤ (maximalIdeal A).map a := by
    intro d hd
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective d
    have ht : t ∈ RingHom.ker v := hd
    have hm := Ideal.mem_map_of_mem π (hk ht)
    have heq : ((maximalIdeal R).map j).map π = (maximalIdeal A).map a := by
      rw [Ideal.map_map, ← haq, ← Ideal.map_map,
        IsLocalRing.map_maximalIdeal_of_surjective q hq]
    exact heq ▸ hm
  have hinj := injective_of_flat_target_of_ker_le gₐ hg hgm
  apply le_antisymm _ hK
  intro t ht
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  change v t = gₐ 0
  rw [map_zero]
  exact ht

end RingHom
