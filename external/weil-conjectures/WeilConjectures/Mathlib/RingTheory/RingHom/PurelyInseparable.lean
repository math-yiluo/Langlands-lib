/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# Purely inseparable ring homomorphisms of fields and isomorphisms

Bijective ring homomorphisms of fields are purely inseparable, and purely inseparable ring
homomorphisms of fields are stable under composition with bijective ones on either side.
-/

@[expose] public section

/-- A bijective ring homomorphism between fields is purely inseparable. -/
lemma RingHom.IsPurelyInseparable.of_bijective {K L : Type*} [Field K] [Field L] (e : K →+* L)
    (he : Function.Bijective e) : e.IsPurelyInseparable := by
  let _ : Algebra K L := e.toAlgebra
  change IsPurelyInseparable K L
  rw [isPurelyInseparable_iff]
  intro x
  obtain ⟨y, rfl⟩ := he.2 x
  exact ⟨isIntegral_algebraMap, fun _ ↦ ⟨y, rfl⟩⟩

/-- Purely inseparable ring homomorphisms of fields are stable under composition with
isomorphisms. -/
lemma RingHom.IsPurelyInseparable.comp_of_bijective {K L M N : Type*} [Field K] [Field L]
    [Field M] [Field N] {e : K →+* L} {f : L →+* M} {e' : M →+* N} (he : Function.Bijective e)
    (hf : f.IsPurelyInseparable) (he' : Function.Bijective e') :
    (e'.comp (f.comp e)).IsPurelyInseparable :=
  RingHom.IsPurelyInseparable.comp
    (RingHom.IsPurelyInseparable.comp (RingHom.IsPurelyInseparable.of_bijective e he) hf)
    (RingHom.IsPurelyInseparable.of_bijective e' he')

/-- If `e' ∘ f = g ∘ e` with `e`, `e'` bijective, then `f` is purely inseparable iff `g` is. -/
lemma RingHom.IsPurelyInseparable.of_comp_eq_comp {K L M N : Type*} [Field K] [Field L]
    [Field M] [Field N] {e : K →+* M} {f : K →+* L} {g : M →+* N} {e' : L →+* N}
    (he : Function.Bijective e) (he' : Function.Bijective e') (h : e'.comp f = g.comp e)
    (hg : g.IsPurelyInseparable) : f.IsPurelyInseparable := by
  let e'' : N ≃+* L := (RingEquiv.ofBijective e' he').symm
  have hf : f = e''.toRingHom.comp (g.comp e) := by
    rw [← h]
    ext x
    exact ((RingEquiv.ofBijective e' he').symm_apply_apply (f x)).symm
  rw [hf]
  exact RingHom.IsPurelyInseparable.comp_of_bijective he hg e''.bijective


/-- If `e' ∘ f = g ∘ e` with `e`, `e'` bijective, then `g` is purely inseparable iff `f` is. -/
lemma RingHom.IsPurelyInseparable.of_comp_eq_comp' {K L M N : Type*} [Field K] [Field L]
    [Field M] [Field N] {e : K →+* M} {f : K →+* L} {g : M →+* N} {e' : L →+* N}
    (he : Function.Bijective e) (he' : Function.Bijective e') (h : e'.comp f = g.comp e)
    (hf : f.IsPurelyInseparable) : g.IsPurelyInseparable := by
  let e'' : M ≃+* K := (RingEquiv.ofBijective e he).symm
  have hg : g = e'.comp (f.comp e''.toRingHom) := by
    ext m
    change g m = e' (f (e'' m))
    rw [← RingHom.comp_apply e' f, h, RingHom.comp_apply]
    congr 1
    exact ((RingEquiv.ofBijective e he).apply_symm_apply m).symm
  rw [hg]
  exact RingHom.IsPurelyInseparable.comp_of_bijective e''.bijective hf he'
