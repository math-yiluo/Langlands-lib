/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.Algebra.ExtOneDirectSum

/-!
# Descent of extensions with direct-sum quotient

Source: Stacks Project, More on Algebra, proof of Lemma 05EG
(blueprint: lem-weil-pbc-direct-sum-extension-assembly).

Base change is written `S ⊗[R] M`, as in `LinearMap.baseChange`; tensor symmetry identifies
this with the source's `M ⊗[R] S`. Short exactness is expressed by injectivity, `Function.Exact`,
and surjectivity, the module interpretation of `CategoryTheory.ShortComplex.ShortExact`
via `ShortExact.moduleCat_exact_iff_function_exact` and its injective/surjective lemmas,
as in `LinearMap.exists_cyclic_extension_flat_descent`.
-/

@[expose] public section

universe u v w x y z

open TensorProduct DirectSum

namespace LinearMap

private theorem glue_extension_maps
    {R : Type*} [CommRing R] {N F V : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup F] [Module R F]
    [AddCommGroup V] [Module R V]
    {J : Type*} [DecidableEq J] (C E : J → Type*)
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    (i : N →ₗ[R] F) (q : F →ₗ[R] ⨁ j, C j)
    (hi : Function.Injective i) (hiq : Function.Exact i q)
    (a : N →ₗ[R] V) (ij : ∀ j, N →ₗ[R] E j) (qj : ∀ j, E j →ₗ[R] C j)
    (hj : ∀ j, Function.Exact (ij j) (qj j) ∧ Function.Surjective (qj j))
    (f : ∀ j, E j →ₗ[R] F) (t : ∀ j, E j →ₗ[R] V)
    (hfi : ∀ j n, f j (ij j n) = i n)
    (hfq : ∀ j e, q (f j e) = DirectSum.lof R J C j (qj j e))
    (hti : ∀ j n, t j (ij j n) = a n) :
    ∃ g : F →ₗ[R] V, (∀ n, g (i n) = a n) ∧ ∀ j e, g (f j e) = t j e := by
  classical
  let fs := DirectSum.toModule R J F f
  let ts := DirectSum.toModule R J V t
  let ns := DirectSum.toModule R J N (fun _ ↦ LinearMap.id)
  have hqfs : q.comp fs = DirectSum.lmap qj := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro e
    simpa [fs] using hfq j e
  have hfis : fs.comp (DirectSum.lmap ij) = i.comp ns := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro n
    simpa [fs, ns] using hfi j n
  have htis : ts.comp (DirectSum.lmap ij) = a.comp ns := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro n
    simpa [ts, ns] using hti j n
  let p : N × (⨁ j, E j) →ₗ[R] F := i.coprod fs
  let v : N × (⨁ j, E j) →ₗ[R] V := a.coprod ts
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨d, hd⟩ := (DirectSum.lmap_surjective qj).mpr (fun j ↦ (hj j).2) (q x)
    have hx : q (x - fs d) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hqfs, hd, sub_self]
    obtain ⟨n, hn⟩ := (hiq _).mp hx
    refine ⟨(n, d), ?_⟩
    change i n + fs d = x
    rw [hn, sub_add_cancel]
  have hker : p.ker ≤ v.ker := by
    rintro ⟨n, d⟩ h
    change i n + fs d = 0 at h
    have hd : DirectSum.lmap qj d = 0 := by
      have hh := congrArg q h
      simpa only [map_add, hiq.apply_apply_eq_zero, zero_add, map_zero,
        ← LinearMap.comp_apply, hqfs] using hh
    have hdi : d ∈ (DirectSum.lmap ij).range := by
      rw [DirectSum.range_lmap]
      change ∀ j ∈ (Set.univ : Set J), d j ∈ (ij j).range
      intro j _
      apply (hj j).1 _ |>.mp
      have hh := congrArg (fun c : ⨁ j, C j ↦ c j) hd
      simpa using hh
    obtain ⟨d', rfl⟩ := hdi
    have hn : n + ns d' = 0 := by
      apply hi
      rw [map_add, map_zero]
      simpa only [← LinearMap.comp_apply, hfis] using h
    change a n + ts (DirectSum.lmap ij d') = 0
    rw [← LinearMap.comp_apply, htis, LinearMap.comp_apply, ← map_add, hn, map_zero]
  let g := (p.ker.liftQ v hker).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hg (x : N × (⨁ j, E j)) : g (p x) = v x := by
    simp [g, LinearMap.quotKerEquivOfSurjective_symm_apply]
  refine ⟨g, ?_, ?_⟩
  · intro n
    simpa [p, v] using hg (n, 0)
  · intro j e
    simpa [p, v, fs, ts] using hg (0, DirectSum.lof R J E j e)

private theorem extension_map_ext
    {R : Type*} [CommRing R] {N F V : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup F] [Module R F]
    [AddCommGroup V] [Module R V]
    {J : Type*} [DecidableEq J] (C E : J → Type*)
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    (i : N →ₗ[R] F) (q : F →ₗ[R] ⨁ j, C j) (hiq : Function.Exact i q)
    (qj : ∀ j, E j →ₗ[R] C j) (hqj : ∀ j, Function.Surjective (qj j))
    (f : ∀ j, E j →ₗ[R] F)
    (hfq : ∀ j e, q (f j e) = DirectSum.lof R J C j (qj j e))
    (g g' : F →ₗ[R] V) (hgi : ∀ n, g (i n) = g' (i n))
    (hgf : ∀ j e, g (f j e) = g' (f j e)) : g = g' := by
  classical
  let fs := DirectSum.toModule R J F f
  have hqfs : q.comp fs = DirectSum.lmap qj := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro e
    simpa [fs] using hfq j e
  have hgfs : g.comp fs = g'.comp fs := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro e
    simpa [fs] using hgf j e
  apply LinearMap.ext
  intro x
  obtain ⟨d, hd⟩ := (DirectSum.lmap_surjective qj).mpr hqj (q x)
  have hx : q (x - fs d) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply, hqfs, hd, sub_self]
  obtain ⟨n, hn⟩ := (hiq _).mp hx
  have hxn : x = i n + fs d := by rw [hn, sub_add_cancel]
  rw [hxn, map_add, map_add, hgi]
  exact congrArg (g' (i n) + ·) (DFunLike.congr_fun hgfs d)

/-- Source: Stacks Project, More on Algebra, proof of Lemma 05EG, the reduction using
compatibility of Ext with arbitrary direct sums
(blueprint: lem-weil-pbc-direct-sum-extension-assembly).

If every extension with quotient a base-changed summand descends along a flat ring map,
then every extension with quotient the base-changed direct sum descends, fixing both ends.
The middle modules `T` range over one universe `z` in the hypothesis and the conclusion;
the pullbacks `T_j` of the proof are submodules of `T`, so they lie in that universe.

Proof: Pull back the given extension along each base-changed canonical inclusion, and use
its descent hypothesis to choose an R-extension of that summand. Surjectivity of the
Ext-one direct-sum comparison (theorem-finite-etale-covers-proper-henselian--2) assembles these
classes into an R-extension of the direct sum. Base-changing extension equivalences preserves their
fixed endpoints, by identity and composition compatibility of def-weil-module-base-change.
Next use lem-weil-pbc-tensor-commutes-with-colimits to identify the base-changed direct sum
and its inclusions. The assembled sequence stays short exact by lem-weil-pbc-flat-tensor-exact
and lem-weil-pbc-tensor-right-exact. Pullbacks commute with flat base change: describe a
pullback as the kernel of the difference map out of a finite direct sum, use tensor's
compatibility with finite sums, and apply lem-weil-pbc-flat-tensor-exact to that kernel.
Consequently the assembled base-changed extension has the same pullback class on each
summand as the original extension. Injectivity of the Ext-one direct-sum comparison over S
(theorem-finite-etale-covers-proper-henselian--2) gives an isomorphism of extensions fixing both
ends. -/
theorem extension_descends_of_summands
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat)
    {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} (C : J → Type y) [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    (hC : ∀ (j : J) (T : Type z) [AddCommGroup T] [Module S T]
      (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] C j),
      Function.Injective a → Function.Exact a b → Function.Surjective b →
      ∃ (E : Type (max w y)) (_ : AddCommGroup E) (_ : Module R E)
        (i : N →ₗ[R] E) (q : E →ₗ[R] C j),
        Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
        ∃ θ : S ⊗[R] E ≃ₗ[S] T,
          θ.toLinearMap.comp (i.baseChange S) = a ∧
          b.comp θ.toLinearMap = q.baseChange S)
    {T : Type z} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (⨁ j, C j))
    (ha : Function.Injective a) (hab : Function.Exact a b)
    (hb : Function.Surjective b) :
    ∃ (E : Type (max w x y)) (_ : AddCommGroup E) (_ : Module R E)
      (i : N →ₗ[R] E) (q : E →ₗ[R] (⨁ j, C j)),
      Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (i.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S := by
  classical
  have hmodels : ∀ j, ∃ (E : Type (max w y)) (_ : AddCommGroup E) (_ : Module R E)
      (i : N →ₗ[R] E) (q : E →ₗ[R] C j),
      Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
      ∃ k : S ⊗[R] E →ₗ[S] T,
        k.comp (i.baseChange S) = a ∧
        b.comp k = ((DirectSum.lof R J C j).baseChange S).comp (q.baseChange S) := by
    intro j
    let f := (DirectSum.lof R J C j).baseChange S
    let r := (DirectSum.component R J C j).baseChange S
    have hrf : r.comp f = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, DirectSum.component_comp_lof_same]
      exact LinearMap.baseChange_id
    have hrf_apply (c : S ⊗[R] C j) : r (f c) = c :=
      DFunLike.congr_fun hrf c
    let P : Submodule S T := f.range.comap b
    have hP (t : P) : f (r (b t)) = b t := by
      obtain ⟨c, hc⟩ := t.property
      rw [← hc, hrf_apply]
    let aj : S ⊗[R] N →ₗ[S] P := a.codRestrict P (by
      intro n
      change b (a n) ∈ f.range
      rw [hab.apply_apply_eq_zero]
      exact Submodule.zero_mem _)
    let bj : P →ₗ[S] S ⊗[R] C j := r.comp (b.comp P.subtype)
    have haj : Function.Injective aj := by
      intro n n' h
      exact ha (congrArg Subtype.val h)
    have habj : Function.Exact aj bj := by
      intro t
      constructor
      · intro ht
        have hbt : b t = 0 := by
          rw [← hP t]
          change f (bj t) = 0
          rw [ht, map_zero]
        obtain ⟨n, hn⟩ := (hab t).mp hbt
        exact ⟨n, Subtype.ext hn⟩
      · rintro ⟨n, rfl⟩
        change r (b (a n)) = 0
        rw [hab.apply_apply_eq_zero, map_zero]
    have hbj : Function.Surjective bj := by
      intro c
      obtain ⟨t, ht⟩ := hb (f c)
      refine ⟨⟨t, ?_⟩, ?_⟩
      · change b t ∈ f.range
        exact ⟨c, ht.symm⟩
      · change r (b t) = c
        rw [ht, hrf_apply]
    obtain ⟨E, hAdd, hMod, i, q, hi, hiq, hq, θ, hθi, hθq⟩ :=
      hC j P aj bj haj habj hbj
    let k : S ⊗[R] E →ₗ[S] T := P.subtype.comp θ.toLinearMap
    refine ⟨E, hAdd, hMod, i, q, hi, hiq, hq, k, ?_, ?_⟩
    · change P.subtype.comp (θ.toLinearMap.comp (i.baseChange S)) = a
      rw [hθi]
      rfl
    · apply LinearMap.ext
      intro e
      change b (θ e) = f ((q.baseChange S) e)
      rw [← hP (θ e)]
      congr 1
      exact DFunLike.congr_fun hθq e
  choose E hAdd hMod i q hi hiq hq k hki hkq using hmodels
  let : ∀ j, AddCommGroup (E j) := hAdd
  let : ∀ j, Module R (E j) := hMod
  obtain ⟨F, hFAdd, hFMod, iF, qF, hiF, hiqF, hqF, hpull⟩ :=
    (extOne_directSum_bijective.{u, w, x, y, max w y, max w x y} (R := R) (N := N) C).1 E i q
      (fun j ↦ ⟨hi j, hiq j, hq j⟩)
  refine ⟨F, hFAdd, hFMod, iF, qF, hiF, hiqF, hqF, ?_⟩
  choose h hhi hhq using hpull
  let f : ∀ j, E j →ₗ[R] F := fun j ↦
    (LinearMap.fst R F (C j)).comp
      ((LinearMap.ker (qF ∘ₗ LinearMap.fst R F (C j) -
        DirectSum.lof R J C j ∘ₗ LinearMap.snd R F (C j))).subtype.comp
          (h j).symm.toLinearMap)
  have hfi : ∀ j n, f j (i j n) = iF n := by
    intro j n
    have hn : (iF n, 0) ∈ LinearMap.ker (qF ∘ₗ LinearMap.fst R F (C j) -
        DirectSum.lof R J C j ∘ₗ LinearMap.snd R F (C j)) := by
      simp [hiqF.apply_apply_eq_zero]
    have hh : (h j).symm (i j n) = ⟨(iF n, 0), hn⟩ := by
      rw [← hhi j n hn, LinearEquiv.symm_apply_apply]
    change ((h j).symm (i j n) : F × C j).1 = iF n
    rw [hh]
  have hfq : ∀ j e, qF (f j e) = DirectSum.lof R J C j (q j e) := by
    intro j e
    let p := (h j).symm e
    have hp := p.property
    change qF (p : F × C j).1 - DirectSum.lof R J C j (p : F × C j).2 = 0 at hp
    have hq := hhq j p
    simp only [p, LinearEquiv.apply_symm_apply] at hq
    change qF (p : F × C j).1 = DirectSum.lof R J C j (q j e)
    rw [sub_eq_zero.mp hp, hq]
  let : Module R T := Module.compHom T (algebraMap R S)
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let a0 : N →ₗ[R] T := (a.restrictScalars R).comp (TensorProduct.mk R S N 1)
  let t : ∀ j, E j →ₗ[R] T := fun j ↦
    ((k j).restrictScalars R).comp (TensorProduct.mk R S (E j) 1)
  have hti : ∀ j n, t j (i j n) = a0 n := by
    intro j n
    simpa [t, a0] using DFunLike.congr_fun (hki j) (1 ⊗ₜ[R] n)
  obtain ⟨g0, hgi0, hgf0⟩ := glue_extension_maps C E iF qF hiF hiqF a0 i q
    (fun j ↦ ⟨hiq j, hq j⟩) f t hfi hfq hti
  let g : S ⊗[R] F →ₗ[S] T := TensorProduct.AlgebraTensorModule.lift
    (LinearMap.smulRight (LinearMap.id : S →ₗ[S] S) g0)
  have hg (s : S) (e : F) : g (s ⊗ₜ[R] e) = s • g0 e := rfl
  have hgi : g.comp (iF.baseChange S) = a := by
    ext n
    simp [hg, hgi0, a0]
  have hb0 : (b.restrictScalars R).comp g0 =
      (TensorProduct.mk R S (⨁ j, C j) 1).comp qF := by
    apply extension_map_ext C E iF qF hiqF q hq f hfq
    · intro n
      simp [hgi0, a0, hab.apply_apply_eq_zero, hiqF.apply_apply_eq_zero]
    · intro j e
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, hgf0, hfq]
      change b (k j (1 ⊗ₜ[R] e)) = 1 ⊗ₜ[R] DirectSum.lof R J C j (q j e)
      simpa using DFunLike.congr_fun (hkq j) (1 ⊗ₜ[R] e)
  have hbg : b.comp g = qF.baseChange S := by
    ext e
    simpa [hg] using DFunLike.congr_fun hb0 e
  let : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hflat
  have hex : Function.Exact (iF.baseChange S) (qF.baseChange S) := by
    change Function.Exact (iF.lTensor S) (qF.lTensor S)
    exact Module.Flat.lTensor_exact S hiqF
  have hsur : Function.Surjective (qF.baseChange S) := by
    change Function.Surjective (qF.lTensor S)
    exact LinearMap.lTensor_surjective S hqF
  have hginj : Function.Injective g := by
    intro x y hxy
    have hz : g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hqz : qF.baseChange S (x - y) = 0 := by
      rw [← hbg, LinearMap.comp_apply, hz, map_zero]
    obtain ⟨n, hn⟩ := (hex _).mp hqz
    have han : a n = 0 := by
      rw [← hgi, LinearMap.comp_apply, hn, hz]
    have hn0 : n = 0 := ha (han.trans (map_zero a).symm)
    have hsub : x - y = 0 := by rw [← hn, hn0, map_zero]
    exact sub_eq_zero.mp hsub
  have hgsur : Function.Surjective g := by
    intro t'
    obtain ⟨x, hx⟩ := hsur (b t')
    have ht : b (t' - g x) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hbg, hx, sub_self]
    obtain ⟨n, hn⟩ := (hab _).mp ht
    refine ⟨x + iF.baseChange S n, ?_⟩
    have hgin : g (iF.baseChange S n) = a n := DFunLike.congr_fun hgi n
    rw [map_add, hgin, hn]
    simpa only [add_comm] using sub_add_cancel t' (g x)
  exact ⟨LinearEquiv.ofBijective g ⟨hginj, hgsur⟩, hgi, hbg⟩

end LinearMap
