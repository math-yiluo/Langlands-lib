/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.CompletionRestrictionFlatQuotients
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.Flat.FlatModulePowers

/-!
# Flatness of completion along a flat local map

Source: Stacks Project, More on Algebra, Lemma 0C4G (more-algebra-lemma-flat-completion),
line 10731, the implication from flatness of a local map to flatness of its completions
(blueprint: lem-weil-pbc-flat-completion).
-/

@[expose] public section

universe u v

/-- A flat local homomorphism of Noetherian local rings induces a flat homomorphism
on adic completions.

The map is characterized levelwise by the maps on quotients, and by compatibility
with the canonical maps.  Source: Stacks Project, More on Algebra, Lemma 0C4G,
line 10731 (blueprint: lem-weil-pbc-flat-completion).

Proof:
1. The canonical map from B to its completion is flat by
   `lem-weil-pbc-noetherian-completion-flat`. Compose it with the flat map φ using
   `lem-weil-pbc-flat-ring-map-comp` to make Bhat a flat A-module.
2. For every positive n, `lem-weil-pbc-flat-module-quotient-flat` makes
   Bhat / mA ^ n Bhat flat over A / mA ^ n.
3. By `lem-weil-pbc-local-completion-local-ring`, Ahat has maximal ideal mA Ahat,
   whose nth power is mA ^ n Ahat. By `lem-weil-pbc-adic-completion-mod-power`,
   the canonical map identifies A / mA ^ n with Ahat / (mA Ahat) ^ n;
   finite generation follows from `def-weil-pbc-noetherian-ring`.
4. The identity φhat.comp ιA = ιB.comp φ identifies (mA Ahat) ^ n Bhat with
   mA ^ n Bhat and their quotient module structures. Transport the flatness
   from step 2 along the ring isomorphism of step 3.
5. Both completions are Noetherian by `lem-weil-pbc-adic-completion-noetherian`.
   By `lem-weil-pbc-local-completion-local-ring`, Bhat is local with maximal
   ideal mB Bhat; locality of φ puts mA Bhat inside it. Bhat is finite over
   itself. Apply `theorem-finite-etale-covers-proper-henselian--2` with R = Ahat, I = mA Ahat,
   S = Bhat and M = S to conclude φhat.Flat (`def-weil-pbc-flat-ring-map`).
-/
theorem flat_adicCompletion_of_flat_local
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (hlocal : ∀ x : A, x ∈ IsLocalRing.maximalIdeal A →
      φ x ∈ IsLocalRing.maximalIdeal B) :
    let mA : Ideal A := IsLocalRing.maximalIdeal A
    let mB : Ideal B := IsLocalRing.maximalIdeal B
    let Ahat := AdicCompletion mA A
    let Bhat := AdicCompletion mB B
    let ιA : A →+* Ahat := algebraMap A Ahat
    let ιB : B →+* Bhat := algebraMap B Bhat
    ∃ φhat : Ahat →+* Bhat,
      (∀ n : ℕ,
        ((AdicCompletion.evalₐ mB n).toRingHom).comp φhat =
          (Ideal.Quotient.lift (mA ^ n)
            ((Ideal.Quotient.mk (mB ^ n)).comp φ) (by
              intro x hx
              change Ideal.Quotient.mk (mB ^ n) (φ x) = 0
              rw [Ideal.Quotient.eq_zero_iff_mem]
              exact (pow_le_pow_left' ((Ideal.map_le_iff_le_comap).2 (by
                intro y hy
                exact hlocal y hy)) n) (by
                  rw [← Ideal.map_pow]
                  exact Ideal.mem_map_of_mem φ hx)) ).comp
            (AdicCompletion.evalₐ mA n).toRingHom) ∧
      φhat.comp ιA = ιB.comp φ ∧ φhat.Flat := by
  dsimp only
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  have hmap : mA.map φ ≤ mB := Ideal.map_le_iff_le_comap.mpr hlocal
  have hpow (n : ℕ) : (mA ^ n).map φ ≤ mB ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmap n
  let qmap (n : ℕ) : A ⧸ mA ^ n →+* B ⧸ mB ^ n :=
    Ideal.Quotient.lift (mA ^ n) ((Ideal.Quotient.mk (mB ^ n)).comp φ) (by
      intro x hx
      change Ideal.Quotient.mk (mB ^ n) (φ x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hpow n (Ideal.mem_map_of_mem φ hx))
  let f (n : ℕ) := (qmap n).comp (AdicCompletion.evalₐ mA n).toRingHom
  have hf {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow mB hmn).comp (f n) = f m := by
    ext x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simpa [f, qmap] using congrArg (qmap m) (AdicCompletion.Ideal.mk_eq_mk mA hmn x)
  let φhat := AdicCompletion.liftRingHom mB f (fun hmn ↦ hf hmn)
  have heval (n : ℕ) : (AdicCompletion.evalₐ mB n).toRingHom.comp φhat = f n :=
    AdicCompletion.evalₐ_comp_liftRingHom mB f (fun hmn ↦ hf hmn) n
  have hcomp : φhat.comp (algebraMap A (AdicCompletion mA A)) =
      (algebraMap B (AdicCompletion mB B)).comp φ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    simpa [f, qmap, AdicCompletion.algebraMap_apply] using
      RingHom.congr_fun (heval n) ((algebraMap A (AdicCompletion mA A)) x)
  refine ⟨φhat, heval, hcomp, ?_⟩
  let : Algebra (AdicCompletion mA A) (AdicCompletion mB B) := φhat.toAlgebra
  let := AdicCompletion.isNoetherianRing mA
  let := AdicCompletion.isNoetherianRing mB
  have hflatB : (algebraMap B (AdicCompletion mB B)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflatA : (φhat.comp (algebraMap A (AdicCompletion mA A))).Flat := by
    rw [hcomp]
    exact hφ.comp hflatB
  have hquot := AdicCompletion.flat_quotients_of_flat_restriction mA
    (IsNoetherian.noetherian mA) φhat hflatA
  have hmax : (mA.map (algebraMap A (AdicCompletion mA A))).map
      (algebraMap (AdicCompletion mA A) (AdicCompletion mB B)) ≤
      IsLocalRing.maximalIdeal (AdicCompletion mB B) := by
    rw [Ideal.map_map, φhat.algebraMap_toAlgebra, hcomp,
      ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_mono hmap
  change Module.Flat (AdicCompletion mA A) (AdicCompletion mB B)
  exact (Module.Flat.flat_of_flat_quotients_powers
    (M := AdicCompletion mB B) (mA.map (algebraMap A (AdicCompletion mA A)))
    (fun n _ ↦ hquot n)).2 hmax
