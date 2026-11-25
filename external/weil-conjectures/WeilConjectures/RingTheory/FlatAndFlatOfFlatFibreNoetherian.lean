/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.FlatPermanence
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Nakayama
import WeilConjectures.Mathlib.RingTheory.Filtration

/-!
# The Noetherian fibre criterion for flatness

Source: Stacks Project, Algebra, Tag 00MP, lemma-criterion-flatness-fibre-Noetherian
(blueprint: lem-weil-pbc-criterion-flatness-fibre-noetherian).
-/

@[expose] public section

open scoped TensorProduct
set_option autoImplicit false
universe u v w z

namespace Module

/-- The Noetherian fibre criterion, Stacks Project, Algebra, Tag 00MP
(blueprint: lem-weil-pbc-criterion-flatness-fibre-noetherian).

The scalar towers express restriction along the local maps `R → S → S'`.
The tensor fibre is canonically isomorphic to `M / mM`, not definitionally equal to it.

Proof following the seven steps of the node:
1. Put `I = mS`. Locality gives `I ⊆ m_S`, so `I` is proper. Scalar compatibility
   gives `IM = mM`, and hence the fibre hypothesis says `M/IM` is flat over `S/I`.
2. The map `m ⊗[R] M → I ⊗[S] M`, sending `a ⊗ x` to `φ(a) ⊗ x`, is surjective:
   write `b ∈ I` as a sum of `φ(a_j)s_j`, and move each `s_j` onto the module factor.
   Its composite with multiplication `I ⊗[S] M → M` is multiplication over `R`.
3. Flatness over `R` makes `m ⊗[R] M → M` injective. The surjection of step 2
   therefore makes `I ⊗[S] M → M` injective (Tag 00M6 identifies its kernel with Tor).
4. Apply `lem-weil-pbc-flat-variant-local-criterion` (Tag 00ML) to `S → S'`,
   the proper ideal `I`, finite `M`, step 3 and fibre flatness. Thus `M` is flat over `S`.
5. By `lem-weil-pbc-nakayama-jacobson` (Tag 00DV), finiteness and nonzero `M` give
   `m_{S'}M ≠ M`. Locality gives `m_S M ⊆ m_{S'}M`, hence `M/m_S M ≠ 0`.
6. By `lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals` (Tag 00HP), step 4
   and step 5 make `M` faithfully flat over `S`.
7. Apply `lem-weil-pbc-flat-permanence` (Tag 039V) to `M`, flat over `R` and
   faithfully flat over `S`, to deduce that `S` is flat over `R`. This is the node's
   descent version of the second paragraph of Tag 00MP. Together with step 4 it
   gives both conclusions.
-/
theorem flat_and_flat_of_flat_fibre_noetherian
    (R : Type u) (S : Type v) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    [Module.Finite S' M] [Nontrivial M]
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M))
    [Module.Flat R M] : Module.Flat R S ∧ Module.Flat S M := by
  let I : Ideal S := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)
  have hI : Ideal.map (algebraMap S S') I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact (Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (algebraMap R S))).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap S S'))
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  let e' : ((S ⧸ I) ⊗[S] M) ≃ₗ[S ⧸ I] (M ⧸ I • (⊤ : Submodule S M)) :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change e ((algebraMap S (S ⧸ I)) a • x) =
          (algebraMap S (S ⧸ I)) a • e x
        simpa only [IsScalarTower.algebraMap_smul] using e.map_smul a x }
  have : Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M) := h_fibre
  have : Module.Flat (S ⧸ I) (M ⧸ I • (⊤ : Submodule S M)) :=
    Module.Flat.of_linearEquiv e'.symm
  have hinj : Function.Injective (I.subtype.lTensor M) := by
    classical
    let J := IsLocalRing.maximalIdeal R
    let f : J →ₛₗ[algebraMap R S] I :=
      { toFun := fun a => ⟨algebraMap R S a, Ideal.mem_map_of_mem _ a.property⟩
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp [map_mul, Algebra.smul_def] }
    let g : M →ₛₗ[algebraMap R S] M :=
      { toFun := id
        map_add' := by intros; rfl
        map_smul' := by intros; simp }
    let a := TensorProduct.map g f
    have ha : Function.Surjective a := by
      have hgen : ∀ b ∈ I, ∀ (hb : b ∈ I) (x : M),
          ∃ z, a z = x ⊗ₜ[S] (⟨b, hb⟩ : I) := by
        intro b hb
        change b ∈ Submodule.span S (algebraMap R S '' (J : Set R)) at hb
        induction hb using Submodule.span_induction with
        | mem b hb =>
          obtain ⟨r, hr, rfl⟩ := hb
          intro hb x
          exact ⟨x ⊗ₜ[R] (⟨r, hr⟩ : J), rfl⟩
        | zero =>
          intro hb x
          exact ⟨0, by change a 0 = x ⊗ₜ[S] (0 : I); simp⟩
        | add b c hb hc ihb ihc =>
          intro hbc x
          obtain ⟨y, hy⟩ := ihb hb x
          obtain ⟨z, hz⟩ := ihc hc x
          exact ⟨y + z, by simpa [map_add, hy, hz] using
            (TensorProduct.tmul_add x (⟨b, hb⟩ : I) (⟨c, hc⟩ : I)).symm⟩
        | smul r b hb ih =>
          intro hrb x
          obtain ⟨z, hz⟩ := ih hb (r • x)
          refine ⟨z, ?_⟩
          change a z = x ⊗ₜ[S] (r • (⟨b, hb⟩ : I))
          rw [← TensorProduct.smul_tmul]
          exact hz
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul x b => exact hgen b b.property b.property x
      | add y z hy hz =>
        obtain ⟨y, rfl⟩ := hy
        obtain ⟨z, rfl⟩ := hz
        exact ⟨y + z, map_add a y z⟩
    let muR := (TensorProduct.rid R M).toLinearMap ∘ₗ J.subtype.lTensor M
    let muS := (TensorProduct.rid S M).toLinearMap ∘ₗ I.subtype.lTensor M
    have hR : Function.Injective muR :=
      (TensorProduct.rid R M).injective.comp
        (Module.Flat.lTensor_preserves_injective_linearMap J.subtype Subtype.val_injective)
    have hcomm : ∀ z, muS (a z) = muR z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x b => simp [muS, muR, a, f, g]
      | add x y hx hy => simp [map_add, hx, hy]
    intro x y hxy
    obtain ⟨x, rfl⟩ := ha x
    obtain ⟨y, rfl⟩ := ha y
    apply congrArg a
    apply hR
    rw [← hcomm, ← hcomm]
    exact congrArg (TensorProduct.rid S M) hxy
  have hSM : Module.Flat S M :=
    Module.Flat.of_flat_quotient_of_lTensor_injective (S := S') I hI
      hinj
  have hne : (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S M) ≠ ⊤ := by
    intro h
    have hle : (⊤ : Submodule S' M) ≤
        (IsLocalRing.maximalIdeal S') • (⊤ : Submodule S' M) := by
      intro x hx
      have hx' : x ∈ (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S M) := by rw [h]; trivial
      have hres := Submodule.restrictScalars_map_smul_eq
        (IsLocalRing.maximalIdeal S) (⊤ : Submodule S' M)
      rw [Submodule.restrictScalars_top] at hres
      rw [← hres] at hx'
      exact Submodule.smul_mono
        (IsLocalRing.map_maximalIdeal_le (algebraMap S S')) le_rfl hx'
    exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal S') ⊤ Module.Finite.fg_top hle
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]))
  have : Module.FaithfullyFlat S M :=
    { hSM with
      submodule_ne_top := fun m hm => by
        have hm' : m = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hm
        simpa [hm'] using hne }
  have hcomp : letI := Module.compHom M (algebraMap R S); Module.Flat R M := by
    have heq : Module.compHom M (algebraMap R S) = ‹Module R M› := by
      apply Module.ext
      funext r x
      exact IsScalarTower.algebraMap_smul S r x
    change @Module.Flat R M _ _ (Module.compHom M (algebraMap R S))
    rw [heq]
    infer_instance
  have hRS := RingHom.flat_of_flat_module_of_faithfullyFlat_module
    (M := M) (algebraMap R S) hcomp
  exact ⟨(RingHom.flat_algebraMap_iff).mp hRS, hSM⟩

end Module
