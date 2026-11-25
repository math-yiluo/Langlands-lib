/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Flat.Tensor
import WeilConjectures.RingTheory.TensorTowerKernelProZero
import WeilConjectures.RingTheory.TensorLimitOfProZeroKernels

/-!
# Inverse limits of flat modules over ideal-power quotients

Source: Stacks Project, More on Algebra, Lemma Tag 0912 (lemma-limit-flat).
(blueprint: lem-weil-pbc-limit-flat-modules)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- An inverse system of flat `A / Iⁿ`-modules with surjective transitions has flat limit,
and tensoring with a finite module commutes with this limit.
Source: Stacks Project, More on Algebra, Lemma Tag 0912 (lemma-limit-flat).
(blueprint: lem-weil-pbc-limit-flat-modules)

The object `F.obj (op n)` denotes `M_{n+1}`. The quotient module structures, together
with `IsScalarTower`, say that the given `A`-action factors through `A / I^(n+1)`;
in particular `I^(n+1)` annihilates this object. The tensor comparison is stated as
injectivity into the product and surjectivity onto its compatible sequences. Its
`n`-th component is `1 ⊗ limit.π F (op n)`.

Proof, using a presentation-level version of the argument of Tag 0912:
1. Artin--Rees and flatness over the quotients show that tensor kernels of finite
   submodule inclusions are eventually killed by tower transitions. This is
   `tensor_kernel_eventually_zero_of_flat_quotients`, which needs no surjectivity.
2. The general `tensor_limit_comparison_of_proZero_kernels` uses these kernels,
   finite free presentations, recursive lifting and Mittag--Leffler fibres to prove
   the canonical tensor comparison. It applies to every finite `Q`, with independent
   universes for the ring, the tower, and `Q`.
3. Apply the finitely generated ideal criterion for flatness. If `y ∈ J ⊗ lim F`
   is killed by the inclusion into `A ⊗ lim F`, tensor naturality puts each
   coordinate in the corresponding tensor kernel. For each n, choose a later m
   whose transition kills that kernel. Compatibility of the limit projections
   then makes the n-th coordinate zero. Injectivity of the comparison for `J`
   gives `y = 0`, proving flatness. -/
theorem limit_flat_of_flat_quotients
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    [∀ n : ℕ, Module (A ⧸ I ^ (n + 1)) (F.obj (op n))]
    [∀ n : ℕ, IsScalarTower A (A ⧸ I ^ (n + 1)) (F.obj (op n))]
    (hflat : ∀ n : ℕ, Module.Flat (A ⧸ I ^ (n + 1)) (F.obj (op n)))
    (hsurj : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) :
    Module.Flat A (limit F : ModuleCat.{v} A) ∧
      ∀ (Q : Type w) [AddCommGroup Q] [Module A Q] [Module.Finite A Q],
        Function.Injective (LinearMap.pi fun n : ℕ ↦ (limit.π F (op n)).hom.lTensor Q) ∧
          ∀ x : ∀ n : ℕ, TensorProduct A Q (F.obj (op n)),
            (∀ n : ℕ, (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor Q (x (n + 1))
              = x n) →
            ∃ y : TensorProduct A Q (limit F : ModuleCat.{v} A),
              ∀ n : ℕ, (limit.π F (op n)).hom.lTensor Q y = x n := by
  have hker := tensor_kernel_eventually_zero_of_flat_quotients A I F hflat
  refine ⟨?_, tensor_limit_comparison_of_proZero_kernels A F hsurj hker⟩
  apply Module.Flat.iff_rTensor_injective.mpr
  intro J hJ
  let : Module.Finite A J := Module.Finite.iff_fg.mpr hJ
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  apply (tensor_limit_comparison_of_proZero_kernels A F hsurj hker J).1
  ext n
  obtain ⟨m, hnm, hm⟩ := hker A J n
  have hnat : J.subtype.rTensor (F.obj (op m))
      ((limit.π F (op m)).hom.lTensor J y) =
      (limit.π F (op m)).hom.lTensor A (J.subtype.rTensor (limit F : ModuleCat.{v} A) y) := by
    clear hy
    induction y using TensorProduct.inductionOn with
    | tmul j t => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hz := hm ((limit.π F (op m)).hom.lTensor J y) (by rw [hnat, hy, map_zero])
  have hw : (F.map (homOfLE hnm).op).hom.comp (limit.π F (op m)).hom =
      (limit.π F (op n)).hom := by
    exact congrArg ModuleCat.Hom.hom (limit.w F (homOfLE hnm).op)
  simpa only [← LinearMap.lTensor_comp_apply, hw, LinearMap.pi_apply,
    LinearMap.zero_apply, map_zero] using hz

end ModuleCat
