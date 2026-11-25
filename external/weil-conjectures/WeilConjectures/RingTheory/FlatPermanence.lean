/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness descends through a faithfully flat module

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 039V (lemma-flat-permanence),
line 8958 (blueprint: lem-weil-pbc-flat-permanence).
-/

@[expose] public section

universe u v w

/--
Let `φ : R →+* S` be a homomorphism of commutative rings and `M` an `S`-module,
viewed as an `R`-module by restriction of scalars along `φ`.  If `M` is flat over `R` and faithfully
flat over `S`, then `φ` is flat. Source: Stacks Project, Algebra, Lemma 039V
(blueprint: lem-weil-pbc-flat-permanence).

Proof:
1. For an injective `R`-linear map `u : N₁ → N₂`, flatness of `φ` reduces to
   injectivity of `u ⊗ 1_S`, equivalently `1_S ⊗ u` by tensor symmetry
   (def-weil-pbc-flat-ring-map).
2. Flatness of `M` over `R` makes `u ⊗ 1_M` injective, hence also `1_M ⊗ u`
   by tensor symmetry (def-weil-pbc-flat-ring-map).
3. The natural cancellation isomorphisms `M ⊗[S] (S ⊗[R] Nᵢ) ≃ M ⊗[R] Nᵢ`
   identify tensoring `1_S ⊗ u` with the injective map of step 2
   (lem-weil-pbc-module-tensor-cancel-base-change).
4. Faithful flatness over `S` reflects exactness of the complex starting at zero,
   so `1_S ⊗ u` is injective (def-weil-pbc-faithfully-flat-ring-map). Step 1 concludes.
-/
theorem RingHom.flat_of_flat_module_of_faithfullyFlat_module
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S)
    [AddCommGroup M] [Module S M] [Module.FaithfullyFlat S M]
    (hM : letI := Module.compHom M φ; Module.Flat R M) :
    RingHom.Flat φ := by
  let : Algebra R S := φ.toAlgebra
  let : Module R M := Module.compHom M φ
  have : IsScalarTower R S M :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ rfl
  have hM' : Module.Flat R M := hM
  rw [RingHom.Flat]
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let g : TensorProduct R S N →ₗ[S] TensorProduct R S P :=
    TensorProduct.AlgebraTensorModule.lTensor S S f
  have hfg : Function.Injective (LinearMap.lTensor M f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  let cN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N
  let cP := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M P
  have hcomp : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor S M f ∘ₗ cN.toLinearMap) := by
    intro x y hxy
    apply cN.injective
    apply hfg
    exact hxy
  have hnat : TensorProduct.AlgebraTensorModule.lTensor S M f ∘ₗ cN.toLinearMap =
      cP.toLinearMap ∘ₗ LinearMap.lTensor M g := by
    ext m s
    simp [cN, cP, g]
  rw [hnat] at hcomp
  have hB : Function.Injective (LinearMap.lTensor M g) := by
    intro x y hxy
    apply hcomp
    exact congrArg (fun z ↦ cP.toLinearMap z) hxy
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective S M g).mp hB
