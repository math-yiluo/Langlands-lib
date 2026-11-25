/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

/-!

# Morphisms into derived complete complexes are `ℓ`-adically separated

Let `L` be a derived complete complex of `𝒪_{E,X}`-module objects
(`ProEtale.derivedCompleteIntegers`) and `K` a complex such that the groups
`Hom(K⟦1⟧, Res_n (red_n L))` are finite (e.g. bounded constructible complexes on a scheme of
finite type over a separably closed field). A morphism `f : K ⟶ L` divisible by every power of
`ℓ` is zero (`ProEtale.eq_zero_of_forall_exists_eq_pow_zsmul`): its composite with the unit
`L ⟶ Res_n (red_n L)` factors through `ℓⁿ • 𝟙 L`, which vanishes on the reduction triangle, and
morphisms into `L` are determined by these composites (`ProEtale.eq_of_comp_unit_eq`).

This is the input that makes the action of the pro-`p` kernel `P'` on integral nearby cycles
trivial once it is trivial modulo `ℓ` (SGA 4½, [Th. finitude], §3.7;
`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished_of_separated`).

-/

@[expose] public section

universe u

open CategoryTheory Category Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

open scoped CategoryTheory.Obj

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] {X : Scheme.{u}}

/-- **`ℓ`-adic separatedness of morphisms into a derived complete complex**: a morphism into a
derived complete complex which is divisible by every power of `ℓ` is zero, when the groups
`Hom(K⟦1⟧, Res_n (red_n L))` are finite. -/
theorem eq_zero_of_forall_exists_eq_pow_zsmul
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    [∀ n : ℕ, Finite (K⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))]
    {f : K ⟶ L} (hf : ∀ m : ℕ, ∃ g : K ⟶ L, f = ((ℓ : ℤ) ^ m) • g) : f = 0 := by
  refine eq_of_comp_unit_eq hL fun n ↦ ?_
  obtain ⟨g, rfl⟩ := hf (n + 1)
  have h : (((ℓ : ℤ) ^ (n + 1)) • 𝟙 L) ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E (n + 1))).unit.app L = 0 :=
    comp_distTriang_mor_zero₁₂ _ (integersModPowReduction_distinguished ℓ E (n + 1) L)
  rw [Limits.zero_comp]
  calc _ = g ≫ ((((ℓ : ℤ) ^ (n + 1)) • 𝟙 L) ≫
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowReduction X ℓ E (n + 1))).unit.app L) := by
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp]
    _ = 0 := by rw [h, Limits.comp_zero]

end AlgebraicGeometry.ProEtale
