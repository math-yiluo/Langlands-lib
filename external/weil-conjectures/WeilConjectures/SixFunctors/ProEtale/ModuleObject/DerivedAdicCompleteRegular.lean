/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdicCompleteHomology
public import WeilConjectures.CategoryTheory.Sites.DerivedAdicComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.Topology.ContinuousMapAdicTower

/-!
# Finitely presented `𝒪_{E,V}`-modules are derived complete

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `V` a scheme.

- The sections of `𝒪_{E,V}` over `W ∈ V_proét` are the continuous maps `W → 𝒪_E` (Bhatt–Scholze,
  Lemma 4.2.12, `ProEtale.isIso_continuousMapComparison`), and on `C(W, 𝒪_E)^ℕ` the map
  `(xᵢ) ↦ (xᵢ - ℓ xᵢ₊₁)` is bijective (`ContinuousMap.bijective_sub_zsmul_succ`). Hence the
  regular module `𝒪_{E,V}` is derived `ℓ`-adically complete
  (`ProEtale.isDerivedAdicComplete_regular_padicIntegers`).
- Derived complete objects of an abelian category with exact countable products are stable
  under finite direct sums and cokernels (`CategoryTheory.IsDerivedAdicComplete.biproduct`,
  `DerivedCategory.isDerivedAdicComplete_cokernel`), so every finitely presented
  `𝒪_{E,V}`-module is derived `ℓ`-adically complete
  (`ProEtale.isDerivedAdicComplete_of_isFinitelyPresented`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

section

variable {X : Scheme.{u}} (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- A module object over `Λ_X` is derived `n`-adically complete if its underlying abelian sheaf
is. -/
lemma isDerivedAdicComplete_of_isDerivedAdicComplete_X {n : ℤ}
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsDerivedAdicComplete n M.X) : IsDerivedAdicComplete n M :=
  IsDerivedAdicComplete.of_map (fun _ : Unit ↦ Mod.forget (condensedRingObj Λ X))
    (fun f hf ↦ have := hf (); isIso_of_reflects_iso f (Mod.forget _)) fun _ ↦ h

end

/-- Let `T` be a complete normed commutative ring all of whose elements have norm `≤ 1`, and
`n : ℤ` with `‖(n : T)‖ < 1`. Then the sheaf `C(-, T)` on `X_proét` is derived `n`-adically
complete: on sections over `W`, the map `(xᵢ) ↦ (xᵢ - n xᵢ₊₁)` of `C(W, T)^ℕ` is bijective. -/
lemma isDerivedAdicComplete_continuousMapRingSheaf (X : Scheme.{u}) (T : Type)
    [NormedCommRing T] [CompleteSpace T] (n : ℤ) (hn : ‖(n : T)‖ < 1) (hT : ∀ x : T, ‖x‖ ≤ 1) :
    IsDerivedAdicComplete n ((sheafCompose (ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)) := by
  refine Sheaf.isDerivedAdicComplete_of_forall _ fun U ↦ ?_
  rw [AddCommGrpCat.isDerivedAdicComplete_iff_bijective]
  let e : (ℕ → ULift.{u + 1} C(U.unop.left, T)) ≃ (ℕ → C(U.unop.left, T)) :=
    Equiv.piCongrRight fun _ ↦ Equiv.ulift
  have h := ContinuousMap.bijective_sub_zsmul_succ (W := U.unop.left) n hn hT
  rw [← e.symm.comp_bijective, ← e.bijective_comp] at h
  exact h

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The elements of the ring of integers `𝒪_E` have norm `≤ 1`. -/
lemma norm_integers_le_one :
    letI := normedFieldOfAlgebra ℓ E.1
    ∀ x : integers ℓ E.1, ‖x‖ ≤ 1 := by
  let := normedFieldOfAlgebra ℓ E.1
  intro x
  have := (mem_integers_iff ℓ E.1 x).1 x.2
  rwa [← NNReal.coe_le_coe, coe_nnnorm] at this

/-- The prime `ℓ` has norm `< 1` in the ring of integers `𝒪_E`. -/
lemma norm_prime_integers_lt_one :
    letI := normedFieldOfAlgebra ℓ E.1
    ‖((ℓ : ℤ) : integers ℓ E.1)‖ < 1 := by
  let := normedFieldOfAlgebra ℓ E.1
  have h : ‖((ℓ : ℤ) : integers ℓ E.1)‖ = ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (ℓ : ℚ_[ℓ])‖ := by
    rw [map_natCast]
    rfl
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

/-- **The regular module `𝒪_{E,V}` is derived `ℓ`-adically complete.** -/
lemma isDerivedAdicComplete_regular_padicIntegers (V : Scheme.{u}) :
    IsDerivedAdicComplete (ℓ : ℤ)
      (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) V)) := by
  let := normedFieldOfAlgebra ℓ E.1
  have := compactSpace_integers ℓ E.1
  have : CompleteSpace (integers ℓ E.1) := complete_of_compact
  refine isDerivedAdicComplete_of_isDerivedAdicComplete_X _ _ ?_
  exact (isDerivedAdicComplete_continuousMapRingSheaf V (integers ℓ E.1) ℓ
    (norm_prime_integers_lt_one ℓ E) (norm_integers_le_one ℓ E)).of_iso
      (asIso (continuousMapComparison V (integers ℓ E.1))).symm

/-- **Finitely presented `𝒪_{E,V}`-modules are derived `ℓ`-adically complete**: they are
cokernels of morphisms of finite free modules. -/
theorem isDerivedAdicComplete_of_isFinitelyPresented {V : Scheme.{u}}
    (N : Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) V))
    (hN : Mod.IsFinitelyPresented _ N) : IsDerivedAdicComplete (ℓ : ℤ) N := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := hN
  have hfree (k : ℕ) : IsDerivedAdicComplete (ℓ : ℤ) (Mod.finiteFree _ k) :=
    IsDerivedAdicComplete.biproduct _ fun _ ↦ isDerivedAdicComplete_regular_padicIntegers ℓ E V
  exact (DerivedCategory.isDerivedAdicComplete_cokernel f (hfree m) (hfree n)).of_iso i.symm

end AlgebraicGeometry.ProEtale
