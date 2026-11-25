/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Algebraic.Defs
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.IsN1AdjoinSingleton
import WeilConjectures.RingTheory.NagataDomainN2
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Algebraic monogenic extensions of Nagata domains are Japanese

Source: Stacks Project, Algebra, Proposition Tag 0334, claim (**) and Step 4
(blueprint: lem-weil-pbc-algebraic-monogenic-nagata-domain-n2).
-/

@[expose] public section

universe u

/-- An algebraic injective monogenic extension of Nagata domains is N-2.

Source: Stacks Project, Algebra, Proposition Tag 0334, claim (**) and Step 4
(blueprint: lem-weil-pbc-algebraic-monogenic-nagata-domain-n2).

Proof: Write `K = Frac(A)` and `L = Frac(B)`; injectivity embeds `K` in `L`.
Clearing denominators identifies algebraicity over `A` with algebraicity over `K`.
Since `x` generates `B`, it generates `L` as a field over `K`, so `L/K` is finite.
For any finite extension `M/L`, the tower law makes `M/K` finite. The integral
closure `A'` of `A` in `M` is finite over `A` by N-2 (the zero prime of the Nagata
hypothesis), normal with fraction field `M`, and Nagata by Tag 032T. Inside `M`,
put `T = A'[x]`. The finite module generators of `A'` over `A` generate `T` over
`B`: expand coefficients of each polynomial in `x` in those generators. Thus
`T/B` is finite, hence integral, and `Frac(T) = M` since `A'` is contained in `T`.
The integral closures of `B` and `T` in `M` agree: integrality over `B` implies
integrality over `T` by the same equation; conversely use transitivity through
`T/B`. Claim (***) of Tag 0334 makes `T` N-1, so this closure is finite over `T`.
Finiteness transitivity makes it finite over `B`. Varying `M/L` proves N-2.

No normality of `A` is needed: only `A'` must be normal. If `x = 0` or is in the
image of `A`, `L = K` and the same argument applies. -/
theorem isN2_of_algebraic_monogenic_nagata_domain (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] (hA : IsNagataRing A)
    (hinj : Function.Injective (algebraMap A B)) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) (hx : IsAlgebraic A x) :
    IsN2 B (FractionRing B) := by
  let K := FractionRing A
  let L := FractionRing B
  have hinjL : Function.Injective (algebraMap A L) :=
    (IsFractionRing.injective B L).comp hinj
  let : Algebra K L := (IsFractionRing.lift hinjL : K →+* L).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsFractionRing.lift_algebraMap hinjL a).symm
  let E := IntermediateField.adjoin K ({algebraMap B L x} : Set L)
  have hB : ∀ b : B, algebraMap B L b ∈ E := by
    intro b
    have hb : b ∈ Algebra.adjoin A ({x} : Set B) := hgen ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
      exact E.algebraMap_mem _
    | add y z _ _ hy hz => simpa using E.add_mem hy hz
    | mul y z _ _ hy hz => simpa using E.mul_mem hy hz
  have hE : E = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective B z
    rw [← hz]
    exact E.div_mem (hB a) (hB b)
  have hxL : IsAlgebraic A (algebraMap B L x) := hx.algHom (IsScalarTower.toAlgHom A B L)
  have hxK : IsIntegral K (algebraMap B L x) :=
    (IsFractionRing.isAlgebraic_iff A K L).mp hxL |>.isIntegral
  have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hxK
  have : FiniteDimensional K L := by
    have : FiniteDimensional K (⊤ : IntermediateField K L) := hE ▸ inferInstance
    exact Module.Finite.equiv
      (IntermediateField.topEquiv : (⊤ : IntermediateField K L) ≃ₐ[K] L).toLinearEquiv
  intro M _ _ _ _ _
  let : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra A M := ((algebraMap B M).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A K M := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap B M (algebraMap A B a) =
      algebraMap L M (IsFractionRing.lift hinjL (algebraMap A K a))
    rw [IsFractionRing.lift_algebraMap hinjL]
    exact IsScalarTower.algebraMap_apply B L M (algebraMap A B a)
  have : FiniteDimensional K M := Module.Finite.trans L M
  let C := integralClosure A M
  have : Module.Finite A C := isN2_of_isNagataRing_domain A hA M
  let : IsFractionRing C M := integralClosure.isFractionRing_of_finite_extension K M
  let : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hC : IsNagataRing C := (finite_over_nagata_is_nagata A C hA).1
  let T := Algebra.adjoin C ({algebraMap B M x} : Set M)
  have hbT : ∀ b : B, algebraMap B M b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A ({x} : Set B) := hgen ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply A B M, IsScalarTower.algebraMap_apply A C M]
      exact T.algebraMap_mem _
    | add y z _ _ hy hz => simpa using T.add_mem hy hz
    | mul y z _ _ hy hz => simpa using T.mul_mem hy hz
  let f : B →ₐ[A] T :=
    (IsScalarTower.toAlgHom A B M).codRestrict (T.restrictScalars A) hbT
  let : Algebra B T := f.toRingHom.toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  let : IsScalarTower B T M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let g : TensorProduct A B C →ₐ[B] T :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId B T)
      (IsScalarTower.toAlgHom A C T)
  have hg : Function.Surjective g := by
    intro t
    have ht : ∀ y : M, y ∈ T → ∃ z, (g z : M) = y := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
        have hyx : y = algebraMap B M x := Set.mem_singleton_iff.mp hy
        subst y
        exact ⟨TensorProduct.tmul A x 1, by simp [g]; rfl⟩
      | algebraMap c =>
        exact ⟨TensorProduct.tmul A 1 c, by simp [g]⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        exact ⟨a + b, by simp [ha, hb]⟩
      | mul y z _ _ hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        exact ⟨a * b, by simp [ha, hb]⟩
    obtain ⟨z, hz⟩ := ht t t.property
    exact ⟨z, Subtype.ext hz⟩
  have : Module.Finite B T := Module.Finite.of_surjective g.toLinearMap hg
  have : Module.Finite T (integralClosure T M) :=
    isN1_adjoin_singleton_of_isNagataRing C M hC (algebraMap B M x)
  have : Module.Finite B (integralClosure T M) := Module.Finite.trans T _
  let q : integralClosure T M →ₗ[B] integralClosure B M :=
    { toFun := fun z ↦ ⟨z.1, isIntegral_trans z.1 z.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hq : Function.Surjective q := by
    intro z
    exact ⟨⟨z.1, z.2.tower_top⟩, rfl⟩
  exact Module.Finite.of_surjective q hq
