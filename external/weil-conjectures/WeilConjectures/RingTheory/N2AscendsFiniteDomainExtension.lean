/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink

/-!
# N-2 ascends along a finite extension of Noetherian domains

Source: Stacks Project, Algebra, Lemma Tag 032I, lines 45202-45232
(blueprint: lem-weil-pbc-n2-ascends-finite-domain-extension).
-/

@[expose] public section

universe uA uB uK uE

set_option autoImplicit false

/-- If `A ⊆ B` is a finite extension of Noetherian domains and `A` is N-2, then `B` is N-2.
Source: Stacks Project, Algebra, Lemma Tag 032I, lines 45202-45232
(blueprint: lem-weil-pbc-n2-ascends-finite-domain-extension).

Proof (the six steps of Tag 032I). (1) The injective map `A → B` induces an embedding of
fraction fields `K → E`, so every finite extension of the latter
is also an `A`-algebra through the former (using
`def-weil-pbc-localization-at-prime` and `def-pc-field-extension`). (2) Finite generators
of `B` over `A` span a finite-dimensional domain over `K`; the
finite-dimensional-domain-is-a-field lemma identifies this span with `E`, so
the fraction-field extension is finite (using
`lem-weil-pbc-finite-dimensional-domain-is-field`). (3) The tower law
(`lem-weil-pbc-field-degree-multiplicativity`) makes every finite extension of
`E` finite over `K`. (4) `IsN2 A K` therefore makes the integral
closure of `A` in that extension finite over `A` (using
`def-weil-pbc-integral-closure` and `def-weil-pbc-japanese-domain`). (5) Since `B` is finite
over `A`, it is integral, and integrality transitivity identifies that closure with the
integral closure of `B` (using `lem-weil-pbc-finite-algebra-is-integral` and
`lem-weil-pbc-integral-transitive`). (6) The same generators over `A` generate this closure
over `B`, proving `IsN2 B E` (using `def-weil-finitely-generated-module`).
-/
theorem isN2_of_finite_domain_extension (A : Type uA) (B : Type uB)
    (K : Type uK) (E : Type uE) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra B E] [IsFractionRing B E]
    (hAB : Function.Injective (algebraMap A B)) (hA : IsN2 A K) : IsN2 B E := by
  let : Algebra A E := (algebraMap B E).comp (algebraMap A B) |>.toAlgebra
  let : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap A E) :=
    (IsFractionRing.injective B E).comp hAB
  let : Algebra K E := (IsFractionRing.lift hinj : K →+* E).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsFractionRing.lift_algebraMap hinj a).symm
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hAB
  -- Localize the finite generators instead of first constructing their span as a field.
  have : FiniteDimensional K E := by
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
    exact Module.finite_def.mpr <|
      (span_eq_top_localization_localization K (nonZeroDivisors A) E hs) ▸
        Submodule.fg_span (Set.toFinite _)
  intro M _ _ _ _ _
  let : Algebra K M := ((algebraMap E M).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra A M := ((algebraMap B M).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A K M := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap B M (algebraMap A B a) =
      algebraMap E M (IsFractionRing.lift hinj (algebraMap A K a))
    rw [IsFractionRing.lift_algebraMap hinj]
    exact IsScalarTower.algebraMap_apply B E M (algebraMap A B a)
  have : FiniteDimensional K M := Module.Finite.trans E M
  -- IsN2 tests fields in K's universe; finite-dimensionality lets us shrink M to it.
  have : Small.{uK} M := Module.Finite.small K M
  let : IsScalarTower A K (Shrink.{uK} M) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply (Shrink.algEquiv A M).injective
      rw [AlgEquiv.commutes]
      change algebraMap A M a =
        (Shrink.algEquiv K M) (algebraMap K (Shrink.{uK} M) (algebraMap A K a))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply A K M a
  have : Module.Finite A (integralClosure A (Shrink.{uK} M)) := hA (Shrink.{uK} M)
  have : Module.Finite A (integralClosure A M) :=
    Module.Finite.equiv (Shrink.algEquiv A M).mapIntegralClosure.toLinearEquiv
  let f : integralClosure A M →ₗ[A] integralClosure B M :=
    { toFun := fun x ↦ ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Surjective f := by
    intro x
    exact ⟨⟨x.1, isIntegral_trans x.1 x.2⟩, rfl⟩
  have : Module.Finite A (integralClosure B M) := Module.Finite.of_surjective f hf
  exact Module.Finite.of_restrictScalars_finite A B (integralClosure B M)
