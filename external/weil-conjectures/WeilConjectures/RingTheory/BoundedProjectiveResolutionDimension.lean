/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import WeilConjectures.RingTheory.ProjectiveResolutionSuccSplice

/-!
# Bounded projective resolutions and projective dimension

Mathlib defines projective dimension by Ext vanishing. This module constructs the
bounded projective resolution needed to compare it with the explicit resolution predicate.
Source: Stacks Project, Algebra, Lemma 065R.
-/

@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- The explicit bounded-resolution predicate agrees with Mathlib's projective-dimension
predicate. Unlike the Ext criteria already in Mathlib, the reverse implication constructs
an actual bounded projective resolution. Induct on the bound: at zero use the identity
resolution of a projective object; at a successor use Mathlib's dimension shifting for
the kernel of a projective epimorphism and augment its shorter resolution. Exactness,
projectivity and the support bound of the augmented complex give the required resolution.
The forward implication represents Ext classes by cocycles on the zero resolution terms
and applies Mathlib's `HasProjectiveDimensionLT.mk`.
Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3).
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · rintro ⟨P, hP⟩
    apply (hasProjectiveDimensionLT_iff X (n + 1)).mpr
    intro i hi Y a
    obtain ⟨f, _, rfl⟩ := P.extMk_surjective a (i + 1) rfl
    have hfzero : f = 0 := (hP i (by omega)).eq_of_src _ _
    simpa only [hfzero] using P.extMk_zero (i + 1) rfl
  · intro h
    induction n generalizing X with
    | zero =>
      have : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr h
      refine ⟨ProjectiveResolution.self X, fun i hi ↦ ?_⟩
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    | succ n ih =>
      let S := ShortComplex.mk _ _ (Limits.kernel.condition (Projective.π X))
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hK : HasProjectiveDimensionLE S.X₁ n :=
        (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
      exact hasProjectiveResolutionLE_of_shortExact_projective_middle n S hS
        inferInstance (ih S.X₁ hK)
/-- A module has a projective resolution of finite length if and only if it has finite
projective dimension. -/
theorem exists_hasProjectiveResolutionLE_iff
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) :
    (∃ n, HasProjectiveResolutionLE X n) ↔ HasFiniteProjectiveDimension X :=
  exists_congr fun n ↦ hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n

/-- If `d` is the least length of a projective resolution of a nonzero module `X`, then the
projective dimension of `X` is `d`. Source: Stacks Project, Algebra, Lemma 065R. -/
theorem projectiveDimension_eq_of_hasProjectiveResolutionLE
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (hX : ¬ Limits.IsZero X) (d : ℕ)
    (hd : HasProjectiveResolutionLE X d) (hmin : ∀ m < d, ¬ HasProjectiveResolutionLE X m) :
    projectiveDimension X = d := by
  refine le_antisymm ((projectiveDimension_le_iff X d).2
    ((hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X d).1 hd)) ?_
  cases d with
  | zero =>
    have hne : projectiveDimension X ≠ ⊥ := fun h ↦ hX ((projectiveDimension_eq_bot_iff X).1 h)
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    rw [← ha]
    exact WithBot.coe_le_coe.2 (zero_le (a := a))
  | succ k =>
    refine (projectiveDimension_ge_iff X (k + 1)).2 fun h ↦ ?_
    exact hmin k (Nat.lt_succ_self k)
      ((hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X k).2 h)

end ModuleCat

namespace Ring

/-- Global dimension at most `n` means that every module has a projective resolution of length
at most `n`. -/
theorem hasGlobalDimensionLE_iff (R : Type u) [CommRing R] (n : ℕ) :
    HasGlobalDimensionLE.{u, max u v} R n ↔
      ∀ M : ModuleCat.{max u v} R, ModuleCat.HasProjectiveResolutionLE M n :=
  forall_congr' fun M ↦
    (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE M n).symm

end Ring
