/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Triangle

/-!
# Exactness of the stalks of Weil sheaves

The stalk functor of Weil sheaves at a geometric point preserves homology, so exact sequences
of Weil sheaves give exact sequences of stalks.

## Main statements

- `AlgebraicGeometry.WeilSheaf.preservesHomology_stalkFunctor`
- `AlgebraicGeometry.WeilSheaf.range_stalkAtMap_eq_ker`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The stalk functor of Weil sheaves at a geometric point preserves homology: it preserves
finite limits and epimorphisms. -/
instance preservesHomology_stalkFunctor
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (stalkFunctor k₀ l s).PreservesHomology := by
  have : PreservesFiniteLimits (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι :=
    inferInstance
  have : PreservesFiniteLimits (stalkFunctor k₀ l s) := by
    unfold stalkFunctor sheafFunctor
    infer_instance
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The stalks of an exact sequence of Weil sheaves form an exact sequence. -/
theorem range_stalkAtMap_eq_ker {S : ShortComplex (WeilSheaf k₀ l X)} (hS : S.Exact)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    LinearMap.range (stalkAtMap s m hs S.f) = LinearMap.ker (stalkAtMap s m hs S.g) := by
  have h := (hS.map (stalkFunctor k₀ l s))
  rw [ShortComplex.moduleCat_exact_iff] at h
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← stalkAtMap_comp, S.zero, stalkAtMap_zero]
  · obtain ⟨x, hx⟩ := h y hy
    exact ⟨x, hx⟩

end WeilSheaf

end AlgebraicGeometry
