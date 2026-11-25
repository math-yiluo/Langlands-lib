/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Triangle

/-!
# The long exact sequence of compactly supported cohomology

A distinguished triangle `K → L → M → K[1]` of Weil complexes gives exact sequences
`H_c^r(K) → H_c^r(L) → H_c^r(M)` (see also `WeilConjectures.WeilSheaf.CohomologySequence`): the
direct image with compact support `Ra_!` is triangulated, the cohomology sheaves form a
homological functor, and the global sections of Weil sheaves on `Spec k₀`, which are sections on
the spectrum of the algebraically closed field `k̄`, form an exact functor.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.exact_map_globalSectionsFunctor`: the global sections functor is
  exact on `Spec k₀`.
- `AlgebraicGeometry.WeilComplex.exact_homologySheaf_derivedLowerShriek`: the cohomology sheaves
  of `Ra_!` of a distinguished triangle form an exact sequence.
- `AlgebraicGeometry.WeilSheaf.exact_compactlySupportedCohomologyMap`: exactness in the middle
  for a short exact sequence of Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

section GlobalSectionsFunctor

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

instance : (globalSectionsFunctor k₀ l X).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)).Additive := Functor.additive_of_preserves_binary_products _
  have : (sheafFunctor k₀ l X).Additive := inferInstanceAs
    (ObjectProperty.ι _ ⋙ IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _).Additive
  unfold globalSectionsFunctor
  infer_instance

instance : IsIso (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (IsIso (𝟙 _))

instance : LocallyOfFiniteType (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

/-- The geometric fiber of `Spec k₀` is the spectrum of the algebraic closure `k̄`. -/
noncomputable def geometricFiberSpecIso :
    Spec (.of (AlgebraicClosure k₀)) ≅
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (asIso (pullback.snd (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
    (Scheme.specAlgebraicClosure k₀).hom)).symm

/-- The global sections on the geometric fiber `Spec k₀ ⊗ k̄ ≅ Spec k̄` preserve
epimorphisms, every pro-étale cover of the spectrum of an algebraically closed field being
split. -/
instance preservesEpimorphisms_Γ_geometricFiber_spec :
    (Sheaf.Γ (Scheme.ProEt.topology
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).PreservesEpimorphisms := by
  have := (ProEtale.upperStarLowerStarAdjunction (A := WeilCoefficients.{u} l)
    (g := (geometricFiberSpecIso k₀).hom)).isLeftAdjoint
  exact Functor.PreservesEpimorphisms.of_iso
    (ProEtale.globalSectionsUpperStarIso (WeilCoefficients.{u} l) (geometricFiberSpecIso k₀))

/-- The global sections of Weil sheaves on `Spec k₀` form an exact functor: they are left exact,
and they preserve epimorphisms, being sections on the spectrum of `k̄`. -/
theorem exact_map_globalSectionsFunctor {S : ShortComplex (WeilSheaf k₀ l (Spec (.of k₀)))}
    (hS : S.Exact) : (S.map (globalSectionsFunctor k₀ l (Spec (.of k₀)))).Exact := by
  have : (globalSectionsFunctor k₀ l (Spec (.of k₀))).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact hS.map _

end GlobalSectionsFunctor

end WeilSheaf

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology sheaves of the direct image with compact support of a distinguished triangle
of Weil complexes form an exact sequence of Weil sheaves on `Spec k₀`. -/
theorem exact_homologySheaf_derivedLowerShriek {T : Triangle (WeilComplex k₀ l X)}
    (hT : T ∈ distTriang _) (r : ℤ) :
    (ShortComplex.mk
      ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₁))
      ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₂))
      (by rw [← Functor.map_comp, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT,
        Functor.map_zero, Functor.map_zero])).Exact := by
  let Φ := derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
  have hT' := (WeilComplex.objectProperty k₀ l (Spec (.of k₀))).ι.map_distinguished _
    (Φ.map_distinguished T hT)
  have h := (_root_.DerivedCategory.homologyFunctor _ r).map_distinguished_exact _ hT'
  have := (WeilSheaf.objectProperty k₀ l (Spec (.of k₀))).preservesKernels_ι
  have : (WeilSheaf.objectProperty k₀ l (Spec (.of k₀))).ι.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact (ShortComplex.exact_map_iff_of_faithful _
    (WeilSheaf.objectProperty k₀ l (Spec (.of k₀))).ι).1 h

end WeilComplex

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Long exact sequence of compactly supported cohomology** for a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of Weil sheaves: `H_c^r(F₁) → H_c^r(F₂) → H_c^r(F₃)` is exact. -/
theorem exact_compactlySupportedCohomologyMap {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (r : ℤ) :
    Function.Exact (WeilComplex.compactlySupportedCohomologyMap (toComplex.map S.f) r)
      (WeilComplex.compactlySupportedCohomologyMap (toComplex.map S.g) r) :=
  WeilComplex.exact_compactlySupportedCohomologyMap (singleTriangle hS) r
    (singleTriangle_distinguished hS)

end WeilSheaf

end AlgebraicGeometry
