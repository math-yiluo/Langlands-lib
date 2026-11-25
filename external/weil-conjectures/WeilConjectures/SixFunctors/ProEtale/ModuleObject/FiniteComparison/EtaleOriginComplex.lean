/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Complexes of étale origin with finite coefficients

Let `T` be a finite discrete commutative ring and `Λ = C(-, T)` its condensed ring. An object `C`
of `D(Mod_{Λ_X})` whose image under the finite-coefficient comparison
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` is bounded below of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin`, i.e. `Φ C ≅ D(ν^*) N` for a bounded below complex `N`
of étale sheaves of `T`-modules) is represented by a strictly bounded below complex `K` of module
objects each of whose terms is of étale origin: `E (K n) ≅ ν^* F₀ⁿ` for étale sheaves `F₀ⁿ`, where
`E = ProEtale.finiteCoefficientModEquivalence`
(`ProEtale.exists_complex_of_plusEtaleOrigin`).

This is the form in which bounded below complexes of étale origin enter levelwise constructions
(traces, acyclicity) on module objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

instance additive_finiteCoefficientModEquivalence_inverse :
    (finiteCoefficientModEquivalence X T).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Complexes of étale origin.** If `Φ C` is bounded below of étale origin, then `C` is
represented by a strictly bounded below complex `K` of module objects whose terms are of étale
origin: `E (K n) ≅ ν^* F₀ⁿ` for étale sheaves of `T`-modules `F₀ⁿ`. -/
theorem exists_complex_of_plusEtaleOrigin
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C)) :
    ∃ (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) X)) ℤ) (a : ℤ),
      K.IsStrictlyGE a ∧
      (∀ n, ∃ F₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)),
        Nonempty ((finiteCoefficientModEquivalence X T).functor.obj (K.X n) ≅
          (ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj F₀)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ C) := by
  obtain ⟨N, ⟨n, hN⟩, ⟨e⟩⟩ := hC
  have : N.IsGE n := hN
  obtain ⟨N', hN', ⟨e'⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE N n
  let E := finiteCoefficientModEquivalence X T
  let ν := ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)]
  let K := (E.inverse.mapHomologicalComplex _).obj ((ν.mapHomologicalComplex _).obj N')
  refine ⟨K, n, ?_, fun m ↦ ⟨N'.X m, ⟨E.counitIso.app _⟩⟩, ⟨?_⟩⟩
  · refine (CochainComplex.isStrictlyGE_iff K n).2 fun i hi ↦ ?_
    change IsZero (E.inverse.obj (ν.obj (N'.X i)))
    exact Functor.map_isZero _ (Functor.map_isZero _ (N'.isZero_of_isStrictlyGE n i hi))
  · let Φ := finiteCoefficientDerivedEquivalence X T
    exact (E.inverse.mapDerivedCategoryFactors.app _).symm ≪≫
      Φ.inverse.mapIso ((ν.mapDerivedCategoryFactors.app N').symm ≪≫
        ν.mapDerivedCategory.mapIso e'.symm ≪≫ e) ≪≫ Φ.unitIso.symm.app C

end AlgebraicGeometry.ProEtale
