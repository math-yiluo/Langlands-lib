/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible

/-!
# Constructible module objects with finite coefficients are of étale origin

Let `T` be a finite discrete commutative ring (for instance `𝒪_E ⧸ ℓⁿ`) and `X` a scheme. A
bounded constructible complex `K` of module objects over `Λ_X = p_X^* T̲` on the pro-étale site
(`ProEtale.boundedConstructible`) is of étale origin: under the identification
`ProEtale.finiteCoefficientDerivedEquivalence` of module objects over `Λ_X` with sheaves of
`T`-modules, it is `D(ν^*) K'` for a bounded constructible complex `K'` of étale sheaves of
`T`-modules (`ProEtale.isEtaleOrigin_of_isConstructible`).

This is the reading on the étale site of the finite coefficient categories of blueprint
`definition-constructible-sheaves`, in the form needed for blueprint
`proposition-six-operations-change-coefficients` (1) for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site.

The proof: the cohomology sheaves of `K` are constructible module objects, so the corresponding
sheaves of `T`-modules are constructible in the intrinsic sense
(`ProEtale.isConstructible_finiteCoefficientModEquivalence_functor_obj`), and an intrinsically
bounded constructible pro-étale complex is of étale origin
(`ProEtale.DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic`).

## Main statements

- `ProEtale.isEtaleOrigin_of_isConstructible`: bounded constructible complexes of module objects
  over `Λ_X` are of étale origin.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X : Scheme.{u}}

/-- **Constructible finite-coefficient module objects are of étale origin.** For a finite
discrete commutative ring `T`, a bounded constructible complex `K` of module objects over
`Λ_X = p_X^* T̲` on `X_proét` corresponds, under `finiteCoefficientDerivedEquivalence`, to a
complex of étale origin: `D(ν^*) K'` for a bounded constructible complex `K'` of étale sheaves of
`T`-modules.

This is blueprint `theorem-comparison-constructible-sheaves` (section `chap-The-pro-etale-site`,
`theorem-bounded-below-cohomology-comparison`); Bhatt–Scholze, *The pro-étale topology for schemes*,
Corollary 5.1.6 and Section 6.8. -/
theorem isEtaleOrigin_of_isConstructible
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K) :=
  DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic
    ⟨(finiteCoefficientModEquivalence X T).functor.bounded_mapDerivedCategory_obj hK.1, fun n ↦
      isConstructible_of_iso
        (((finiteCoefficientModEquivalence X T).functor.mapDerivedCategoryHomologyFunctorIso
          n).app K)
        (isConstructible_finiteCoefficientModEquivalence_functor_obj T (hK.2 n))⟩

end AlgebraicGeometry.ProEtale
