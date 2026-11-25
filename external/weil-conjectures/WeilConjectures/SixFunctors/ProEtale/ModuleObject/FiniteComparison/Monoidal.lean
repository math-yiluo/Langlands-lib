/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.EquivalenceTensorIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# The comparison of the two finite-coefficient models commutes with `⊗`

For a finite discrete commutative ring `T` and a scheme `X`, the equivalence
`ProEtale.finiteCoefficientModEquivalence` between module objects over `Λ_X = p_X^* T̲` and
pro-étale sheaves of `T`-modules commutes with the tensor products
(`ProEtale.finiteCoefficientModEquivalenceTensorIso`): it is restriction of scalars along the
isomorphism of ring objects `T_X ≅ Λ_X`, which is strong monoidal (`Mod.monoidal_comap`),
followed by `Sheaf.modToSheafModule`, which commutes with `⊗` (`Sheaf.modToSheafModuleTensorIso`).
Hence the derived equivalence `ProEtale.finiteCoefficientDerivedEquivalence` commutes with the
derived tensor products (`ProEtale.finiteCoefficientDerivedEquivalenceTensorIso`, by
`DerivedCategory.tensorLeftCompMapDerivedCategoryIsoOfTensorIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The equivalence `finiteCoefficientModEquivalence` commutes with the tensor products: it is
the composite of the restriction of scalars along the isomorphism of ring objects
`T_X ≅ Λ_X`, which is strong monoidal (`Mod.monoidal_comap`), and of
`Sheaf.modToSheafModule`, which commutes with the tensor products
(`Sheaf.modToSheafModuleTensorIso`). -/
noncomputable def finiteCoefficientModEquivalenceTensorIso :
    (Functor.postcompose₂.obj (finiteCoefficientModEquivalence X T).functor).obj
        (curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T) X))) ≅
      (((Functor.whiskeringLeft₂ _).obj (finiteCoefficientModEquivalence X T).functor).obj
        (finiteCoefficientModEquivalence X T).functor).obj
        (curriedTensor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)))) :=
  Functor.TensorIso.comp
    (Functor.Monoidal.tensorIso (Mod.comap (constRingSheafToCondensedRingObj X T)))
    (Sheaf.modToSheafModuleTensorIso _ (ULift.{u + 1} T))

/-- The derived equivalence `finiteCoefficientDerivedEquivalence` commutes with the derived
tensor products (`DerivedCategory.tensorLeftCompMapDerivedCategoryIsoOfTensorIso`). -/
noncomputable def finiteCoefficientDerivedEquivalenceTensorIso
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    (finiteCoefficientDerivedEquivalence X T).functor.obj (A ⊗ B) ≅
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).obj
        ((finiteCoefficientDerivedEquivalence X T).functor.obj A)).obj
        ((finiteCoefficientDerivedEquivalence X T).functor.obj B) :=
  (DerivedCategory.tensorLeftCompMapDerivedCategoryIsoOfTensorIso
    (finiteCoefficientModEquivalence X T).functor
    (finiteCoefficientModEquivalenceTensorIso X T) A).app B

end AlgebraicGeometry.ProEtale
