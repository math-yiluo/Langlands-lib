/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Restriction to an open subscheme preserves flat sheaves

Let `j : U ⟶ X` be an open immersion. Tensoring with the restriction `j^* F` of an étale sheaf
`F` on `X` factors as
```
Sh(U_ét) --j_!--> Sh(X_ét) --(F ⊗ -)--> Sh(X_ét) --j^*--> Sh(U_ét),
```
since `j^* j_! ≅ 𝟭` and `j^*` is strong monoidal. All three functors are exact when `F` is
flat, so `j^*` sends flat sheaves to flat sheaves.

## Main definitions and results

- `AlgebraicGeometry.Etale.tensorLeftUpperStarIso` and
  `AlgebraicGeometry.Etale.tensorRightUpperStarIso`: the factorisations above.
- `AlgebraicGeometry.Etale.preservesFlat_upperStar_of_isOpenImmersion`: `j^*` preserves flat
  objects.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

namespace Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j`, tensoring with `j^* F` is `j^* (F ⊗ j_! -)`. -/
noncomputable def tensorLeftUpperStarIso (F : Sheaf X.smallEtaleTopology A) :
    tensorLeft ((j)^*[A].obj F) ≅ (j)_!open[A] ⋙ tensorLeft F ⋙ (j)^*[A] :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (openImmersionLowerShriekUpperStarAdjunction A j).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.Monoidal.commTensorLeft (j)^*[A] F)

/-- For an open immersion `j`, tensoring with `j^* F` on the right is `j^* (j_! - ⊗ F)`. -/
noncomputable def tensorRightUpperStarIso (F : Sheaf X.smallEtaleTopology A) :
    tensorRight ((j)^*[A].obj F) ≅ (j)_!open[A] ⋙ tensorRight F ⋙ (j)^*[A] :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (openImmersionLowerShriekUpperStarAdjunction A j).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.Monoidal.commTensorRight (j)^*[A] F)

/-- The restriction `j^*` along an open immersion `j` sends flat étale sheaves to flat étale
sheaves. -/
instance preservesFlat_upperStar_of_isOpenImmersion : (j)^*[A].PreservesFlat where
  flat_obj {F} hF := by
    obtain ⟨_, _⟩ := (exactFunctor_iff _).1 hF.tensorLeft
    obtain ⟨_, _⟩ := (exactFunctor_iff _).1 hF.tensorRight
    exact ⟨(exactFunctor _ _).prop_of_iso (tensorLeftUpperStarIso A j F).symm
        ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩),
      (exactFunctor _ _).prop_of_iso (tensorRightUpperStarIso A j F).symm
        ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)⟩

end Etale

end AlgebraicGeometry
