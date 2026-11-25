/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!

# The pullback `g^*` sends flat resolutions to K-flat complexes

The comparison map `Lg^*(K ⊗ᴸ L) ⟶ Lg^*K ⊗ᴸ Lg^*L` for the derived pullback on étale
sheaves, which enters the projection formula (`thm:projection-formula-torsion`), is
computed on flat resolutions of `K` and `L`. Its construction needs the pullback `g^*` to
send these resolutions to K-flat complexes.

The flat resolutions are `ℤ`-indexed colimits of bounded above complexes of flat sheaves,
and `g^*` commutes with colimits, being a left adjoint. So it is enough that `g^*` sends
flat sheaves to flat sheaves, by `CategoryTheory.Functor.PreservesFlat`. We record this as
the hypothesis class `AlgebraicGeometry.Etale.UpperStarPreservesFlat A` on the coefficient
category `A`, and deduce from it that `g^*` sends flat resolutions to K-flat complexes.
For `A = ModuleCat.{u + 1} Λ`, where flatness can be checked on stalks and `g^*`
preserves stalks, the instance is `AlgebraicGeometry.Etale.upperStarPreservesFlat_moduleCat`.

The monoidal structure on étale sheaves used here is the global instance
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`. It is
definitionally the structure `CategoryTheory.Sheaf.monoidalCategory` for which
`AlgebraicGeometry.Etale.oplaxMonoidal_upperStar` makes `g^*` oplax monoidal, see
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall_eq`.

## Main definitions and results

- `AlgebraicGeometry.Etale.UpperStarPreservesFlat`: for every morphism of schemes `g`,
  the pullback `g^*` on `A`-valued étale sheaves preserves flat objects.
- `AlgebraicGeometry.Etale.kFlat_upperStar_mapHomologicalComplex_obj`: under this
  hypothesis, `g^*` sends `ℤ`-indexed colimits of bounded above complexes of flat sheaves,
  in particular flat resolutions, to K-flat complexes.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- For every morphism of schemes `g : X ⟶ Y`, the pullback `g^*` on `A`-valued étale
sheaves sends flat sheaves to flat sheaves. -/
class Etale.UpperStarPreservesFlat : Prop where
  preservesFlat {X Y : Scheme.{u}} (g : X ⟶ Y) : (g)^*[A].PreservesFlat

attribute [instance] Etale.UpperStarPreservesFlat.preservesFlat

variable {A}

/-- If `g^*` preserves flat étale sheaves (for instance under
`AlgebraicGeometry.Etale.UpperStarPreservesFlat A`), it sends `ℤ`-indexed colimits of bounded above
complexes of flat étale sheaves to K-flat complexes. This applies to the functorial flat
resolutions, see `CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj`. -/
lemma Etale.kFlat_upperStar_mapHomologicalComplex_obj
    {X Y : Scheme.{u}} (g : X ⟶ Y) [(g)^*[A].PreservesFlat]
    {K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ}
    (hK : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ K) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K) :=
  (g)^*[A].kFlat_mapHomologicalComplex_obj_of_colimitsOfShape hK

end AlgebraicGeometry
