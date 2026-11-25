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
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!

# The pullback `g^*` sends flat resolutions to K-flat complexes

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat`.

The comparison map `Lg^*(K ⊗ᴸ L) ⟶ Lg^*K ⊗ᴸ Lg^*L` for the derived pullback on pro-étale
sheaves, which enters the projection formula, is computed on flat resolutions of `K` and `L`.
Its construction needs the pullback `g^*` to send these resolutions to K-flat complexes.

The flat resolutions are `ℤ`-indexed colimits of bounded above complexes of flat sheaves,
and `g^*` commutes with colimits, being a left adjoint. So it is enough that `g^*` sends
flat sheaves to flat sheaves, by `CategoryTheory.Functor.PreservesFlat`. We record this as
the hypothesis class `AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A` on the coefficient
category `A`, and deduce from it that `g^*` sends flat resolutions to K-flat complexes.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.UpperStarPreservesFlat`: for every morphism of schemes `g`,
  the pullback `g^*` on `A`-valued pro-étale sheaves preserves flat objects.
- `AlgebraicGeometry.ProEtale.kFlat_upperStar_mapHomologicalComplex_obj`: under this
  hypothesis, `g^*` sends `ℤ`-indexed colimits of bounded above complexes of flat sheaves,
  in particular flat resolutions, to K-flat complexes.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- For every morphism of schemes `g : X ⟶ Y`, the pullback `g^*` on `A`-valued pro-étale
sheaves sends flat sheaves to flat sheaves. -/
class ProEtale.UpperStarPreservesFlat : Prop where
  preservesFlat {X Y : Scheme.{u}} (g : X ⟶ Y) : (g)^*[A].PreservesFlat

attribute [instance] ProEtale.UpperStarPreservesFlat.preservesFlat

variable {A}

/-- If `g^*` preserves flat pro-étale sheaves, it sends `ℤ`-indexed colimits of bounded above
complexes of flat pro-étale sheaves to K-flat complexes. This applies to the functorial flat
resolutions, see `CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj`. -/
lemma ProEtale.kFlat_upperStar_mapHomologicalComplex_obj [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) {K : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (hK : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ K) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K) :=
  (g)^*[A].kFlat_mapHomologicalComplex_obj_of_colimitsOfShape hK

end AlgebraicGeometry
