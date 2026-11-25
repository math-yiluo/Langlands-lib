/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTensorModels

/-!
# The totalized condensed realization of the native tensor

The sheaf-level comparison `condensedRealizationSheafTensorIso` between the condensed realization
of the native sheaf tensor of pro-étale Weil sheaves and the tensor product of condensed module
objects totalizes to an isomorphism of total tensor complexes
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTotalTensorIso`, natural in both
complexes. On the summand `P^p ⊗ T^q` of degree `n = p + q` it is the sheaf-level comparison
followed by the summand insertion
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTotalTensorIso_summand`). It is the
instance of the generic totalization `CategoryTheory.Functor.uncurryMap₂CochainComplexIso`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The totalization of the sheaf-level comparison `condensedRealizationSheafTensorIso`: the
isomorphism `R (P ⊗ T) ≅ R P ⊗ R T` of total tensor complexes, natural in both complexes. -/
def condensedRealizationTotalTensorIso :
    Functor.uncurry.obj (nativeTensorTotal k₀ l X) ⋙
        (condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ) ≅
      ((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).prod
          ((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _).map₂CochainComplex :=
  Functor.uncurryMap₂CochainComplexIso (condensedRealization k₀ l X) (curriedTensor _)
    (nativeTensorBifunctor k₀ l X).flip (condensedRealizationSheafTensorIso k₀ l X)

/-- On the summand `P^p ⊗ T^q` of degree `n = p + q`, the totalization
`condensedRealizationTotalTensorIso` is the sheaf-level comparison
`condensedRealizationSheafTensorIso` followed by the summand insertion. -/
lemma condensedRealizationTotalTensorIso_summand
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (p q n : ℤ) (h : p + q = n) :
    (condensedRealization k₀ l X).map (nativeOpenTensorInsertion k₀ l X P T p q n h) ≫
        ((condensedRealizationTotalTensorIso k₀ l X).app (P, T)).hom.f n =
      ((condensedRealizationSheafTensorIso k₀ l X).app (P.X p, T.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj P)
          (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj T)
          (curriedTensor _) (.up ℤ) p q n h :=
  Functor.map_ιMapBifunctor_uncurryMap₂CochainComplexIso_hom_app_f _ _ _ _ P T p q n h

end AlgebraicGeometry.ProEtaleWeilSheaf
