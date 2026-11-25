/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTotalTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.UncurriedComparison
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# The condensed realization and the pullback–tensor comparisons on complexes

Let `g : Z ⟶ Y` be a morphism of `k₀`-schemes, `ḡ` its base change to the geometric fibres, and
`u : N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z` the isomorphism of
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso`. We show that `u` carries
the native pullback–tensor comparison to the comonoidal structure of the condensed pullback `ḡ^*`:

* on sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso_tensor`), for
  the sheaf comparison `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullSheafTensor` and the
  realization of the native sheaf tensor
  `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationSheafTensorIso`;
* on cochain complexes
  (`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso_totalTensor`), for their
  totalizations `nativePullTotalTensor` and `condensedRealizationTotalTensorIso`, the comonoidal
  structure being `HomologicalComplex.mapBifunctorComparison` of `δ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- **The pullback comparison of the condensed realization is monoidal, on sheaves.** For
pro-étale Weil sheaves `M`, `N` on `Y`, the isomorphism `u : N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z` carries the
native sheaf comparison `g^*(M ⊗ N) ≅ g^* M ⊗ g^* N` to the comonoidal structure `δ` of the
condensed pullback `ḡ^*`, up to the realizations of the native sheaf tensors. -/
lemma condensedRealizationUpperStarIso_tensor :
    Functor.whiskerLeft (nativeOpenSheafTensor k₀ l Y)
          (condensedRealizationUpperStarIso k₀ l g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (nativePullSheafTensor k₀ l g).hom (condensedRealization k₀ l Z) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((upperStar k₀ l g).prod (upperStar k₀ l g))
          (condensedRealizationSheafTensorIso k₀ l Z).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (condensedRealizationSheafTensorIso k₀ l Y).hom
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((condensedRealization k₀ l Y).prod (condensedRealization k₀ l Y))
          (Functor.OplaxMonoidal.δUncurried (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((Functor.prodCompIso _ _).hom ≫
            NatTrans.prod (condensedRealizationUpperStarIso k₀ l g).hom
              (condensedRealizationUpperStarIso k₀ l g).hom ≫ (Functor.prodCompIso _ _).inv)
          (Functor.uncurry.obj (curriedTensor _)) ≫
        (Functor.associator _ _ _).hom :=
  sorry

/-- The isomorphism `u : N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z` on cochain complexes, degreewise. -/
noncomputable def condensedRealizationUpperStarComplexIso :
    (condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ) ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).mapHomologicalComplex (.up ℤ) ≅
      (upperStar k₀ l g).mapHomologicalComplex (.up ℤ) ⋙
        (condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) _ ≪≫
    NatIso.mapHomologicalComplex (condensedRealizationUpperStarIso k₀ l g) _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm

/-- **The pullback comparison of the condensed realization is monoidal, on complexes.** For
complexes `P`, `T` of pro-étale Weil sheaves on `Y`, the isomorphism `u` carries the totalized
native comparison `g^* Tot(P ⊗ T) ≅ Tot(g^* P ⊗ g^* T)` (`nativePullTotalTensor`) to the
comonoidal structure of `ḡ^*` on complexes (`HomologicalComplex.mapBifunctorComparison` of `δ`),
up to the totalized realizations `condensedRealizationTotalTensorIso` of the native tensors. -/
lemma condensedRealizationUpperStarIso_totalTensor :
    Functor.whiskerLeft (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
          (condensedRealizationUpperStarComplexIso k₀ l g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (nativePullTotalTensor k₀ l g).hom
          ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).prod
            ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)))
          (condensedRealizationTotalTensorIso k₀ l Z).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (condensedRealizationTotalTensorIso k₀ l Y).hom
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g
              (comp_over g (Spec (CommRingCat.of k₀))))).mapHomologicalComplex (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ)).prod
            ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ)))
          (HomologicalComplex.mapBifunctorComparisonUncurried
            (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar
              (Profinite.padicAlgClRingObj l)
              (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))))
            (.up ℤ)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((Functor.prodCompIso _ _).hom ≫
            NatTrans.prod (condensedRealizationUpperStarComplexIso k₀ l g).hom
              (condensedRealizationUpperStarComplexIso k₀ l g).hom ≫
            (Functor.prodCompIso _ _).inv)
          (Functor.uncurry.obj (curriedTensor _).map₂CochainComplex) ≫
        (Functor.associator _ _ _).hom :=
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
