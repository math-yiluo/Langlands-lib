/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible

/-!
# Compactly supported cohomology of pulled-back Weil sheaves in the condensed model

Let `k₀` be a finite field, `X₀` a separated `k₀`-scheme of finite type with structure morphism
`a : X₀ ⟶ Spec k₀`, `G` a Weil sheaf of the old model on `X₀` and `M` a module object over
`ℚ̲̄_ℓ` on `X₀` such that `G` corresponds to `p^* M` with its canonical Frobenius structure under
the comparison of the two models (`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed`). Then the
cohomology sheaves `𝓗ʲ(Ra_! G)` of the compactly supported direct image of `G`, Weil sheaves of
the old model on `Spec k₀`, correspond to the pullbacks to `Spec k̄` of the cohomology sheaves
`Hʲ(Ra_! M)` of the compactly supported direct image of `M` in the condensed model, with their
canonical Frobenius structure
(`AlgebraicGeometry.WeilComplex.toCondensedHomologySheafDerivedLowerShriekIso`).

This chains `AlgebraicGeometry.WeilComplex.derivedLowerShriekCompToCondensedIso` (the two models
of `Ra_!` for the same compactification), the compatibility of the comparison with the
embeddings in degree `0` and with homology, and the base change of `Ra_!` to the geometric fibres
with Weil structures
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilRightDerivedLowerShriekIso'`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

-- `Spec k₀` lies over itself through the identity, so that the structure-morphism instances
-- `(X ↘ S).IsOver S` apply.
attribute [local instance 1100] CategoryTheory.instOverClass

variable (X) in
/-- The compactification of the structure morphism `a : X₀ ⟶ Spec k₀` chosen by
`AlgebraicGeometry.WeilComplex.derivedLowerShriek`. -/
noncomputable abbrev structureMorphismCompactification :
    Compactification (X ↘ Spec (CommRingCat.of k₀)) :=
  HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) (X ↘ Spec (CommRingCat.of k₀)))

/-- The derived comparison of a Weil sheaf `G` placed in degree `0`, for `G` corresponding to
`p^* M` with its canonical Frobenius structure (`α`): `D(E)(G[0]) ≅ D(p^*)(M[0])`. -/
noncomputable def derivedEquivCondensedSingleIso (G : WeilSheaf k₀ l X)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj G.obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj M) :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj
        (WeilSheaf.toComplex.obj G).obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M) :=
  (ProEtaleWeilSheaf.singleFunctorCompDerivedEquivCondensedIso k₀ l X 0).app G.obj ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso α ≪≫
    ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategorySingleFunctor 0).symm.app M

/-- The new-model compactly supported direct image of `D(E)(G[0])`, for `G` corresponding to
`p^* M` with its canonical Frobenius structure (`α`), is the pullback to the geometric fibre of
`Ra_!(M[0])` with its canonical Frobenius structure. -/
noncomputable def condensedRightDerivedLowerShriekSingleIso (G : WeilSheaf k₀ l X)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj G.obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj M) :
    (ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
        (structureMorphismCompactification X)).obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj
          (WeilSheaf.toComplex.obj G).obj) ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
          ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
              (structureMorphismCompactification X)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M)) :=
  (ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
      (structureMorphismCompactification X)).mapIso (derivedEquivCondensedSingleIso G M α) ≪≫
    (geometricFiberWeilRightDerivedLowerShriekIso' (structureMorphismCompactification X)
      (comp_over (X ↘ Spec (CommRingCat.of k₀)) (Spec (CommRingCat.of k₀)))).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M)

/-- **Compactly supported cohomology of pulled-back Weil sheaves in the two models**: for a Weil
sheaf `G` on `X₀` corresponding to `p^* M` with its canonical Frobenius structure (`α`), the
cohomology sheaf `𝓗ʲ(Ra_! G)` on `Spec k₀`, through the comparison of the two models, is the
pullback to the geometric fibre of `Hʲ(Ra_! M)`, with its canonical Frobenius structure; here
`Ra_!` is taken for the compactification `structureMorphismCompactification X` chosen by
`WeilComplex.derivedLowerShriek`. -/
noncomputable def toCondensedHomologySheafDerivedLowerShriekIso (G : WeilSheaf k₀ l X)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj G.obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj M) (j : ℤ) :
    (ProEtaleWeilSheaf.toCondensed k₀ l (Spec (CommRingCat.of k₀))).obj
        ((homologySheaf j).obj ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj G))).obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).obj
          ((_root_.DerivedCategory.homologyFunctor _ j).obj
            ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
              (structureMorphismCompactification X)).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) :=
  (ProEtaleWeilSheaf.homologyFunctorCompToCondensedIso k₀ l _ j).app _ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ j).mapIso
      ((derivedLowerShriekCompToCondensedIso k₀ l (X ↘ Spec (CommRingCat.of k₀))).app
          (WeilSheaf.toComplex.obj G) ≪≫
        condensedRightDerivedLowerShriekSingleIso G M α) ≪≫
    ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapDerivedCategoryHomologyFunctorIso
        j).symm.app _

end AlgebraicGeometry.WeilComplex
