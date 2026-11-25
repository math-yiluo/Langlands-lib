/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-!

# The derived finite-coefficient comparison commutes with pushforward and extension by zero

Let `T` be a finite discrete commutative ring and `g : X ⟶ Y` a morphism of schemes. The
equivalence `ProEtale.finiteCoefficientModEquivalence` identifies module objects over
`Λ_X = p_X^* T̲` with pro-étale sheaves of `T`-modules on `X`, and commutes with pushforward
(`ProEtale.lowerStarFiniteCoefficientModEquivalenceIso`) and pullback
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso`). This file derives the consequences for
the derived pushforward and for extension by zero along open immersions.

## Main definitions and results

* `ProEtale.finiteCoefficientDerivedLowerStarIso`: the derived comparison commutes with the
  derived pushforward, `D(Φ_X) ⋙ Rg_* ≅ Rg_*⟦T̲⟧ ⋙ D(Φ_Y)`.
* `CategoryTheory.Adjunction.leftAdjointCompEquivalenceIso`: a commutation of right adjoints
  with equivalences induces the conjugate commutation of the left adjoints. Hence the extension
  by zero versions `ProEtale.finiteCoefficientModOpenImmersionLowerShriekIso` and
  `ProEtale.finiteCoefficientDerivedOpenImmersionLowerShriekIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### Transporting a commutation of right adjoints to the left adjoints -/

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  (eC : C ≌ C') (eD : D ≌ D') {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}

/-- Given equivalences `eC : C ≌ C'`, `eD : D ≌ D'` and adjunctions `L ⊣ R`, `L' ⊣ R'`, an
isomorphism `eC ⋙ R' ≅ R ⋙ eD` of right adjoints induces the conjugate isomorphism
`eD ⋙ L' ≅ L ⋙ eC` of left adjoints. -/
noncomputable def leftAdjointCompEquivalenceIso (adj : L ⊣ R) (adj' : L' ⊣ R')
    (i : eC.functor ⋙ R' ≅ R ⋙ eD.functor) : eD.functor ⋙ L' ≅ L ⋙ eC.functor :=
  (conjugateIsoEquiv (adj.comp eC.toAdjunction) (eD.toAdjunction.comp adj')).symm
    (Iso.inverseCompIso (Iso.isoCompInverse i.symm ≪≫ Functor.associator _ _ _))

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The derived finite-coefficient comparison commutes with pushforward**: for
`Φ = finiteCoefficientDerivedEquivalence`, `Φ_X ⋙ Rg_* ≅ Rg_*⟦T̲⟧ ⋙ Φ_Y`. Since `Φ_X` is an
exact equivalence, it preserves K-injective complexes and `D(Φ_X) ⋙ Rg_* ≅ R(Φ_X ⋙ g_*)`; since
`Φ_Y` is exact, `R(g_*⟦T̲⟧ ⋙ Φ_Y) ≅ Rg_*⟦T̲⟧ ⋙ D(Φ_Y)`; the two right derived functors are
identified by `lowerStarFiniteCoefficientModEquivalenceIso`. -/
noncomputable def finiteCoefficientDerivedLowerStarIso :
    (finiteCoefficientDerivedEquivalence X T).functor ⋙
        R((g)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ≅
      R((g)_*⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientDerivedEquivalence Y T).functor :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIso
      (finiteCoefficientModEquivalence X T).functor _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarFiniteCoefficientModEquivalenceIso g T).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _
      (finiteCoefficientModEquivalence Y T).functor

/-! ### Extension by zero -/

/-- **The finite-coefficient comparison commutes with extension by zero** along an open
immersion `j`: `Φ_U ⋙ j_! ≅ j_!⟦T̲⟧ ⋙ Φ_X`, the conjugate of
`upperStarFiniteCoefficientModEquivalenceIso` along the adjunctions `j_! ⊣ j^*`. -/
noncomputable def finiteCoefficientModOpenImmersionLowerShriekIso {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (finiteCoefficientModEquivalence U T).functor ⋙
        (j)_!open[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      (j)_!open⟦Profinite.continuousMapRingObj T⟧ ⋙
        (finiteCoefficientModEquivalence X T).functor :=
  Adjunction.leftAdjointCompEquivalenceIso _ _
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj T) j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction _ j)
    (upperStarFiniteCoefficientModEquivalenceIso j T).symm

/-- **The derived finite-coefficient comparison commutes with extension by zero** along an open
immersion `j`: `Φ_U ⋙ Dj_! ≅ Dj_!⟦T̲⟧ ⋙ Φ_X`, both extensions by zero being exact. -/
noncomputable def finiteCoefficientDerivedOpenImmersionLowerShriekIso {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (finiteCoefficientDerivedEquivalence U T).functor ⋙
        D((j)_!open[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ≅
      D((j)_!open⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientDerivedEquivalence X T).functor :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (finiteCoefficientModOpenImmersionLowerShriekIso T j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale
