/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyExchange
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.TraceFormula.WeilSheafLowerStarDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.WeilObject.BoundedConstructible.Homology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.TraceFormula.UnitBasis
public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.Mathlib.CategoryTheory.Iso
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.Shift.ShiftDecomposition
public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict
public import WeilConjectures.AlgebraicGeometry.ClosedPointsFiberProduct
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadingOut
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitDimension
public import WeilConjectures.TraceFormula.FrobeniusIterate
import WeilConjectures.AlgebraicGeometry.OverPullbackFiniteType

/-!

# Homology sheaves of the pushforward of Weil objects along a finite morphism

Let `f : X ⟶ Y` be a finite morphism with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`. For a Weil object `K` for `e_X`, the homology sheaves of the derived
pushforward `Rf_*^Weil K` are the pushforwards of the homology sheaves of `K`, as Weil sheaves
for `e_Y` (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerStar_iso`):
```
Hʲ(Rf_*^Weil K) ≅ f_* Hʲ(K).
```
The pushforward of module objects along a finite morphism is exact
(`ProEtale.CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite`), so `Rf_*` commutes
with homology (`Functor.rightDerivedFunctorHomologyFunctorIso`). The Frobenius structures agree:
on homology, the derived base-change morphism of the Frobenius square is the base-change morphism
of module objects (`Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction`), and the
base-change morphism on bounded constructible complexes is the restriction of the derived one on
the ambient derived categories (`Adjunction.map_exchangeRight_app_of_comm`). The two are
assembled by `Endofunctor.IsoAlgebra.mapOfNatIsoHomologyExchangeIso`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section SquareComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- On the ambient derived category, the inverse of the composition isomorphism of the derived
pullbacks on bounded constructible complexes is that of `leftDerivedUpperStarComp`. -/
@[simp]
lemma boundedConstructibleUpperStarComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Y')
    (K : Dᵇc(Y'.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarComp Λ ℓ f g).inv.app K).hom =
      (leftDerivedUpperStarComp Λ f.left g.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- the instances of the general lemmas are found for each of the categories of module objects
/-- On the ambient derived category, the pullback comparison of a commutative square on bounded
constructible complexes is the isomorphism of total left derived functors induced by the
comparison `upperStarSquareComparison` of the pullbacks of module objects. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app_hom (sq : CommSq g' f' f g)
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom =
      (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison Λ
        ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩)).hom.app K.obj := by
  have h1 := congrArg (fun φ ↦ φ.hom)
    (boundedConstructiblePullbackSquareComparison_hom_app Λ ℓ sq K)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarComp_inv_app_hom,
    boundedConstructibleUpperStarComp_hom_app_hom, ObjectProperty.eqToHom_hom] at h1
  have h2 := Adjunction.leftDerivedFunctorSquareIso_hom_app_of_eq
    (upperStarSquareComparison Λ ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩)
    (upperStarComp Λ f'.left g.left) (upperStarComp Λ g'.left f.left)
    (by rw [Over.left_comp_left_eq_of_comp_eq sq.w]) rfl K.obj
  refine h1.trans ?_
  simpa only [leftDerivedUpperStarComp, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc] using h2.symm

-- the instances of the general lemmas are found for each of the categories of module objects
/-- `boundedConstructiblePullbackSquareComparison_hom_app_hom` through the compatibilities of the
restricted derived pullbacks with the inclusions. -/
lemma map_boundedConstructiblePullbackSquareComparison_hom_app (sq : CommSq g' f' f g)
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    L((f'.left)^*⟦Λ⟧).map ((boundedConstructibleUpperStarCompatibility Λ ℓ g).inv.app K) ≫
        (boundedConstructibleUpperStarCompatibility Λ ℓ f').inv.app
          ((boundedConstructibleUpperStar Λ ℓ g).obj K) ≫
        (boundedConstructible _).ι.map
          ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K) =
      (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison Λ
          ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩)).hom.app ((boundedConstructible _).ι.obj K) ≫
        L((g'.left)^*⟦Λ⟧).map ((boundedConstructibleUpperStarCompatibility Λ ℓ f).inv.app K) ≫
        (boundedConstructibleUpperStarCompatibility Λ ℓ g').inv.app
          ((boundedConstructibleUpperStar Λ ℓ f).obj K) := by
  change L((f'.left)^*⟦Λ⟧).map (𝟙 (L((g.left)^*⟦Λ⟧).obj K.obj)) ≫ 𝟙 _ ≫
      ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom =
    (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison Λ
      ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩)).hom.app K.obj ≫
      L((g'.left)^*⟦Λ⟧).map (𝟙 (L((f.left)^*⟦Λ⟧).obj K.obj)) ≫ 𝟙 _
  simp only [(L((f'.left)^*⟦Λ⟧)).map_id, (L((g'.left)^*⟦Λ⟧)).map_id,
    Category.id_comp, Category.comp_id]
  exact (boundedConstructiblePullbackSquareComparison_hom_app_hom Λ ℓ sq K).trans
    (Category.comp_id _).symm

end SquareComparison

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

-- the instances of the general lemmas are found for each of the categories of module objects
/-- **Homology of the pushforward of Weil objects along a finite morphism**: for finite `f`, the
Weil sheaf `Hʲ(Rf_*^Weil K)` for `e_Y` is the pushforward `f_* Hʲ(K)` of the Weil sheaf `Hʲ(K)`.
The pushforward along a finite morphism is exact, so `Rf_*` commutes with homology, and on
homology the derived base-change morphism of the Frobenius square is the base-change morphism
of module objects. -/
theorem nonempty_homologyFunctor_weilLowerStar_iso [IsFinite f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj
        ((weilLowerStar ℓ eX eY f hf).obj K) ≅
      (weilSheafLowerStar ℓ eX eY hf).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : LocallyOfFinitePresentation f.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have := preservesFiniteColimits_lowerStar_of_isFinite (Profinite.padicAlgClRingObj ℓ) f.left
  have : IsIso (Adjunction.exchangeRight
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ)
        (commSq_left_of_comp_eq eX eY hf))) :=
    isIso_lowerStarBaseChange_of_isIso _ _
  exact Endofunctor.IsoAlgebra.nonempty_mapOfNatIso_obj_iso_of_restrict
    (cX := boundedConstructibleUpperStarCompatibility _ ℓ eX.hom)
    (cY := boundedConstructibleUpperStarCompatibility _ ℓ eY.hom)
    (μX := (eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctorHomologyFunctorIso j)
    (μY := (eY.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctorHomologyFunctorIso j)
    (cR := boundedConstructibleLowerStarCompatibility ℓ f)
    (ρ := (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.rightDerivedFunctorHomologyFunctorIso j)
    (cF := boundedConstructibleUpperStarCompatibility _ ℓ f)
    (θD := Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison
      (Profinite.padicAlgClRingObj ℓ) (commSq_left_of_comp_eq eX eY hf)))
    (θK := boundedConstructiblePullbackSquareComparison _ ℓ (CommSq.mk hf))
    (B' := asIso (weilLowerStarComparison ℓ eX eY f hf))
    (b := weilSheafLowerStarComparison ℓ eX eY hf)
    (bc := Adjunction.exchangeRight
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ)
        (commSq_left_of_comp_eq eX eY hf)))
    (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).derivedAdjunction
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (map_boundedConstructiblePullbackSquareComparison_hom_app _ ℓ (CommSq.mk hf))
    (boundedConstructibleBaseChange_eq_exchangeRight ℓ (CommSq.mk hf))
    ((weilSheafLowerStarComparison_hom ℓ eX eY hf).trans (lowerStarBaseChange_eq _ _))
    (fun M ↦
      Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction_leftDerivedFunctorSquareIso
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ)
        (commSq_left_of_comp_eq eX eY hf)) j M)
    _ _ _ _ K _ _ _ _ rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

end AlgebraicGeometry.ProEtale.CondensedRing
