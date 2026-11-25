/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.FiniteComparisonConstantRealization

/-! # Pullback of finite scalar realizations on constant charts

Source: blueprint scalar-six-ctf (1), finite projective local models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- On a constant ordinary comparison chart, the pullback of the finite scalar
realization is the single complex of the realized constant module. This comparison
requires no finiteness or projectivity of the constant module.

Source: blueprint scalar-six-ctf (1), constant-model and pullback comparisons;
Stacks 099Y and the exact-functor derived single comparison.

Proof: commute each exact functor with the degree-zero single functor. The finite
comparison realization commutes with scheme pullback, and restriction along e.hom
commutes with inverse image via the coefficient-pullback comparison. Apply the given
constant-chart isomorphism and compose these isomorphisms. Every comparison is an
isomorphism on the whole module category, so empty charts and the zero ring cause no
exception. -/
theorem finiteScalarRealizationConstantChart
    (S T : Scheme.{u}) (f : T ⟶ S)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (i : (AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).obj L) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) :
    Nonempty ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj
      ((finiteScalarRealization A e eR S).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap e.hom.hom T)).obj
          ((finiteComparisonRealization A T eR).obj
            ((constantSheaf (Scheme.ProEt.topology T)
              (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)))) := by
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S
  let H := finiteComparisonRealization A S eR
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (coefficientMap e.hom.hom S)
  let UT := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.hom.hom T)
  let Pf := CondensedRing.upperStar Λ.X f
  let s := U.mapDerivedCategory.mapIso
      (H.mapDerivedCategory.mapIso ((N.mapDerivedCategorySingleFunctor 0).app L) ≪≫
        (H.mapDerivedCategorySingleFunctor 0).app (N.obj L)) ≪≫
    (U.mapDerivedCategorySingleFunctor 0).app (H.obj (N.obj L))
  -- Elaborated without an expected type, so that its instance arguments are synthesized.
  let c := comapUpperStarIso (Λ := Λ.X) (Λ' := Profinite.continuousMapRingObj.{u} A)
    e.hom.hom f
  let r := finiteComparisonRealizationUpperStarIso A eR f
  let k := (c.app (H.obj (N.obj L))).symm ≪≫ UT.mapIso (r.app (N.obj L)).symm ≪≫
      UT.mapIso ((finiteComparisonRealization A T eR).mapIso i)
  exact ⟨Pf.mapDerivedCategory.mapIso s ≪≫
    (Pf.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso k⟩

end AlgebraicGeometry.ProEtale.CondensedRing
