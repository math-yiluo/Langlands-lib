/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.IntegralResiduePullOrdinaryUnit
/-! # The ordinary scalar pullback square on homotopy categories -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralIntegralResiduePullOrdinaryUnit
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
attribute [local irreducible] Mod.extendScalarsIsoComapInv
private theorem extendSquare_forget
    {C : Type*} [Category C] [MonoidalCategory C]
    [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]
    {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : R ⟶ R') [IsMonHom a] [IsIso a] (b : S ⟶ S') [IsMonHom b] [IsIso b]
    (sq : a ≫ ψ = φ ≫ b) (N : Mod C S) :
    ((Mod.extendScalarsComapIsoOfIsIso φ ψ a b sq).hom.app N).hom ≫
      ((Mod.extendScalarsIsoComapInv a).hom.app ((Mod.comap φ).obj N)).hom =
      ((Mod.extendScalarsIsoComapInv b).hom.app N).hom := by
  simp only [Mod.extendScalarsComapIsoOfIsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Mod.comp_hom', Mod.comap_map_hom,
    Mod.comapComp_hom_app_hom, Mod.comapComp_inv_app_hom,
    Mod.comapCongr_hom_app_hom]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.assoc,
    ← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom', Category.comp_id]

private theorem isoInvFac {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (u : Y ⟶ Z) (v : X ⟶ Z) (h : e.hom ≫ u = v) :
    e.inv ≫ v = u := by
  rw [← h, e.inv_hom_id_assoc]

private theorem unitCompositeMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : C ⥤ D} {S : D ⥤ C}
    {U : A ⥤ C} {T : C ⥤ A} {V : B ⥤ D} {W : D ⥤ B}
    (af : F ⊣ R) (ag : G ⊣ S) (au : U ⊣ T) (av : V ⊣ W)
    (e : W ⋙ R ≅ S ⋙ T) (q : R ⋙ U ⟶ V ⋙ S)
    (hq : ((mateEquiv av au).symm (TwoSquare.mk _ _ _ _ e.hom)) = q)
    (M : A) :
    U.map (af.unit.app M) ≫ q.app (F.obj M) =
      ag.unit.app (U.obj M) ≫ S.map
        ((Adjunction.pullIsoOfComapIso ag af au av e).hom.app M) := by
  have hi := iterated_mateEquiv_conjugateEquiv_symm af ag au av
    (TwoSquare.mk _ _ _ _ e.hom)
  have h := unit_mateEquiv_symm af ag (TwoSquare.mk _ _ _ _ q) M
  have hq' : (mateEquiv av au).symm (TwoSquare.mk _ _ _ _ e.hom) =
      TwoSquare.mk _ _ _ _ q := by
    ext
    exact congr_app hq _
  rw [hq'] at hi
  change U.map (af.unit.app M) ≫ q.app (F.obj M) = _ at h
  rw [hi] at h
  exact h

namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.comapUpperStarIso CondensedRing.comapLowerStarIso
  profinitePointModuleForgetPullbackIso
-- The concrete comparisons unfold several coefficient and module functor wrappers.
private theorem comapUpperStar_forget
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    ((CondensedRing.comapUpperStarIso a f).hom.app N).hom ≫
        (profinitePointModuleForgetPullbackIso Λ f).hom.app
          ((Mod.comap (coefficientMap a Y)).obj N) =
      (profinitePointModuleForgetPullbackIso Λ' f).hom.app N := by
  have hs := extendSquare_forget
    ((upperStar Ab.{u + 1} f).map (coefficientMap a Y))
    (coefficientMap a X) (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
    (map_coefficientMap_comp_condensedPullbackHom a f).symm
    (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ' Y)).obj N)
  let e := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)
  let z := ((upperStar Ab.{u + 1} f).mapModComapIso (coefficientMap a Y)).inv.app N
  have h := congrArg (fun k ↦ k.hom) (e.hom.naturality z)
  simp only [Mod.comp_hom', Mod.comap_map_hom] at h
  simp only [CondensedRing.comapUpperStarIso,
    profinitePointModuleForgetPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Mod.comp_hom', Mod.id_hom']
  erw [Category.id_comp, Category.comp_id]
  erw [Category.id_comp, Category.assoc, h]
  erw [← Category.assoc, hs]
  rfl


-- The concrete comparisons unfold several coefficient and module functor wrappers.
private theorem ordinary_vertical_unit
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    (Mod.comap (coefficientMap a Y)).map
        ((CondensedRing.upperStarLowerStarAdjunction Λ' f).unit.app N) ≫
      (CondensedRing.comapLowerStarIso a f).hom.app
        ((CondensedRing.upperStar Λ' f).obj N) =
    (CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app
        ((Mod.comap (coefficientMap a Y)).obj N) ≫
      (CondensedRing.lowerStar Λ f).map
        ((CondensedRing.comapUpperStarIso a f).inv.app N) := by
  apply Mod.hom_ext
  have : IsIso ((lowerStar Ab.{u + 1} f).map
      ((profinitePointModuleForgetPullbackIso Λ' f).hom.app N)) := inferInstance
  apply (cancel_mono ((lowerStar Ab.{u + 1} f).map
      ((profinitePointModuleForgetPullbackIso Λ' f).hom.app N))).1
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    CondensedRing.comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
    Category.assoc]
  erw [Category.id_comp]
  have hm : ((CondensedRing.lowerStar Λ f).map
      ((CondensedRing.comapUpperStarIso a f).inv.app N)).hom ≫
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ' f).hom.app N) =
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).hom.app
          ((Mod.comap (coefficientMap a Y)).obj N)) := by
    change (lowerStar Ab.{u + 1} f).map
      (((CondensedRing.comapUpperStarIso a f).inv.app N).hom) ≫ _ = _
    erw [← Functor.map_comp, comapUpperStar_inv_forget]
  erw [hm, moduleUnit_forget Λ' f N,
    moduleUnit_forget Λ f ((Mod.comap (coefficientMap a Y)).obj N)]
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
/-- The scalar adjunction unit intertwines the ordinary pull isomorphism and restriction.

Source: Bhatt--Scholze, Remark 6.8.15; the extension/restriction adjunction and its
compatibility with inverse image. (blueprint: new-integral-residue-pull-ordinary-unit)

Proof. Forget module structure. Pullback along the coefficient pullback isomorphism
is identified with inverse image of the underlying sheaf. Under this identification,
the components of `comapUpperStarIso` are identities. The two module adjunction units
become the unit for inverse image of abelian sheaves, and `comapLowerStarIso` has
identity underlying morphism. Hence the inverse of `comapUpperStarIso` is the inverse
vertical mate of `comapLowerStarIso`. The iterated-mates identity identifies its inverse
horizontal mate with the conjugate defining `pullIso`. The unit identity for inverse
mates gives the asserted equation on modules. Apply it in each degree, then pass to
the homotopy category; the induced adjunction unit is the degreewise scalar unit. -/
theorem residueExchangePull_ordinary_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    (((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).map
        (((Mod.extendRestrictAdjunction
          (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).unit.app H) ≫
      (NatTrans.mapHomotopyCategory
        (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj H) =
    ((Mod.extendRestrictAdjunction
        (coefficientMap (integralReductionMap ℓ E) X)).mapHomotopyCategory
          (.up ℤ)).unit.app
        ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H) ≫
      ((Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapHomotopyCategory
        (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app H) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategory_map, NatTrans.mapHomotopyCategory_app]
  have hx := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (Mod.extendRestrictAdjunction (coefficientMap (integralReductionMap ℓ E) X))
    ((((f)^*⟦integralCoeff ℓ E⟧).mapHomologicalComplex (.up ℤ)).obj P)
  erw [hx]
  simp only [← Functor.map_comp]
  congr 1
  ext i : 1
  exact ordinaryScalarUnit (integralReductionMap ℓ E) f (P.X i)

end AlgebraicGeometry.ProEtale.CondensedRing
