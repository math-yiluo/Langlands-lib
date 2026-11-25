/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Uncurrying on integral Hom representatives

Source: Stacks 07A4 and 08J9; blueprint coefficient-extension paragraph 2.
(blueprint: lem-sf-integral-hom-representative-uncurry).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

-- Reuse the transparent composition cache of the chain-level construction.
attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose

section Representatives
variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
  [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

private theorem total_generator_ext (P Q I : CochainComplex (Modules.{t, u} Y R) ℤ)
    {f g : (coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, Q) ⟶ I}
    (h : ∀ (i j k : ℤ) (hij : i + j = k) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (f.f k).val.app U (coefficientTensorGenerator.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k hij U x y) =
      (g.f k).val.app U (coefficientTensorGenerator.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k hij U x y)) : f = g := by
  letI := countableColimits.{t, u} Y R
  letI := ordinaryTensorZero.{t, u} Y R
  letI := ordinaryTensorObjZero.{t, u} Y R
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (P.X i) (Q.X j)).inv).mp
  apply (adj.homEquiv _ (I.X k)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h i j k hij U x y

attribute [local irreducible] totalTensor totalPair pair projection evaluate homModelMap
  homComplexFunctor derivedInternalHomOfUniverses
  CategoryTheory.RingedDerivedNative.chainEquiv

open CategoryTheory.RingedDerivedNative

-- Compare the two Hom-complex models without unfolding the derived internal Hom.
/-- Unsigned representative uncurrying agrees with the normalized right-tensor adjunction.

Source: Stacks Tags 07A4 and 08J9; blueprint coefficient-extension paragraph 2.
(blueprint: lem-sf-integral-hom-representative-uncurry).

Proof: uncurry the chain map by the existing chain tensor-Hom equivalence; its
product-projection formula is ordinary evaluation, without a sign in the order
(source of q) tensor (source of Hom). Compose q with the fixed injective-resolution
augmentation and apply the normalization of T. Pure-tensor generation identifies
the resulting chain map with uncurrying of the augmented q. Naturality of chain
uncurrying identifies this map with the original uncurry followed by augmentation.
After localization, the augmentation followed by its fixed inverse is the identity.
This gives the comparison equation into the original target complex. -/
theorem representative_uncurry_evaluation
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)
    (P L I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hL : flat.{t, u} Y R L)
    (φ : P ⟶ homComplex (R := R) L I) :
    ∃ a : (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, L) ⟶ I,
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
        (a.f k).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R P L p q k h U x y) =
          (((φ.f p ≫ homComplexπ L I p q k h').val.app U x).app
            (op (Over.mk (𝟙 U.unop)))) y) ∧
      T.comparison.hom.app (⟨P, hP⟩, ⟨L, hL⟩) ≫
        (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj I)).symm
            (DerivedCategory.Q.map φ ≫ homModelMap.{t, u} Y R L I) =
        DerivedCategory.Q.map a := by
  letI := derivedCategory.{t, u} Y R
  refine ⟨(chainEquiv.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R P L I).symm φ, ?_, ?_⟩
  · intro p q k h h' U x y
    exact chainEquiv_symm_pure.{t + 1, t, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R P L I _ p q k h h' U x y
  · let J := AlgebraicGeometry.Scheme.ProEt.topology Y
    letI := baseGrothendieck.{t + 1, t, u} J R
    let r : I ⟶ (coefficientHomResolution.{u, t + 1, t} J R).obj I :=
      (CochainComplex.toKInjectiveResolution.{max u (t + 1)} (Modules.{t, u} Y R)).app I
    let φ' : P ⟶ homComplex (R := R) L
        ((coefficientHomResolution.{u, t + 1, t} J R).obj I) :=
      φ ≫ ((homComplexFunctor (R := R)).obj (op L)).map r
    have huncurry : CoefficientTensorUncurryModel J R S T.comparison :=
      T.uncurry_model
    let hmodels := huncurry ⟨P, hP⟩ ⟨L, hL⟩ I φ'
    obtain ⟨ψ, hψ, hsquare⟩ := hmodels
    have hψeq : ψ = (chainEquiv.{t + 1, t, u} J R P L
        ((coefficientHomResolution.{u, t + 1, t} J R).obj I)).symm φ' := by
      apply total_generator_ext Y R
      intro i j k hij U x y
      exact (hψ i j k hij (by omega) U x y).trans
        (chainEquiv_symm_pure.{t + 1, t, u} J R P L
          ((coefficientHomResolution.{u, t + 1, t} J R).obj I)
            φ' i j k hij (by omega) U x y).symm
    rw [hψeq] at hsquare
    have hn := chainEquiv_symm_naturality.{t + 1, t, u} J R
      P P L L I ((coefficientHomResolution.{u, t + 1, t} J R).obj I)
        (𝟙 P) (𝟙 L) r φ
    have htensor : (coefficientTotalTensor.{u, t + 1, t} J R).map
        (X := (P, L)) (Y := (P, L)) (𝟙 P, 𝟙 L) = 𝟙 _ :=
      (coefficientTotalTensor.{u, t + 1, t} J R).map_id (P, L)
    rw [htensor] at hn
    simp only [op_id] at hn
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app] at hn
    simp only [Category.id_comp] at hn
    change (chainEquiv.{t + 1, t, u} J R P L _).symm φ' =
      (chainEquiv.{t + 1, t, u} J R P L I).symm φ ≫ r at hn
    rw [hn] at hsquare
    simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hsquare
    have hr : DerivedCategory.Q.map r ≫
        coefficientHomResolutionInverse.{u, t + 1, t, (max u (t + 1)) + 1} J R I = 𝟙 _ := by
      exact (augmentationIso.{t + 1, t, u, (max u (t + 1)) + 1} J R I).hom_inv_id
    erw [hr, Category.comp_id] at hsquare
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [φ', CategoryTheory.Functor.map_comp, Category.assoc, homModelMap, r]
        using hsquare

end Representatives
end WeilConjectures.IntegralHom
