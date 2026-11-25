/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorCoordinateMap
import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorComponents
import WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorComparison
import WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorExt
import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermUnitTensorKInjective
import all WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
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

/-! # Invertibility of the derived signed action of a perfect coefficient complex

Source: the finite-free calculation in paragraph 1 of
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 08J7, 08J9 and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open CategoryTheory.MonoidalCategory
open scoped ZeroObject
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
  homModelMap totalPair pair projection evaluate derivedInternalHomOfUniverses

open CategoryTheory.RingedDerivedNative
section Monoidal
attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose
attribute [local instance] signedModuleMonoidal signedModuleSymmetric
  signedModulePreadditive signedModuleClosed signedModuleLimits signedModuleColimits
  signedGradedTensor signedGradedTensorFour signedGradedTensorLeft signedGradedTensorRight
attribute [local instance 5000] signedComplexMonoidal signedComplexBraided
attribute [local instance 10000] signedComplexStruct

section TensorTransport
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem flat_generic (P : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) :
    (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem tensor_quasiIso_between_flat
    (X A B : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hA : flat.{t, u} Y R A) (hB : flat.{t, u} Y R B) (g : A ⟶ B) (hg : QuasiIso g) :
    QuasiIso (((totalTensor.{t, u} Y R).obj X).map g) := by
  obtain ⟨X', s, hX', _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
  have hAg := flat_generic Y R A hA
  have hBg := flat_generic Y R B hB
  have hXg := flat_generic Y R X' hX'
  have : QuasiIso (s ▷ A) := hAg.2 _ hs
  have : QuasiIso (s ▷ B) := hBg.2 _ hs
  have : QuasiIso (X' ◁ g) := hXg.1 _ hg
  unfold totalTensor
  change QuasiIso (X ◁ g)
  have : QuasiIso ((s ▷ A) ≫ (X ◁ g)) := by
    rw [← whisker_exchange]
    exact quasiIso_comp _ _
  exact quasiIso_of_comp_left (s ▷ A) (X ◁ g)

end TensorTransport

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem homModelMap_isIso
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) (hI : I.IsKInjective) :
    IsIso (homModelMap.{t, u} Y R P I) := by
  have : I.IsKInjective := hI
  have : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  let eta := (CochainComplex.toKInjectiveResolution.{max u (t + 1)} _).app I
  have : QuasiIso eta :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  have : ((CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} _).obj
      I).IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ I
  have hI' : ((𝟭 (CochainComplex (Modules.{t, u} Y R) ℤ)).obj I).IsKInjective := hI
  have hh := quasiIso_homComplex_mapOfUniverses.{t + 1, t, u} eta (𝟙 P)
  rw [op_id, (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R)).map_id,
    NatTrans.id_app,
    Category.id_comp] at hh
  have : IsIso (DerivedCategory.Q.map
      (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R)).obj (op P)).map eta)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hh
  unfold homModelMap
  infer_instance

end Monoidal

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem homModelMap_naturality
    (P A B : CochainComplex (Modules.{t, u} Y R) ℤ) (g : A ⟶ B) :
    DerivedCategory.Q.map (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R)).obj (op P)).map g) ≫
        homModelMap.{t, u} Y R P B =
      homModelMap.{t, u} Y R P A ≫
        (hom.{t, u} Y R).map (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
          (DerivedCategory.Q.map g)) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  have : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      J R).1
  let K := CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} (Modules.{t, u} Y R)
  let eta := CochainComplex.toKInjectiveResolution.{max u (t + 1)} (Modules.{t, u} Y R)
  let H := (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R)).obj (op P)
  have hc := homRepresentativeIso_inv_naturality.{t + 1, t, u, max u (t + 1) + 1}
    J R P P A B (𝟙 P) g
  simp only [op_id, (homComplexFunctor (R := R)).map_id,
    NatTrans.id_app, Category.id_comp] at hc
  unfold homModelMap
  erw [← Category.assoc, ← Functor.map_comp, ← H.map_comp]
  have hn : g ≫ eta.app B = eta.app A ≫ K.map g := eta.naturality g
  erw [hn]
  erw [H.map_comp, Functor.map_comp, Category.assoc, ← hc]
  erw [DerivedCategory.Q.map_id, op_id]
  exact (Category.assoc _ _ _).symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The signed chain map induces an isomorphism into derived internal Hom when
its coefficient object is isomorphic to a two-term complex of units. The map
into derived Hom is essential: the target Hom complex need not compute it by itself.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 08J7, 08J9 and 0A8X.
(blueprint: lem-sf-perfect-coefficient-signed-hom-action).

Proof: first take the coefficient complex to be the two-term unit complex Q0.
Its signed exchange is invertible in every degree by the finite-coordinate
calculation. Tensoring a K-injective complex with this bounded complex of
finite free modules is K-injective: its terms are finite sums of shifts and
its differential is assembled by a mapping cone. Hence homModelMap is an
isomorphism in this case. For a general K-flat Q with the given derived
isomorphism to Q0, represent that isomorphism by a roof of quasi-isomorphisms
between K-flat complexes. Tensoring an arbitrary complex with a
quasi-isomorphism between K-flat complexes is a quasi-isomorphism: its cone is
acyclic and K-flat. Thus both source tensoring with Hom(P,I) and target
tensoring with I descend on this roof. Derived Hom preserves the target
isomorphisms. The signed formula determines the exchange map uniquely by
Hom projections and tensor-sheafification descent, so its naturality gives
a commutative square on each leg of the roof. Transport invertibility from
Q0 through this square. This proves invertibility of the displayed composite,
without claiming K-injectivity of I tensor Q or invertibility of f alone.
The same proof includes zero complexes and the empty site. -/
theorem perfectCoefficient_signedHomAction_isIso
    (P I Q Q0 : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hI : I.IsKInjective)
    (hQ : flat.{t, u} Y R Q) (hQ0 : flat.{t, u} Y R Q0)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q0.X k))
    (eNeg : Q0.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q0.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eQ : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q0)
    (f : ((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor.{t, u} Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) :
    IsIso (DerivedCategory.Q.map f ≫
      homModelMap.{t, u} Y R P (((totalTensor.{t, u} Y R).obj I).obj Q)) := by
  have _ := hP
  let H := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I
  let T := (totalTensor.{t, u} Y R).obj I
  let S := (totalTensor.{t, u} Y R).obj H
  obtain ⟨alpha, halpha⟩ := signedHomTensorComparison_exists Y R P I
  let action (A : CochainComplex (Modules.{t, u} Y R) ℤ) :=
    DerivedCategory.Q.map (alpha.app A) ≫ homModelMap.{t, u} Y R P (T.obj A)
  have square {A B : CochainComplex (Modules.{t, u} Y R) ℤ} (g : A ⟶ B) :
      DerivedCategory.Q.map (S.map g) ≫ action B =
        action A ≫ (hom.{t, u} Y R).map
          (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
            (DerivedCategory.Q.map (T.map g))) := by
    dsimp only [action]
    rw [← Category.assoc, ← Functor.map_comp, alpha.naturality,
      Functor.map_comp, Category.assoc]
    erw [homModelMap_naturality Y R P (T.obj A) (T.obj B) (T.map g)]
    exact (Category.assoc _ _ _).symm
  have transport {A B : CochainComplex (Modules.{t, u} Y R) ℤ}
      (hA : flat.{t, u} Y R A) (hB : flat.{t, u} Y R B) (g : A ⟶ B) (hg : QuasiIso g) :
      IsIso (action A) ↔ IsIso (action B) := by
    have : QuasiIso (S.map g) := tensor_quasiIso_between_flat Y R H A B hA hB g hg
    have : QuasiIso (T.map g) := tensor_quasiIso_between_flat Y R I A B hA hB g hg
    have : IsIso (DerivedCategory.Q.map (S.map g)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    have : IsIso (DerivedCategory.Q.map (T.map g)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    have : IsIso (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
        (DerivedCategory.Q.map (T.map g))) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have he := square g
    constructor
    · intro h
      have : IsIso (action A) := h
      have : IsIso (DerivedCategory.Q.map (S.map g) ≫ action B) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map (S.map g)) (action B)
    · intro h
      have : IsIso (action B) := h
      have : IsIso (action A ≫ (hom.{t, u} Y R).map
          (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
            (DerivedCategory.Q.map (T.map g)))) := by
        rw [← he]
        infer_instance
      exact IsIso.of_isIso_comp_right (action A)
        ((hom.{t, u} Y R).map (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
          (DerivedCategory.Q.map (T.map g))))
  have hbase : IsIso (action Q0) := by
    have (j : ℤ) : IsIso ((alpha.app Q0).f j) :=
      twoTermFreeHomTensor_component_isIso Y R P I Q0 hzero eNeg eZero
        (alpha.app Q0) (halpha Q0) j
    have : IsIso (alpha.app Q0) := HomologicalComplex.Hom.isIso_of_components _
    have hJ := twoTermUnit_tensor_isKInjective Y R I Q0 hI hzero eNeg eZero
    have : IsIso (homModelMap.{t, u} Y R P (T.obj Q0)) :=
      homModelMap_isIso Y R P (T.obj Q0) hJ
    dsimp only [action]
    infer_instance
  obtain ⟨A, s, hs, g, he⟩ := DerivedCategory.right_fac eQ.hom
  have : IsIso (DerivedCategory.Q.map s) := hs
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hs
  have hg : IsIso (DerivedCategory.Q.map g) := by
    have he' : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ eQ.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [he']
    infer_instance
  have hg' : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hg
  obtain ⟨A', r, hrflat, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) A
  have : QuasiIso r := hr
  have : QuasiIso s := hs'
  have : QuasiIso g := hg'
  have hleft : QuasiIso (r ≫ s) := inferInstance
  have hright : QuasiIso (r ≫ g) := inferInstance
  have hmiddle : IsIso (action A') :=
    (transport hrflat hQ0 (r ≫ g) hright).2 hbase
  have hresult : IsIso (action Q) := (transport hrflat hQ (r ≫ s) hleft).1 hmiddle
  have hfalpha := signedHomTensor_ext Y R P I Q f (alpha.app Q) hf (halpha Q)
  rw [hfalpha]
  exact hresult

end WeilConjectures.IntegralHom
