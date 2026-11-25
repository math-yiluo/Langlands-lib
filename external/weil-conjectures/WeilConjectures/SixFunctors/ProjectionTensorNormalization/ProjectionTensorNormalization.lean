/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import all WeilConjectures.SixFunctors.ProjectionTensorCoefficient.ProjectionCoefficientTensorTotal
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # Normalization and naturality for coefficient tensor descent

The private helpers retain the existing coefficient proof interfaces while checking their
self-contained proofs separately from the constructible coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory

namespace WeilConjectures.ProjectionTensorNormalization

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
attribute [local instance 3000] integralTowerHasDerivedCategory

open WeilConjectures.ProjectionTensorCoefficient

private theorem good (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : (proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory) :
    proEtaleFlatRepresentatives X (pbcAdicCompletion X (pbcIntegralDatum l E))
      ((complexTransport l E X).obj P.obj) := by
  let t := (SheafOfModules.ringIso_tensor_transport.{u + 1, u, u + 1, u + 2, u + 2}
    (coefficientIso l E X)).some
  constructor
  · apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
    apply (t.kflat_iff P.obj).mpr
    exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr P.property.1
  · intro n
    exact (t.flat_iff (P.obj.X n)).mpr (P.property.2 n)

private theorem inverseSquare {C : Type*} [Category* C]
    {A A' B B' : C} (a : A ≅ B) (b : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).mp
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem totalComparison_naturality
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (F : A ⥤ B) [F.Additive]
    (mu : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (hmu : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      F.map (f ⊗ₘ g) ≫ (mu X' Y').hom =
        (mu X Y).hom ≫ (F.map f ⊗ₘ F.map g))
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g)) ≫
        tensorPullbackTotal F mu hmu P' Q' =
      tensorPullbackTotal F mu hmu P Q ≫ (F.mapHomologicalComplex (.up ℤ)).map
        ((Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).map
          (Prod.mkHom f g)) := by
  simp only [Functor.uncurry_obj_map, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex,
    SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor]
  exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
    F mu hmu f g

private theorem totalIso_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    {P P' Q Q' : CochainComplex (integralTowerModules l E X) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (complexTransport l E X).map
        ((constructibleTensorTotal l E X).map (Prod.mkHom f g)) ≫
      (totalIso l E X P' Q').hom =
    (totalIso l E X P Q).hom ≫
      (totalTarget l E X).map (Prod.mkHom f g) := by
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E X)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  let := proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  let := proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let F : integralTowerModules l E X ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) := fdCoefficientTransport l E X
  let : F.Additive := fdCoefficientTransportAdditive l E X
  have h : (totalTarget l E X).map (Prod.mkHom f g) ≫ total l E X P' Q' =
      total l E X P Q ≫ (complexTransport l E X).map
        ((constructibleTensorTotal l E X).map (Prod.mkHom f g)) := by
    exact totalComparison_naturality F (moduleComparison l E X)
      (module_tensorHom_naturality l E X) f g
  exact inverseSquare (totalIso l E X P Q).symm (totalIso l E X P' Q').symm _ _ h

private theorem representativeSquare_iff {C : Type*} [Category* C]
    {A B C' D H I : C} (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D)
    (k : A ⟶ H) (m : H ⟶ I) (r : I ≅ D) :
    (f ≫ g ≫ h ≫ r.inv = k ≫ m) ↔ (f ≫ g ≫ h = k ≫ m ≫ r.hom) := by
  simpa only [Category.assoc] using (r.comp_inv_eq (f := f ≫ g ≫ h) (g := k ≫ m))

/-- Unique tensor descent with the inverse representative normalization.
Source: Stacks Tags 04VK and 07A4; the coefficient comparison in projection-formula step 13
(blueprint: lem-sf-projection-tensor-normalization-descent).
Proof: use tensorComparisonDescent on the natural isomorphism of representative total tensors.
Its equation is the desired equation postcomposed with the target representative isomorphism.
Postcompose with the inverse to obtain the stated normalization. Conversely cancel that inverse
and apply the uniqueness clause of tensorComparisonDescent. No object-surjectivity hypothesis is
used: fully faithful restriction supplies both existence and uniqueness. -/
theorem normalizedTensorDescent
    {K : Type u₁} [Category.{v₁} K] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ≅ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : ∀ Z : K × K, F.obj (t.obj Z) ≅ t'.obj ((F.prod F).obj Z))
    (hb : ∀ {X Y : K × K} (f : X ⟶ Y),
      F.map (t.map f) ≫ (b Y).hom = (b X).hom ≫ t'.map ((F.prod F).map f)) :
    ∃! a : T ⋙ LF ≅ (LF.prod LF) ⋙ T',
      ∀ X Y : P.FullSubcategory,
        LF.map (r.hom.app (X, Y)) ≫ a.hom.app (q.obj X.obj, q.obj Y.obj) ≫
            T'.map (Prod.mkHom (eps.hom.app X.obj) (eps.hom.app Y.obj)) ≫
            r'.inv.app (⟨F.obj X.obj, hF X.obj X.property⟩,
              ⟨F.obj Y.obj, hF Y.obj Y.property⟩) =
          eps.hom.app (t.obj (X.obj, Y.obj)) ≫ q'.map ((b (X.obj, Y.obj)).hom) := by
  obtain ⟨a, ha, hu⟩ := tensorComparisonDescent q q' F LF eps.hom P S hF ff t t' T T' r r'
    (NatIso.ofComponents b (fun f ↦ hb f))
    (fun Z _ ↦ (eps.app Z).isIso_hom)
    (fun Z Z' _ _ ↦ (eps.app (t.obj (Z, Z'))).isIso_hom)
  refine ⟨a, ?_, ?_⟩
  · intro X Y
    exact (representativeSquare_iff _ _ _ _ _
      (r'.app (⟨F.obj X.obj, hF X.obj X.property⟩,
        ⟨F.obj Y.obj, hF Y.obj Y.property⟩))).mpr
      (ha X.obj Y.obj X.property Y.property)
  · intro a' ha'
    apply hu a'
    intro X Y hx hy
    exact (representativeSquare_iff _ _ _ _ _
      (r'.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩))).mp
      (ha' ⟨X, hx⟩ ⟨Y, hy⟩)

private theorem transported_square {A : Type*} [Category* A]
    {B : Type*} [Category* B] (H : A ⥤ B)
    {X Y Z : A} {U V : B} (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z)
    (k : H.obj Z ⟶ U) (m : U ⟶ V) (n : H.obj X ⟶ V)
    (he : f ≫ g = r) (h : H.map r ≫ k ≫ m = n) :
    H.map f ≫ (H.map g ≫ k) ≫ m = n := by
  rw [Category.assoc, ← H.map_comp_assoc, he]
  exact h

end WeilConjectures.ProjectionTensorNormalization
