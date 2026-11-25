/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison
import all WeilConjectures.SixFunctors.PurCompactSupport.FiniteScalarPresentationCompatibility
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarSiteTransport
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsEtale
import WeilConjectures.CategoryTheory.ProperBaseChange.FullyFaithfulMate
import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Sites.CoverPreserving

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

attribute [local implicit_reducible] Scalar.functor restrictScalar
  sfIntrinsicCompactSupport

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private instance coefficientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem rightDerived_eqShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (h : F = G) :
    (Functor.rightDerivedFunctorNatIso (eqToIso h)).hom.CommShift ℤ := by
  subst G
  simp only [eqToIso_refl]
  rw [PurCompactSupport.rightDerived_refl]
  change NatTrans.CommShift (𝟙 F.rightDerivedFunctor) ℤ
  infer_instance

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private instance ambientCompactShift
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfAmbientCompactSupportCandidate A c).CommShift ℤ :=
  compactShift A c

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private instance directImageAdditive
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleConstantModuleDirectImage f A).Additive :=
  (proEtaleConstantModuleDirectImage_additive_leftExact f A).1

attribute [local instance] coefficientFinite ambientCompactShift directImageAdditive

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem finiteImageShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    letI := ambientCompactShift (Padic.coefficientExtensionRing l E (n + 1)) c
    (PurCompactSupport.finiteImageIso l E n c).hom.CommShift ℤ := by
  let : (proEtaleConstantModuleDirectImage c.g
      (Padic.coefficientExtensionRing l E (n + 1))).Additive := directImageAdditive _ _
  let := rightDerived_eqShift _ _ (PurCompactSupport.finiteDirectImage_eq l E n c.g)
  dsimp only [PurCompactSupport.finiteImageIso, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem leftScalarShift
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (leftScalarMap φ c).CommShift ℤ := by
  let : (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
      c).CommShift ℤ := ambientCompactShift _ c
  let : (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l L (m + 1))
      c).CommShift ℤ := ambientCompactShift _ c
  let a : PurCompactSupport.Change
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n))
      (PurCompactSupport.finite l L (m + 1) (Nat.succ_pos m)) := {
    map := fun T ↦ proEtaleConstantRingMap (T := T) φ
    square := fun g ↦ (proEtaleConstantInverseImageMap_naturality g
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1, u, u} φ))).symm }
  have hc := eq_of_heq (PurCompactSupport.finiteScalarPresentationCompatibility
    l E L n m a φ (fun _ ↦ rfl) c)
  have he : leftScalarMap φ c =
      (isoWhiskerRight (PurCompactSupport.finiteImageIso l E n c).symm
        (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) φ))).hom ≫
      PurCompactSupport.comparison a c ≫
      (isoWhiskerLeft (pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ))
        (PurCompactSupport.finiteImageIso l L m c)).hom := by
    rw [hc]
    simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
    simp only [← Category.assoc, ← whiskerRight_comp, Iso.inv_hom_id,
      whiskerRight_id', Category.id_comp]
    simp only [Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
      whiskerLeft_id']
    exact (Category.comp_id _).symm
  rw [he]
  let := PurCompactSupport.imageCommShift
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
  let := PurCompactSupport.imageCommShift
    (PurCompactSupport.finite l L (m + 1) (Nat.succ_pos m)) c
  let := finiteImageShift l E n c
  let := finiteImageShift l L m c
  let := NatTrans.CommShift.of_isIso (PurCompactSupport.finiteImageIso l E n c).hom ℤ
  let := PurCompactSupport.comparison_commShift a c
  dsimp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
  have h₁ : (whiskerRight (PurCompactSupport.finiteImageIso l E n c).inv
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) φ))).CommShift ℤ := by
    infer_instance
  have h₂ : (PurCompactSupport.comparison a c).CommShift ℤ := by infer_instance
  have h₃ : (whiskerLeft (pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ))
      (PurCompactSupport.finiteImageIso l L m c).hom).CommShift ℤ := by infer_instance
  infer_instance

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem cubeMate_isIso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [c.ReflectsIsomorphisms]
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (hF : IsIso (mateEquiv adj adj' (.mk _ _ _ _ pF.inv)))
    (hK : IsIso (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)))
    (hθ : IsIso (mateEquiv adj' adjK' (.mk _ _ _ _ θ'))) :
    IsIso (mateEquiv adj adjK (.mk _ _ _ _ θ)) := by
  have hFapp (M : B) : IsIso ((mateEquiv adj adj'
      (.mk _ _ _ _ pF.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hKapp (M : D) : IsIso ((mateEquiv adjK adjK'
      (.mk _ _ _ _ pK.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hθapp (M : B') : IsIso ((mateEquiv adj' adjK'
      (.mk _ _ _ _ θ')).app M) := NatIso.isIso_app_of_isIso _ M
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have he := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc M
  have hi : IsIso
      (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M) ≫
        (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M)) := by
    rw [he]
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M))
  exact isIso_of_reflects_iso _ c

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem leftScalarMap_app_isIso
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian Y] [IsNoetherian c.Z]
    (S : Scalar l E L n m φ X)
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    IsIso ((leftScalarMap φ c).app K.obj) := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l L (m + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : Finite B := Padic.finite_coefficientExtensionRing l L (m + 1) (Nat.succ_pos m)
  let ρ := FiniteCompactScalar.scalarRingMap φ
  have hK := K.property.1
  have hred := (S.preserves K).1
  have hKo : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} A) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).essImage K.obj := by
    apply ((finiteRing_constructibleDerived_origin X A).2.2.1 K.obj).mpr
    obtain ⟨hs, hc⟩ := hK
    exact ⟨hc, (finite_homology_support_iff K.obj).mp hs⟩
  obtain ⟨G₀, ⟨eK⟩⟩ := hKo
  have hGplus : DerivedCategory.TStructure.t.plus G₀.obj := by
    obtain ⟨lo, hi, _, hv⟩ := G₀.property.2
    exact ⟨lo, (DerivedCategory.isGE_iff _ lo).mpr fun i hi ↦ hv i (Or.inl hi)⟩
  let G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨G₀.obj, hGplus⟩
  let LB := (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) X).obj G.obj
  let eB : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj LB ≅
      (pbcDerivedExtend (ρ X)).obj K.obj :=
    (FiniteCompactScalar.siteScalarIso φ X).symm.app G.obj ≪≫
      (pbcDerivedExtend (ρ X)).mapIso eK
  obtain ⟨lo, hi, _, hvred⟩ := (finite_homology_support_iff _).mp hred.1
  have hvB : ∀ i : ℤ, (i < lo ∨ hi < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj LB) := by
    apply ((finiteRing_constructibleDerived_origin X B).2.2.2 LB lo hi).mpr
    intro i hi
    exact (hvred i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eB)
  let GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨LB, ⟨lo, (DerivedCategory.isGE_iff _ lo).mpr fun i hi ↦ hvB i (Or.inl hi)⟩⟩
  let t := scalarMateTransformation
    (pbcDerivedScalarAdjunction (ρ X)) (pbcDerivedScalarAdjunction (ρ Y))
    (sfIntrinsicCompactSupport c A) (sfIntrinsicCompactSupport c B)
    (sfCompactSupportRestriction c φ).hom
  have ht : IsIso (t.app
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) := by
    change IsIso (((pbcDerivedScalarAdjunction (ρ Y)).homEquiv _ _).symm _)
    have heq := FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom φ c G GB
      (Iso.refl _)
    exact heq ▸ (inferInstance : IsIso
      (FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin φ c G GB (Iso.refl _)).hom)
  have he : t.app K.obj =
      (sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (ρ Y)).map eK.inv ≫
        t.app ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj) ≫
        (pbcDerivedExtend (ρ X) ⋙ sfIntrinsicCompactSupport c B).map eK.hom := by
    rw [← t.naturality, ← Functor.map_comp_assoc, eK.inv_hom_id]
    change t.app K.obj = (sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (ρ Y)).map
      (𝟙 K.obj) ≫ t.app K.obj
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hm : (leftScalarMap φ c).app K.obj = t.app K.obj := by
    apply ((pbcDerivedScalarAdjunction (ρ Y)).homEquiv _ _).injective
    erw [Equiv.apply_symm_apply]
    simpa only [Adjunction.homEquiv_unit, leftScalarMap, TwoSquare.mk,
      Functor.id_obj, Functor.comp_obj, A, B, ρ,
      FiniteCompactScalar.scalarRingMap, sfIntrinsicCompactSupport,
      sfAmbientCompactSupportCandidate] using
      (unit_mateEquiv_symm (pbcDerivedScalarAdjunction (ρ X))
        (pbcDerivedScalarAdjunction (ρ Y))
        (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom) K.obj).symm
  rw [hm, he]
  infer_instance

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def liftIso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} (fully : I.FullyFaithful)
    (z : F ⋙ I ≅ G ⋙ I) : F ≅ G :=
  NatIso.ofComponents (fun K ↦ fully.preimageIso (z.app K)) (fun f ↦ by
    apply fully.map_injective
    simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
      Iso.app_hom, fully.map_preimage]
    exact z.hom.naturality f)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem liftIso_map
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} (fully : I.FullyFaithful)
    (z : F ⋙ I ≅ G ⋙ I) (K : C₀) :
    I.map ((liftIso fully z).hom.app K) = z.hom.app K :=
  fully.map_preimage _

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem liftIso_map_comp
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₃]
    {F G : C₀ ⥤ C₁} (J : C₁ ⥤ C₂) (I : C₂ ⥤ C₃)
    (fully : (J ⋙ I).FullyFaithful) (z : F ⋙ (J ⋙ I) ≅ G ⋙ (J ⋙ I)) (K : C₀) :
    I.map (J.map ((liftIso fully z).hom.app K)) = z.hom.app K :=
  fully.map_preimage _

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem liftNaturalIso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} (fully : I.FullyFaithful)
    (z : F ⋙ I ≅ G ⋙ I) :
    ∃ d : F ≅ G, ∀ K, I.map (d.hom.app K) = z.hom.app K :=
  ⟨liftIso fully z, liftIso_map fully z⟩

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem commShift_of_whiskerRight
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} [I.Faithful]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [I.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (whiskerRight τ I) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  ext X
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (G.obj X))).mp
  have ht := NatTrans.shift_app_comm (whiskerRight τ I) n X
  simpa only [Functor.commShiftIso_comp_hom_app, whiskerRight_app,
    NatTrans.comp_app, whiskerLeft_app, Functor.map_comp, Category.assoc,
    ← Functor.commShiftIso_hom_naturality] using ht

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def comparisonPlus (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  DerivedCategory.Plus.ι ⋙ ProEtale.finiteCoefficientIntrinsicDerivedComparison T A

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def comparisonPlus_ff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) : (comparisonPlus A T).FullyFaithful := by
  let U := ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  have : (DerivedCategory.Plus.ι ⋙ U.mapDerivedCategory).Full := ⟨fun {K L} f ↦ by
    obtain ⟨g, hg⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj L.property).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩⟩
  have : (DerivedCategory.Plus.ι ⋙ U.mapDerivedCategory).Faithful :=
    ⟨fun {K L} f g h ↦ ObjectProperty.hom_ext _
      ((ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj L.property).1 h)⟩
  let z : comparisonPlus A T ≅
      (DerivedCategory.Plus.ι ⋙ U.mapDerivedCategory) ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
    isoWhiskerLeft _ (FiniteCompactScalar.intrinsicSiteFunctorIso A T) ≪≫
      (Functor.associator _ _ _).symm
  have := Functor.Full.of_iso z.symm
  have := Functor.Faithful.of_iso z.symm
  exact Functor.FullyFaithful.ofFullyFaithful _

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private instance comparisonPlusFull (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) : (comparisonPlus A T).Full := (comparisonPlus_ff A T).full

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private instance comparisonPlusFaithful (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) : (comparisonPlus A T).Faithful := (comparisonPlus_ff A T).faithful

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem finiteOrigin
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) :
    (comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T).essImage K.obj := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := coefficientFinite l E n
  obtain ⟨G, ⟨e⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1 K.obj).mpr
    ⟨K.property.1.2, (finite_homology_support_iff K.obj).mp K.property.1.1⟩
  have hp : DerivedCategory.TStructure.t.plus G.obj := by
    obtain ⟨lo, hi, _, hv⟩ := G.property.2
    exact ⟨lo, (DerivedCategory.isGE_iff _ lo).mpr fun i hi ↦ hv i (Or.inl hi)⟩
  exact ⟨⟨G.obj, hp⟩, ⟨e⟩⟩

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def originPlus
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) :=
  Functor.essImage.liftFunctor
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι
    (comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T)
    (finiteOrigin l E n T)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def originIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) :
    originPlus l E n T ⋙ comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T ≅
      (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι :=
  Functor.essImage.liftFunctorCompIso _ _ _

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def origin
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) :=
  originPlus l E n T ⋙ DerivedCategory.Plus.ι

attribute [local implicit_reducible] origin originPlus comparisonPlus

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def origin_ff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) :
    (origin l E n T).FullyFaithful := by
  have : (originPlus l E n T ⋙
      comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T).Full :=
    Functor.Full.of_iso (originIso l E n T).symm
  have : (originPlus l E n T ⋙
      comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T).Faithful :=
    Functor.Faithful.of_iso (originIso l E n T).symm
  have := Functor.Full.of_comp_faithful (originPlus l E n T)
    (comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T)
  have := Functor.Faithful.of_comp (originPlus l E n T)
    (comparisonPlus (Padic.coefficientExtensionRing l E (n + 1)) T)
  dsimp only [origin]
  exact Functor.FullyFaithful.ofFullyFaithful _

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem comparison_map_injective
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    {K N : DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))}
    (hN : DerivedCategory.TStructure.t.plus N) {v w : K ⟶ N}
    (h : (ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).map v =
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).map w) : v = w := by
  let e := FiniteCompactScalar.intrinsicSiteFunctorIso A T
  apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map K N hN).1
  apply (sfIntrinsicDerivedEquivalence T A).functor.map_injective
  apply (cancel_epi (e.hom.app K)).mp
  exact (e.hom.naturality v).symm.trans
    ((congrArg (fun z ↦ z ≫ e.hom.app N) h).trans (e.hom.naturality w))

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem compactSiteIso_naturality
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G H : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (v : G ⟶ H) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).map
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).map v.hom) ≫
        (FiniteCompactScalar.compactSiteIso A c H).hom =
      (FiniteCompactScalar.compactSiteIso A c G).hom ≫
        (sfIntrinsicCompactSupport c A).map
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).map v.hom) := by
  simp only [FiniteCompactScalar.compactSiteIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.comp_map, Category.assoc]
  have hy := (FiniteCompactScalar.intrinsicSiteFunctorIso A Y).hom.naturality
    ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).map v.hom)
  dsimp only [Functor.comp_map] at hy
  erw [reassoc_of% hy]
  have hn := (ProEtale.compactSupportSiteComparison (ULift.{u + 1, u} A) c).inv.naturality v
  dsimp only [Functor.comp_map] at hn
  erw [← Functor.map_comp_assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
  have hr := (FiniteCompactScalar.compactRealizationIso A c).inv.naturality
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      X).mapDerivedCategory.map v.hom)
  dsimp only [Functor.comp_map] at hr
  erw [reassoc_of% hr]
  simp only [← Functor.map_comp]
  have hx := (FiniteCompactScalar.intrinsicSiteFunctorIso A X).inv.naturality v.hom
  dsimp only [Functor.comp_map] at hx
  rw [hx]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp]
  rfl

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def compactSiteNatIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙ comparisonPlus A Y ≅
      comparisonPlus A X ⋙ sfIntrinsicCompactSupport c A :=
  NatIso.ofComponents (fun G ↦
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app G) ≪≫
      FiniteCompactScalar.compactSiteIso A c G) (by
    intro G H v
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
      comparisonPlus, Category.assoc]
    have hn := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).hom.naturality v
    dsimp only [Functor.comp_map] at hn
    erw [← Functor.map_comp_assoc, hn]
    simp only [Functor.map_comp, Category.assoc]
    erw [compactSiteIso_naturality A c G H v]
    rfl)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def leftOriginIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) (op : Operation l E n c) :
    op.F ⋙ origin l E n Y ≅ origin l E n X ⋙
      Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))) c := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let FP := Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c
  let e : (op.F ⋙ originPlus l E n Y) ⋙ comparisonPlus A Y ≅
      (originPlus l E n X ⋙ FP) ⋙ comparisonPlus A Y :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft op.F (originIso l E n Y) ≪≫
      op.left ≪≫ isoWhiskerRight (originIso l E n X).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (originPlus l E n X) (compactSiteNatIso A c).symm ≪≫
      (Functor.associator _ _ _).symm
  let d := liftIso (comparisonPlus_ff A Y) e
  exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight d DerivedCategory.Plus.ι ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft (originPlus l E n X)
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c) ≪≫
    (Functor.associator _ _ _).symm

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem leftOriginIso_map
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) (op : Operation l E n c)
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y
        (Padic.coefficientExtensionRing l E (n + 1))).map
        ((leftOriginIso l E n c op).hom.app K) =
      (originIso l E n Y).hom.app (op.F.obj K) ≫ op.left.hom.app K ≫
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
          ((originIso l E n X).inv.app K) ≫
        (FiniteCompactScalar.compactSiteIso (Padic.coefficientExtensionRing l E (n + 1))
          c ((originPlus l E n X).obj K)).inv := by
  simp only [leftOriginIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Category.id_comp, Category.comp_id, Functor.map_comp]
  erw [liftIso_map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Category.id_comp, Category.comp_id, compactSiteNatIso, NatIso.ofComponents_inv_app,
    Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem rightOriginImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f) (op : Operation l E n c)
    (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    (origin l E n X).essImage
      ((etaleExceptional (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))) c).obj
        ((origin l E n Y).obj N)) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := coefficientFinite l E n
  let EX := sfIntrinsicDerivedEquivalence X A
  let EY := sfIntrinsicDerivedEquivalence Y A
  let UY := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y
  let VY := ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y
  let UX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  let H := etaleExceptional (ULift.{u + 1, u} A) c
  let G := (originPlus l E n Y).obj N
  let eY : UY.mapDerivedCategory.obj G.obj ≅ EY.inverse.obj N.obj :=
    EY.functor.preimageIso
      (((FiniteCompactScalar.intrinsicSiteFunctorIso A Y).app G.obj).symm ≪≫
        (originIso l E n Y).app N ≪≫ (EY.counitIso.app N.obj).symm)
  have hU : DerivedCategory.TStructure.t.plus (UY.mapDerivedCategory.obj G.obj) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (UY.mapDerivedCategoryPlusCompatibility.app G)
      (UY.mapDerivedCategoryPlus.obj G).property
  have hN : DerivedCategory.TStructure.t.plus (EY.inverse.obj N.obj) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso eY hU
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y G.obj G.property
  let zY : G.obj ≅ VY.rightDerivedFunctor.obj (EY.inverse.obj N.obj) :=
    asIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).unit.app G.obj) ≪≫
      VY.rightDerivedFunctor.mapIso eY
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (ULift.{u + 1, u} A) c
  have hp : DerivedCategory.TStructure.t.plus (H.obj G.obj) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso (H.mapIso zY).symm
      (ProEtale.specifiedExceptionalEtale_boundedBelow
        (ULift.{u + 1, u} A) c ⟨_, hN⟩)
  let Z : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨H.obj G.obj, hp⟩
  let z : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj Z.obj ≅
      (exceptional A c).obj N.obj :=
    (FiniteCompactScalar.intrinsicSiteFunctorIso A X).app Z.obj ≪≫
      EX.functor.mapIso (UX.mapDerivedCategory.mapIso (H.mapIso zY))
  let e : (comparisonPlus A X).obj ((originPlus l E n X).obj (op.G.obj N)) ≅
      (comparisonPlus A X).obj Z :=
    (originIso l E n X).app (op.G.obj N) ≪≫ op.right.app N ≪≫ z.symm
  let d := (comparisonPlus_ff A X).preimageIso e
  exact ⟨op.G.obj N, ⟨DerivedCategory.Plus.ι.mapIso d⟩⟩

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem scalarOriginPlusProperty
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) (S : Scalar l E L n m φ T)
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) :
    DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) T).obj
        ((origin l E n T).obj K)) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l L (m + 1)
  let C := ProEtale.finiteCoefficientIntrinsicDerivedComparison T B
  let SA := pbcDerivedExtend (proEtaleConstantRingMap (T := T) φ)
  let e : C.obj ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) T).obj
        ((origin l E n T).obj K)) ≅ SA.obj K.obj :=
    (FiniteCompactScalar.siteScalarIso φ T).symm.app _ ≪≫
      SA.mapIso ((originIso l E n T).app K)
  obtain ⟨lo, hi, _, hv⟩ := (finite_homology_support_iff _).mp (S.preserves K).1.1
  have hb := ((finiteRing_constructibleDerived_origin T B).2.2.2 _ lo hi).mpr
    (fun i h ↦ (hv i h).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e))
  exact ⟨lo, (DerivedCategory.isGE_iff _ lo).mpr fun i hi ↦ hb i (Or.inl hi)⟩

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def scalarOriginPlus
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) (S : Scalar l E L n m φ T) :=
  DerivedCategory.TStructure.t.plus.lift
    (origin l E n T ⋙ Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) T)
    (scalarOriginPlusProperty l E L n m φ T S)

attribute [local implicit_reducible] scalarOriginPlus

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private def scalarOriginIso
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) (S : Scalar l E L n m φ T) :
    S.functor ⋙ origin l L m T ≅ origin l E n T ⋙
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) T := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l L (m + 1)
  let SA := pbcDerivedExtend (proEtaleConstantRingMap (T := T) φ)
  let e : (S.functor ⋙ originPlus l L m T) ⋙ comparisonPlus B T ≅
      scalarOriginPlus l E L n m φ T S ⋙ comparisonPlus B T :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft S.functor (originIso l L m T) ≪≫
      eqToIso S.scalar_eq ≪≫ isoWhiskerRight (originIso l E n T).symm SA ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (originPlus l E n T)
        (isoWhiskerLeft DerivedCategory.Plus.ι (FiniteCompactScalar.siteScalarIso φ T)) ≪≫
      (Functor.associator _ _ _).symm
  let d := liftIso (comparisonPlus_ff B T) e
  exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight d DerivedCategory.Plus.ι

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem scalarOriginIso_map
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) (S : Scalar l E L n m φ T)
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison T
        (Padic.coefficientExtensionRing l L (m + 1))).map
        ((scalarOriginIso l E L n m φ T S).hom.app K) =
      (originIso l L m T).hom.app (S.functor.obj K) ≫
        (pbcDerivedExtend (proEtaleConstantRingMap (T := T) φ)).map
          ((originIso l E n T).inv.app K) ≫
        (FiniteCompactScalar.siteScalarIso φ T).hom.app ((origin l E n T).obj K) := by
  have hS : (eqToIso S.scalar_eq).hom.app K = 𝟙 _ := by
    have he : S.scalar_eq = rfl := Subsingleton.elim _ _
    rw [he]
    rfl
  simp only [scalarOriginIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app,
    isoWhiskerRight_hom, whiskerRight_app]
  erw [Category.id_comp, liftIso_map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    hS, Category.id_comp, Category.comp_id]
  erw [Category.id_comp, Category.id_comp]
  rfl

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem leftScalarMap_origin
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) X).obj G.obj ≅
      GB.obj) :
    (leftScalarMap φ c).app
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj) =
      (FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin φ c G GB eGB).hom := by
  rw [← FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom φ c G GB eGB]
  apply ((pbcDerivedScalarAdjunction
    (proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  simpa only [Adjunction.homEquiv_unit, leftScalarMap, TwoSquare.mk,
    Functor.id_obj, Functor.comp_obj,
    FiniteCompactScalar.scalarRingMap, sfIntrinsicCompactSupport,
    sfAmbientCompactSupportCandidate] using
    (unit_mateEquiv_symm
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ))
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)).symm

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
private theorem compactScalarIso_hom_eq
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y] :
    (Etale.FiniteCompactScalar.compactScalarIso
      (RingHom.ulift.{u + 1, u + 1} φ) c).hom =
      Etale.compactScalarMap (RingHom.ulift.{u + 1, u + 1} φ) c := by
  ext G
  simp only [Etale.FiniteCompactScalar.compactScalarIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    asIso_hom, Iso.symm_hom, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, FiniteCompactScalar.etale_open_iso_eq, ← Etale.compactScalarOpen_eq,
    Etale.compactScalarMap, Etale.ExceptionalCoefficients.compactSupportMap]

private theorem map_map_id_iso_cancel
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) {X : C} {Y : D} (e : Y ≅ F.obj X)
    {Z W : E} (z : Z ≅ G.obj (F.obj X)) (k : W ⟶ Z) :
    ((k ≫ z.hom) ≫ G.map ((F.map (𝟙 X) ≫ e.inv) ≫ e.hom)) ≫ z.inv = k := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, Iso.hom_inv_id]

/-- The finite scalar maps apart from the ambient etale mate package.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps-core).

This is the finite-subcategory part of the scalar-mate construction.  It records the
left and right comparison isomorphisms, their normalization and counit equation, and
their shift compatibilities.  The ambient etale mate package is supplied separately.
-/
structure FiniteScalarMapsCore
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) where
  q : source.F ⋙ scalarY.functor ≅ scalarX.functor ⋙ target.F
  b : source.G ⋙ scalarX.functor ≅ scalarY.functor ⋙ target.G
  q_normalized (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    ((finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι).map (q.hom.app K) ≫
        target.left.hom.app ((scalarX.functor).obj K) =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)).map (source.left.hom.app K) ≫
        (leftScalarMap a c).app K.obj
  counit (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    q.hom.app (source.G.obj N) ≫ target.F.map (b.hom.app N) ≫
        target.adjunction.counit.app ((scalarY.functor).obj N) =
      (scalarY.functor).map (source.adjunction.counit.app N)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ

-- The scalar comparison cube expands several derived naturality squares.
attribute [local irreducible] originIso leftScalarMap leftOriginIso scalarOriginIso in
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived in
/-- The finite-subcategory scalar-mate core exists.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps-core).

Transport the proper/open scalar comparison through the finite-Tor full inclusions
using bounded-below etale origins. This constructs the left comparison and proves its
normalization. Fully faithful origin functors and the exceptional essential-image
condition make the vertical adjunction mates invertible. The scalar comparison cube
then transports invertibility of the ambient etale mate to the finite right mate.
The mate counit identity gives the displayed counit equation; finite-image transport
of the canonical scalar shift gives both shift equations.
-/
theorem finiteScalarMapsCore_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) :
    Nonempty (FiniteScalarMapsCore l E L n m a c scalarX scalarY source target) := by
  classical
  have : IsNoetherian Y := noetherianOfField D.k Y
  have : IsNoetherian c.Z := noetherianCompactification c
  let IX := (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι
  let IY := (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι
  let SX := pbcDerivedExtend (proEtaleConstantRingMap (T := X) a)
  let SY := pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)
  let FA := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  let FB := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l L (m + 1))
  have happ (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
      IsIso ((whiskerLeft IX (leftScalarMap a c)).app K) :=
    leftScalarMap_app_isIso l E L n m a c scalarX K
  let : IsIso (whiskerLeft IX (leftScalarMap a c)) := NatIso.isIso_of_isIso_app _
  let e : (source.F ⋙ scalarY.functor) ⋙ IY ≅ (scalarX.functor ⋙ target.F) ⋙ IY :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft source.F (eqToIso scalarY.scalar_eq) ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight source.left SY ≪≫
      Functor.associator _ _ _ ≪≫ asIso (whiskerLeft IX (leftScalarMap a c)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eqToIso scalarX.scalar_eq).symm FB ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft scalarX.functor target.left.symm ≪≫
      (Functor.associator _ _ _).symm
  obtain ⟨q, hqapp⟩ := liftNaturalIso
    (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).fullyFaithfulι e
  have hnorm (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
      IY.map (q.hom.app K) ≫ target.left.hom.app (scalarX.functor.obj K) =
        SY.map (source.left.hom.app K) ≫ (leftScalarMap a c).app K.obj := by
    rw [hqapp K]
    have hX : (eqToIso scalarX.scalar_eq).hom.app K = 𝟙 _ := by
      have he : scalarX.scalar_eq = rfl := Subsingleton.elim _ _
      rw [he]
      rfl
    have hY : (eqToIso scalarY.scalar_eq).hom.app (source.F.obj K) = 𝟙 _ := by
      have he : scalarY.scalar_eq = rfl := Subsingleton.elim _ _
      rw [he]
      rfl
    simp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      whiskerLeft_app, whiskerRight_app, asIso_hom, Iso.symm_hom, hY,
      eqToIso.inv, eqToHom_refl, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id, Category.assoc]
    simp only [← Category.assoc, Iso.inv_hom_id_app]
    dsimp only [IX, IY, Scalar.functor, restrictScalar, Functor.comp_obj,
      ObjectProperty.lift, ObjectProperty.ι_obj]
    simp only [Category.id_comp, Category.comp_id]
    exact Category.comp_id _
  have hleftshift : (leftScalarMap a c).CommShift ℤ := leftScalarShift l E L n m a c
  let : (restrictScalar l E L n m X a scalarX.preserves).CommShift ℤ :=
    scalarX.commShift
  let : (restrictScalar l E L n m Y a scalarY.preserves).CommShift ℤ :=
    scalarY.commShift
  let := source.leftShiftRealization
  let := target.leftShiftRealization
  let := scalarX.realizationShift
  let := scalarY.realizationShift
  let := hleftshift
  let := NatTrans.CommShift.of_isIso target.left.hom ℤ
  let := NatTrans.CommShift.of_isIso (eqToIso scalarX.scalar_eq).hom ℤ
  have heShift : e.hom.CommShift ℤ := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, asIso_hom]
    infer_instance
  have hqShift : q.hom.CommShift ℤ := by
    have hq : whiskerRight q.hom IY = e.hom := by
      ext K
      exact hqapp K
    have : (whiskerRight q.hom IY).CommShift ℤ := by rw [hq]; exact heShift
    exact commShift_of_whiskerRight (I := IY) q.hom
  let beta := (mateEquiv source.adjunction target.adjunction
    (TwoSquare.mk _ _ _ _ q.inv))
  have hbeta : IsIso beta := by
    let pF := leftOriginIso l E n c source
    let pG := scalarOriginIso l E L n m a X scalarX
    let pH := scalarOriginIso l E L n m a Y scalarY
    let pK := leftOriginIso l L m c target
    let eA := etaleAdjunction
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c
    let eB := etaleAdjunction
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l L (m + 1))) c
    obtain ⟨M⟩ := finiteScalarMapsEtale_exists D l _hl E L n m a f c
    have hf : IsIso (mateEquiv source.adjunction eA
        (.mk _ _ _ _ pF.inv)) :=
      isIso_mateEquiv_of_fullyFaithful_of_essImage source.adjunction eA
        (origin_ff l E n X) (origin_ff l E n Y) pF.symm
        (rightOriginImage l E n c source)
    have hk : IsIso (mateEquiv target.adjunction eB
        (.mk _ _ _ _ pK.inv)) :=
      isIso_mateEquiv_of_fullyFaithful_of_essImage target.adjunction eB
        (origin_ff l L m X) (origin_ff l L m Y) pK.symm
        (rightOriginImage l L m c target)
    have ht : IsIso (mateEquiv eA eB (.mk _ _ _ _ M.q.inv)) := by
      rw [← M.b_normalized]
      infer_instance
    have : (origin l L m X).Full := (origin_ff l L m X).full
    have : (origin l L m X).Faithful := (origin_ff l L m X).faithful
    have : (origin l L m X).ReflectsIsomorphisms :=
      (origin_ff l L m X).reflectsIsomorphisms
    apply cubeMate_isIso source.adjunction target.adjunction
      eA eB (origin l E n X) (origin l E n Y) (origin l L m X) (origin l L m Y)
      pF pG pH pK q.inv M.q.inv ?_ hf hk ht
    intro K
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := Padic.coefficientExtensionRing l L (m + 1)
    let FB := Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c
    let SYE := Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} a) Y
    let G := (originPlus l E n X).obj K
    let GB := (scalarOriginPlus l E L n m a X scalarX).obj K
    have hp : DerivedCategory.TStructure.t.plus (FB.obj GB.obj) :=
      DerivedCategory.TStructure.t.plus.prop_of_iso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).app GB)
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).obj GB).property
    have hhom : pH.hom.app (source.F.obj K) ≫ SYE.map (pF.hom.app K) ≫
          M.q.hom.app ((origin l E n X).obj K) =
        (origin l L m Y).map (q.hom.app K) ≫
          pK.hom.app (scalarX.functor.obj K) ≫ FB.map (pG.hom.app K) := by
      apply comparison_map_injective B Y hp
      simp only [Functor.map_comp]
      have ns := (FiniteCompactScalar.siteScalarIso a Y).hom.naturality (pF.hom.app K)
      dsimp only [Functor.comp_map] at ns
      have nq :
          (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).map
              ((origin l L m Y).map (q.hom.app K)) ≫
              (originIso l L m Y).hom.app (target.F.obj (scalarX.functor.obj K)) =
            (originIso l L m Y).hom.app (scalarY.functor.obj (source.F.obj K)) ≫
              IY.map (q.hom.app K) :=
        (originIso l L m Y).hom.naturality (q.hom.app K)
      have np := compactSiteIso_naturality B c
        ((originPlus l L m X).obj (scalarX.functor.obj K)) GB
        (ObjectProperty.homMk (pG.hom.app K))
      have npi :
          (FiniteCompactScalar.compactSiteIso B c
            ((originPlus l L m X).obj (scalarX.functor.obj K))).inv ≫
            (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).map
              (FB.map (pG.hom.app K)) =
          (sfIntrinsicCompactSupport c B).map
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).map
                (pG.hom.app K)) ≫ (FiniteCompactScalar.compactSiteIso B c GB).inv := by
        apply (cancel_mono (FiniteCompactScalar.compactSiteIso B c GB).hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        erw [np]
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        rfl
      dsimp only [pH, pK]
      simp (config := { zetaDelta := true }) only [Functor.map_comp,
        scalarOriginIso_map l E L n m a Y scalarY (source.F.obj K),
        leftOriginIso_map l L m c target (scalarX.functor.obj K), Category.assoc,
        ← reassoc_of% ns, leftOriginIso_map l E n c source K,
        reassoc_of% nq, npi, scalarOriginIso_map l E L n m a X scalarX K]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
      rw [reassoc_of% (hnorm K)]
      have nl := (leftScalarMap a c).naturality ((originIso l E n X).inv.app K)
      dsimp only [Functor.comp_map] at nl
      simp only [Functor.map_comp, Category.assoc]
      erw [← reassoc_of% nl]
      erw [leftScalarMap_origin a c G GB (Iso.refl _)]
      have hm : M.q.hom = (Etale.FiniteCompactScalar.compactScalarIso
          (RingHom.ulift.{u + 1, u + 1} a) c).hom :=
        M.q_normalized.trans (compactScalarIso_hom_eq a c).symm
      rw [hm]
      dsimp only [SY]
      simp only [FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin,
        Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
        Functor.mapIso_hom, Iso.app_hom,
        Functor.map_comp, CategoryTheory.Functor.map_id,
        Category.assoc]
      simp only [← Functor.map_comp_assoc]
      dsimp only [G, GB, origin, Functor.comp_obj, ObjectProperty.ι_obj]
      simp only [Functor.map_comp,
        Category.comp_id, Category.assoc]
      simp only [← Functor.map_comp_assoc]
      simp only [← Category.assoc]
      exact (map_map_id_iso_cancel
        (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B)
        (sfIntrinsicCompactSupport c B)
        ((FiniteCompactScalar.siteScalarIso a X).app G.obj)
        (FiniteCompactScalar.compactSiteIso B c GB) _).symm
    have hi : pH.app (source.F.obj K) ≪≫ SYE.mapIso (pF.app K) ≪≫
          M.q.app ((origin l E n X).obj K) =
        (origin l L m Y).mapIso (q.app K) ≪≫
          pK.app (scalarX.functor.obj K) ≪≫ FB.mapIso (pG.app K) :=
      Iso.ext hhom
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using (congrArg Iso.inv hi).symm
  let := hbeta
  let := hqShift
  let : source.adjunction.CommShift ℤ := ⟨source.unitShift, source.counitShift⟩
  let : target.adjunction.CommShift ℤ := ⟨target.unitShift, target.counitShift⟩
  have hbShift : beta.CommShift ℤ := by
    let := NatTrans.CommShift.of_isIso q.hom ℤ
    exact NatTrans.CommShift.mateEquiv source.adjunction target.adjunction
      (TwoSquare.mk _ _ _ _ q.inv)
  refine ⟨{ q := q
            b := asIso beta
            q_normalized := hnorm
            qShift := hqShift
            bShift := hbShift
            counit := ?_ }⟩
  intro N
  have hc := mateEquiv_counit source.adjunction target.adjunction q.inv N
  change target.F.map (beta.app N) ≫
    target.adjunction.counit.app (scalarY.functor.obj N) = _ at hc
  change q.hom.app (source.G.obj N) ≫ target.F.map (beta.app N) ≫
    target.adjunction.counit.app (scalarY.functor.obj N) = _
  rw [hc]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end WeilConjectures.ExceptionalFiniteScalar
