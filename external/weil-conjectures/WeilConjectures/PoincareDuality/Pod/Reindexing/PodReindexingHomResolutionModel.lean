/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.SixFunctors.SectionwiseTensorComparison
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageHomComparison
import all WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseFlatKFlat
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonIsomorphism
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceHomComparisonExistence
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement

/-! # Reindexing, completed coefficients, and Hom resolution models

Source: blueprint `theorem-poincare-duality-frobenius--2`, proof Steps 1--2;
Stacks Project, Tags 03EL, 0GMX, 0A8X, 0A95 and 08J7
(blueprint: lem-pod-reindexing-hom-resolution-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w z
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- A positive finite stage (`some n` means exponent n+1), or the completed stage `none`.
Source: blueprint dual-Tate compatibility, Steps 1--2
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    Option ℕ → Sheaf (ProEt.topology W) CommRingCat.{u+1}
  | none => completedIntegralCommRingSheafUnrestricted l E W
  | some n => integralCoefficientCommRingSheaf l E W n

/-- The existing module-sheaf category at either coefficient stage.
Source: blueprint dual-Tate compatibility, Steps 1--2
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingModules (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) (s : Option ℕ) :=
  SheafOfModules.{u+1} ((sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (podReindexingRing l E W s))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Constant-sheaf reindexing is natural in the coefficient ring, and its components
are the specified constant-section maps. Use the canonical comparison commuting
reindexing with sheafification, then its unit equation and uniqueness on constants.
Source: Stacks Tags 09A5 and 0H7J
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
private theorem podReindexingConstantComparison {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    ∃ κ : constantSheaf (ProEt.topology Y) CommRingCat.{u+1} ⋙
        isoSectionwiseInverseImage g CommRingCat.{u+1} ≅
        constantSheaf (ProEt.topology X) CommRingCat.{u+1},
      ∀ A : CommRingCat.{u+1},
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map
          (κ.app A).hom = isoSectionwiseConstantMap.{u,u} g A := by
  let F := proEtaleIsoPostcompose g
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F (proEtaleIsoPostcompose (inv g))
      e.2.1.some.symm e.2.2.1.some
  have : F.IsCocontinuous (ProEt.topology X) (ProEt.topology Y) :=
    (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.2.2.2.2.some
  let β := (F.pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u+1} (ProEt.topology X) (ProEt.topology Y)).symm
  let κ : constantSheaf (ProEt.topology Y) CommRingCat.{u+1} ⋙
      isoSectionwiseInverseImage g CommRingCat.{u+1} ≅
      constantSheaf (ProEt.topology X) CommRingCat.{u+1} :=
    NatIso.ofComponents (fun A ↦ β.app ((Functor.const Y.ProEtᵒᵖ).obj A))
      (fun f ↦ β.hom.naturality ((Functor.const Y.ProEtᵒᵖ).map f))
  refine ⟨κ, ?_⟩
  intro A
  apply (isoSectionwiseConstantMap_existsUnique.{u,u} g A).unique
  · intro U a
    let i := (sheafToPresheaf (ProEt.topology X) CommRingCat.{u+1}).mapIso
      (β.symm.app ((Functor.const Y.ProEtᵒᵖ).obj A))
    have hn : F.op.whiskerLeft
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)) ≫
          (κ.app A).hom.hom =
        toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) := by
      apply (i.comp_inv_eq).2
      exact (F.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u+1}
        (ProEt.topology X) (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).symm
    exact congrArg (fun f ↦ f.app (op U) a) hn
  · exact (isoSectionwiseConstantMap_existsUnique.{u,u} g A).exists.choose_spec

/-- Naturality after forgetting commutativity, before specializing the coefficient rings. -/
private theorem podReindexingConstantNaturality {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (κ : constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
      isoSectionwiseInverseImage g CommRingCat.{u + 1} ≅
        constantSheaf (ProEt.topology X) CommRingCat.{u + 1})
    {A B : CommRingCat.{u + 1}} (f : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map f)) ≫
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (κ.app B).hom =
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (κ.app A).hom ≫
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map f) := by
  exact congrArg
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (κ.hom.naturality f)

/-- The coefficient isomorphisms are uniquely normalized by constant sections at finite
levels and by all completed-ring projections.
Source: blueprint dual-Tate compatibility, Steps 1--2; Stacks Tags 03CO and 09A5
(blueprint: lem-pod-reindexing-hom-resolution-model).

Proof: use the canonical constant coefficient identification for each positive quotient.
The quotient maps commute with it, since both maps act identically on constant sections.
Sectionwise reindexing preserves the ring-sheaf inverse limit, giving the completed map.
Its projections are the prescribed finite maps. Reverse reindexing gives an inverse;
the composites have every projection equal to the original projection, so limit
uniqueness makes them identities. The same uniqueness proves uniqueness of this family.
This is Steps 1--3 of the node, using lem-weil-proetale-isomorphism-inverse-image,
def-weil-completed-integral-coefficients and def-pur-sheaf-inverse-limit. -/
theorem podReindexingCoefficient_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! c : ∀ s : Option ℕ,
      (isoSectionwiseInverseImage g CommRingCat.{u+1}).obj (podReindexingRing l E Y s) ≅
        podReindexingRing l E X s,
      (∀ n : ℕ,
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map
            (c (some n)).hom =
          isoSectionwiseConstantMap.{u,u} g
            (CommRingCat.of (ULift.{u+1} (Padic.coefficientExtensionRing l E (n+1))))) ∧
      (∀ n : ℕ,
        (c none).hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
          (isoSectionwiseInverseImage g CommRingCat.{u+1}).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫ (c (some n)).hom) := by
  obtain ⟨κ, hκ⟩ := podReindexingConstantComparison g
  let WX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})
  let F := isoSectionwiseInverseImage g RingCat.{u+1}
  let DY := integralCoefficientSheafSystem l E Y
  let DX := integralCoefficientSheafSystem l E X
  let A (n : ℕ) := CommRingCat.of (ULift.{u+1} (Padic.coefficientExtensionRing l E (n+1)))
  let α : DY ⋙ F ⟶ DX := NatTrans.ofOpSequence
    (fun n ↦ WX.map (κ.app (A n)).hom) (by
      intro n
      simp only [Functor.comp_map, DY, DX, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      simpa only [integralCoefficientSheafTransition, F, A, WX] using
        podReindexingConstantNaturality g κ
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{u+1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (n+1)).comp
              (ULift.ringEquiv : ULift.{u+1} _ ≃+* _).toRingHom))))
  have : ∀ j, IsIso (α.app j) := fun j ↦ by
    change IsIso (WX.map (κ.app (A j.unop)).hom)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let ε := asIso α
  have : PreservesLimitsOfSize.{0,0} F :=
    (isoSectionwiseInverseImage_equivalence g RingCat.{u+1}).2.1
  let ρ : F.obj (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
      completedIntegralCoefficientSheafUnrestricted l E X :=
    preservesLimitIso F DY ≪≫ HasLimit.isoOfNatIso ε
  let c : ∀ s : Option ℕ,
      (isoSectionwiseInverseImage g CommRingCat.{u+1}).obj (podReindexingRing l E Y s) ≅
        podReindexingRing l E X s
    | some n => κ.app (A n)
    | none => WX.preimageIso ρ
  have hc : ∀ n,
      (c none).hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
        (isoSectionwiseInverseImage g CommRingCat.{u+1}).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫ (c (some n)).hom := by
    intro n
    apply WX.map_injective
    rw [Functor.map_comp]
    have hρ : WX.map (c none).hom = ρ.hom := by
      exact WX.map_preimage (X := (isoSectionwiseInverseImage g CommRingCat.{u+1}).obj
        (podReindexingRing l E Y none)) (Y := podReindexingRing l E X none) ρ.hom
    rw [hρ]
    change ρ.hom ≫ limit.π DX (op n) = F.map (limit.π DY (op n)) ≫ α.app (op n)
    dsimp only [ρ, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl
  refine ⟨c, ⟨fun n ↦ hκ (A n), hc⟩, ?_⟩
  intro d hd
  have hf : ∀ n, d (some n) = c (some n) := by
    intro n
    apply Iso.ext
    apply WX.map_injective
    exact (hd.1 n).trans (hκ (A n)).symm
  funext s
  cases s with
  | some n => exact hf n
  | none =>
    apply Iso.ext
    apply WX.map_injective
    apply limit.hom_ext
    intro j
    obtain ⟨n⟩ := j
    have h₁ := congrArg WX.map (hd.2 n)
    have h₂ := congrArg WX.map (hc n)
    rw [hf n] at h₁
    simp only [Functor.map_comp] at h₁ h₂
    exact h₁.trans h₂.symm

/-- The uniquely projection-normalized coefficient identification, including completion.
Source: blueprint dual-Tate compatibility, Steps 1--2
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
def podReindexingCoefficient {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (podReindexingCoefficient_existsUnique l E g).exists.choose

/-- Reindex modules and transport their actions by the specified inverse coefficient map.
Source: blueprint dual-Tate compatibility, Steps 1--2
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ) :=
  isoSectionwiseModuleInverseImage.{u,u} g
    (RY := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (podReindexingRing l E Y s))
    (RX := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (podReindexingRing l E X s))
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).mapIso
      (podReindexingCoefficient l E g s)).hom

/-- The ordinary unbounded derived category at either stage, with standard localization.
Source: blueprint dual-Tate compatibility, Steps 1--2
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingDerived (W : Scheme.{u}) (s : Option ℕ) :=
  @DerivedCategory (podReindexingModules l E W s) _ _ (HasDerivedCategory.standard.{u+1,u+2} _)

/-- Ordinary completed-ring inverse image, or finite inverse image, by exact termwise descent.
Source: blueprint dual-Tate compatibility, Steps 1--2
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingDerivedFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (s : Option ℕ) : podReindexingDerived l E Y s ⥤ podReindexingDerived l E X s :=
  letI := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E Y s)
  letI := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E X s)
  (podReindexingFunctor l E g s).mapDerivedCategory

/-- The recorded product Hom complex, without changing its coefficient or site universe.
Source: Stacks Tag 0A8X (blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingHom (W : Scheme.{u}) (s : Option ℕ) :=
  homComplexFunctor.{u+1,u,u+1,u+1} (J := ProEt.topology W) (R := podReindexingRing l E W s)

/-- The recorded ordinary unbounded derived internal Hom at the chosen coefficient stage.
Source: Stacks Tag 08J7 (blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingDerivedHom (W : Scheme.{u}) (s : Option ℕ) :=
  @derivedInternalHomOfUniverses.{u+1,u,u,u+2} _ _ (ProEt.topology W) _ _
    (podReindexingRing l E W s) (HasDerivedCategory.standard.{u+1,u+2} _)

/-- The exact termwise functor on actual cochain complexes.
Source: blueprint dual-Tate compatibility, Step 1
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingComplexFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (s : Option ℕ) :=
  (podReindexingFunctor l E g s).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The existing sheaf tensor product with its right input fixed.
Source: Stacks Tag 03EL (blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingTensor (W : Scheme.{u}) (s : Option ℕ)
    (M N : podReindexingModules l E W s) : podReindexingModules l E W s :=
  (SheafOfModules.siteSheafTensorRight.{u,u+1,u+1,u+1}
    (J := ProEt.topology W) (A := podReindexingRing l E W s) N).obj M

/-- The canonical localization functor with the recorded standard derived-category size.
Source: Stacks Tag 05RU (blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingQ (W : Scheme.{u}) (s : Option ℕ) :
    CochainComplex (podReindexingModules l E W s) ℤ ⥤ podReindexingDerived l E W s :=
  @DerivedCategory.Q.{u+2,u+1,u+2} _ _ _ (HasDerivedCategory.standard.{u+1,u+2} _)

/-- Localization intertwines the exact termwise inverse image and its derived functor.
Source: Stacks Tag 05RU (blueprint: lem-pod-reindexing-hom-resolution-model). -/
abbrev podReindexingDerivedFactors {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (s : Option ℕ) :
    podReindexingQ l E Y s ⋙ podReindexingDerivedFunctor l E g s ≅
      podReindexingComplexFunctor l E g s ⋙ podReindexingQ l E X s :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard.{u+1,u+2} _)
    _ _ _ (HasDerivedCategory.standard.{u+1,u+2} _) (podReindexingFunctor l E g s) _ _ _

/-- The canonical Hom resolution comparison: the localization factorization followed by
inversion of the map induced by I → I₀(I). No arbitrary model isomorphism is selected.
Source: Stacks Tags 08J7 and 0A95
(blueprint: lem-pod-reindexing-hom-resolution-model). -/
def podReindexingHomModel (W : Scheme.{u}) (s : Option ℕ)
    (K I : CochainComplex (podReindexingModules l E W s) ℤ) [I.IsKInjective] :
    (podReindexingDerivedHom l E W s).obj
        (op ((podReindexingQ l E W s).obj K), (podReindexingQ l E W s).obj I) ≅
      (podReindexingQ l E W s).obj
        (homComplex.{u+1,u,u+1,u+1} (R := podReindexingRing l E W s) K I) :=
  letI := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E W s)
  letI : IsGrothendieckAbelian.{u+1} (podReindexingModules l E W s) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology W) (podReindexingRing l E W s)).1
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{u+1} (podReindexingModules l E W s)
  let η₀ := CochainComplex.toKInjectiveResolution.{u+1} (podReindexingModules l E W s)
  let e := Localization.fac _
    (derivedInternalHomOfUniverses_inverts.{u+1,u,u,u+2}
      (ProEt.topology W) (podReindexingRing l E W s) I₀ η₀
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u+1} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u+1} _ M⟩))
    ((DerivedCategory.Q.{u+2,u+1,u+2}).op.prod DerivedCategory.Q.{u+2,u+1,u+2})
  letI : QuasiIso (η₀.app I) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u+1} _ I).2
  letI : (I₀.obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u+1} _ I
  let f := ((podReindexingHom l E W s).obj (op K)).map (η₀.app I)
  letI : QuasiIso f := by
    have h := quasiIso_homComplex_map.{u+1,u} (J := ProEt.topology W)
      (R := podReindexingRing l E W s)
      (I' := I) (I := I₀.obj I) (η₀.app I) (𝟙 K)
    simpa [f] using h
  letI : IsIso (DerivedCategory.Q.{u+2,u+1,u+2}.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso.{u+2,u+1,u+2} _ f).mpr inferInstance
  e.app (op K, I) ≪≫ (asIso (DerivedCategory.Q.{u+2,u+1,u+2}.map f)).symm

section

attribute [local irreducible] podReindexingCoefficient
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue
  SheafOfModules.ScalarHomOrdinary.tensorIsoSite

/-- Tensor and ordinary sheaf-Hom comparisons, normalized on local sections.
Source: the tensor and slice-Hom parts of the proof of
`lem-pod-reindexing-hom-resolution-model`, Steps 4 and 7--8.
(blueprint: lem-pod-reindexing-tensor-hom-data).

The proof is the sheafified sectionwise tensor and slice-Hom comparison of
`inverseImage_tensor_hom_iso`, with the coefficient isomorphism transported by
`podReindexingCoefficient`; the displayed section equations are the normalizations. -/
theorem podReindexing_tensor_hom_data {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u+1} X.ProEt] [EssentiallySmall.{u+1} Y.ProEt] (s : Option ℕ) :
    ∃ σ : ∀ M N : podReindexingModules l E Y s,
        (podReindexingFunctor l E g s).obj (podReindexingTensor l E Y s M N) ≅
          podReindexingTensor l E X s ((podReindexingFunctor l E g s).obj M)
            ((podReindexingFunctor l E g s).obj N),
    ∃ η : ∀ M N : podReindexingModules l E Y s,
        (podReindexingFunctor l E g s).obj (SheafOfModules.homObj
          (J := ProEt.topology Y) (R := podReindexingRing l E Y s) M N) ≅
          SheafOfModules.homObj (J := ProEt.topology X) (R := podReindexingRing l E X s)
            ((podReindexingFunctor l E g s).obj M)
            ((podReindexingFunctor l E g s).obj N),
      (∀ (M N : podReindexingModules l E Y s) (U : X.ProEt)
          (a : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
          (b : N.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (σ M N).hom.val.app (op U)
            (purTensorSection (podReindexingRing l E Y s) M N
              ((proEtaleIsoPostcompose g).obj U) a b) =
          purTensorSection (podReindexingRing l E X s)
            ((podReindexingFunctor l E g s).obj M)
            ((podReindexingFunctor l E g s).obj N) U a b) ∧
      (∀ (M N : podReindexingModules l E Y s) (U V : X.ProEt) (a : V ⟶ U)
          (f : (SheafOfModules.homObj (J := ProEt.topology Y)
            (R := podReindexingRing l E Y s) M N).val.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj V))),
        ((η M N).hom.val.app (op U) f).app (op (Over.mk a)) x =
          f.app (op (Over.mk ((proEtaleIsoPostcompose g).map a))) x) := by
  let B := proEtaleIsoPostcompose g
  let R := podReindexingRing l E Y s
  let S := podReindexingRing l E X s
  let c := podReindexingCoefficient l E g s
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let a : W.obj S ≅
      (B.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology Y)).obj
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    (W.mapIso c).symm
  let F := SheafOfModules.pushforward.{u + 1} (F := B) (J := ProEt.topology X)
    (K := ProEt.topology Y) a.hom
  have hinv : inv (W.map c.hom) = W.map c.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← W.map_comp, c.hom_inv_id, W.map_id]
  -- Abstract the scalar morphism before transporting it: sections stay definitionally fixed.
  let P (p : W.obj S ⟶
      (B.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology Y)).obj
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) : Prop :=
    let T := SheafOfModules.pushforward.{u + 1} (F := B) p
    ∃ σ : ∀ M N : podReindexingModules l E Y s,
            T.obj (podReindexingTensor l E Y s M N) ≅
              podReindexingTensor l E X s (T.obj M)
                (T.obj N),
        ∃ η : ∀ M N : podReindexingModules l E Y s,
            T.obj (SheafOfModules.homObj
              (J := ProEt.topology Y) (R := podReindexingRing l E Y s) M N) ≅
              SheafOfModules.homObj (J := ProEt.topology X) (R := podReindexingRing l E X s)
                (T.obj M)
                (T.obj N),
          (∀ (M N : podReindexingModules l E Y s) (U : X.ProEt)
              (a : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
              (b : N.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
            (σ M N).hom.val.app (op U)
                (purTensorSection (podReindexingRing l E Y s) M N
                  ((proEtaleIsoPostcompose g).obj U) a b) =
              purTensorSection (podReindexingRing l E X s)
                (T.obj M)
                (T.obj N) U a b) ∧
          (∀ (M N : podReindexingModules l E Y s) (U V : X.ProEt) (a : V ⟶ U)
              (f : (SheafOfModules.homObj (J := ProEt.topology Y)
                (R := podReindexingRing l E Y s) M N).val.obj
                (op ((proEtaleIsoPostcompose g).obj U)))
              (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj V))),
            ((η M N).hom.val.app (op U) f).app (op (Over.mk a)) x =
              f.app (op (Over.mk ((proEtaleIsoPostcompose g).map a))) x)
  change P (inv (W.map c.hom))
  rw [hinv]
  dsimp only [P]
  have : B.IsEquivalence := (proEtaleIsoPostcompose_equivalence g).1
  have : B.IsCocontinuous (ProEt.topology X) (ProEt.topology Y) :=
    sectionwisePostcompose_cocontinuous g
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  obtain ⟨σ₀, _, hσ₀⟩ := SheafOfModules.sectionwiseTensorComparison B S R a
  let tR := SheafOfModules.ScalarHomOrdinary.tensorIsoSite R
  let tS := SheafOfModules.ScalarHomOrdinary.tensorIsoSite S
  let σ (M N : podReindexingModules l E Y s) :=
    F.mapIso (tR M N).symm ≪≫ σ₀ M N ≪≫ tS (F.obj M) (F.obj N)
  let η (M N : podReindexingModules l E Y s) :=
    PurHom.sheafPushHomIso B (ProEt.topology X) (ProEt.topology Y) R S c.inv M N
  refine ⟨σ, η, ?_, ?_⟩
  · intro M N U x y
    have hR := SheafOfModules.ScalarHomOrdinary.tensorIsoSite_inv_pure
      R M N (op (B.obj U)) x y
    have hS := SheafOfModules.ScalarHomOrdinary.tensorIsoSite_pure
      S (F.obj M) (F.obj N) (op U) x y
    change (tS (F.obj M) (F.obj N)).hom.val.app (op U)
      ((σ₀ M N).hom.val.app (op U)
        ((F.map (tR M N).inv).val.app (op U)
          (purTensorSection R M N (B.obj U) x y))) = _
    change (tS (F.obj M) (F.obj N)).hom.val.app (op U)
      ((σ₀ M N).hom.val.app (op U)
        ((tR M N).inv.val.app (op (B.obj U))
          (purTensorSection R M N (B.obj U) x y))) = _
    exact (congrArg (fun z ↦ (tS (F.obj M) (F.obj N)).hom.val.app (op U)
      ((σ₀ M N).hom.val.app (op U) z)) hR).trans
        ((congrArg ((tS (F.obj M) (F.obj N)).hom.val.app (op U))
          (hσ₀ M N (op U) x y)).trans hS)
  · intro M N U V f φ x
    exact PurHom.sheafPushHomIso_apply B (ProEt.topology X) (ProEt.topology Y)
      R S c.inv M N (op U) φ (op (Over.mk f)) x

end

/-- The canonical site round trip: compose the structure maps and cancel g and its inverse.
The components are identities on the underlying schemes.
Source: Stacks Tag 09A5 (blueprint: lem-pod-reindexing-hom-resolution-model). -/
def podReindexingSiteRoundTrip {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    proEtaleIsoPostcompose (inv g) ⋙ proEtaleIsoPostcompose g ≅ 𝟭 Y.ProEt :=
  (MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale (inv g)) (inferInstance : WeaklyEtale g)).symm ≪≫
    MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) Y
      (inv g ≫ g) (IsIso.inv_hom_id g)

attribute [local irreducible] HasDerivedCategory.standard
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue

private theorem podReindexingConstantRoundTrip {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A) ⟶
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
    (d : (isoSectionwiseInverseImage (inv g) CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A) ⟶
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
    (hc : ∀ (U : X.ProEt) (a : A), c.hom.app (op U)
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U)) a) =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op U) a)
    (hd : ∀ (U : Y.ProEt) (a : A), d.hom.app (op U)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose (inv g)).obj U)) a) =
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app (op U) a) :
    let := Functor.isContinuous_comp (proEtaleIsoPostcompose (inv g))
      (proEtaleIsoPostcompose g) (ProEt.topology Y) (ProEt.topology X) (ProEt.topology Y)
    (isoSectionwiseInverseImage (inv g) CommRingCat.{u + 1}).map c ≫ d =
      ((Functor.sheafPushforwardContinuousId' (podReindexingSiteRoundTrip g)
        CommRingCat.{u + 1} (ProEt.topology Y)).hom.app
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)) := by
  let B := proEtaleIsoPostcompose (inv g) ⋙ proEtaleIsoPostcompose g
  let := Functor.isContinuous_comp (proEtaleIsoPostcompose (inv g))
    (proEtaleIsoPostcompose g) (ProEt.topology Y) (ProEt.topology X) (ProEt.topology Y)
  let : B.IsCocontinuous (ProEt.topology Y) (ProEt.topology Y) :=
    Functor.IsCocontinuous.of_iso (podReindexingSiteRoundTrip g).symm
  let P := (Functor.const Y.ProEtᵒᵖ).obj A
  let e := (B.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology Y) (ProEt.topology Y)).symm.app P
  apply (cancel_epi e.inv).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (D := CommRingCat.{u + 1}) (ProEt.topology Y) _ _
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A).property
  have he : toSheafify (ProEt.topology Y) P ≫ e.inv.hom =
      B.op.whiskerLeft (toSheafify (ProEt.topology Y) P) := by
    exact (B.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology Y) P)
  change toSheafify (ProEt.topology Y) P ≫ (e.inv.hom ≫ _) =
    toSheafify (ProEt.topology Y) P ≫ (e.inv.hom ≫ _)
  rw [← Category.assoc, ← Category.assoc, he]
  ext U a
  change d.hom.app U (c.hom.app _
      ((toSheafify (ProEt.topology Y) P).app _ a)) =
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A).obj.map
      ((podReindexingSiteRoundTrip g).inv.app U.unop).op
        ((toSheafify (ProEt.topology Y) P).app _ a)
  exact (congrArg (fun x ↦ d.hom.app U x)
    (hc ((proEtaleIsoPostcompose (inv g)).obj U.unop) a)).trans <|
      (hd U.unop a).trans <| ConcreteCategory.congr_hom
        ((toSheafify (ProEt.topology Y) P).naturality
          ((podReindexingSiteRoundTrip g).inv.app U.unop).op) a

private theorem podReindexingCoefficientRoundTrip {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (s : Option ℕ) :
    letI := Functor.isContinuous_comp (proEtaleIsoPostcompose (inv g))
      (proEtaleIsoPostcompose g) (ProEt.topology Y) (ProEt.topology X) (ProEt.topology Y)
    (isoSectionwiseInverseImage (inv g) CommRingCat.{u + 1}).map
        (podReindexingCoefficient l E g s).hom ≫
      (podReindexingCoefficient l E (inv g) s).hom =
      (Functor.sheafPushforwardContinuousId' (podReindexingSiteRoundTrip g)
        CommRingCat.{u + 1} (ProEt.topology Y)).hom.app (podReindexingRing l E Y s) := by
  let := Functor.isContinuous_comp (proEtaleIsoPostcompose (inv g))
    (proEtaleIsoPostcompose g) (ProEt.topology Y) (ProEt.topology X) (ProEt.topology Y)
  have hfinite (n : ℕ) := podReindexingConstantRoundTrip g
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (podReindexingCoefficient l E g (some n)).hom
    (podReindexingCoefficient l E (inv g) (some n)).hom (by
      intro U a
      have h := (podReindexingCoefficient_existsUnique l E g).exists.choose_spec.1 n
      exact (congrArg (fun f ↦ f.hom.app (op U)
        ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
            (op ((proEtaleIsoPostcompose g).obj U)) a)) h).trans
        ((isoSectionwiseConstantMap_existsUnique.{u,u} g _).exists.choose_spec U a)) (by
      intro U a
      have h := (podReindexingCoefficient_existsUnique l E (inv g)).exists.choose_spec.1 n
      exact (congrArg (fun f ↦ f.hom.app (op U)
        ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
            (op ((proEtaleIsoPostcompose (inv g)).obj U)) a)) h).trans
        ((isoSectionwiseConstantMap_existsUnique.{u,u} (inv g) _).exists.choose_spec U a))
  cases s with
  | some n => exact hfinite n
  | none =>
    let WY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    apply WY.map_injective
    apply limit.hom_ext
    intro j
    obtain ⟨n⟩ := j
    have hg := (podReindexingCoefficient_existsUnique l E g).exists.choose_spec.2 n
    have hi := (podReindexingCoefficient_existsUnique l E (inv g)).exists.choose_spec.2 n
    change (podReindexingCoefficient l E g none).hom ≫ _ =
      _ ≫ (podReindexingCoefficient l E g (some n)).hom at hg
    change (podReindexingCoefficient l E (inv g) none).hom ≫ _ =
      _ ≫ (podReindexingCoefficient l E (inv g) (some n)).hom at hi
    have h : ((isoSectionwiseInverseImage (inv g) CommRingCat.{u + 1}).map
          (podReindexingCoefficient l E g none).hom ≫
        (podReindexingCoefficient l E (inv g) none).hom) ≫
          completedIntegralCommRingProjectionUnrestricted l E Y n =
        (Functor.sheafPushforwardContinuousId' (podReindexingSiteRoundTrip g)
          CommRingCat.{u + 1} (ProEt.topology Y)).hom.app (podReindexingRing l E Y none) ≫
            completedIntegralCommRingProjectionUnrestricted l E Y n := by
      erw [Category.assoc, hi, ← Category.assoc, ← Functor.map_comp, hg,
        Functor.map_comp, Category.assoc, hfinite n]
      exact (Functor.sheafPushforwardContinuousId' (podReindexingSiteRoundTrip g)
        CommRingCat.{u + 1} (ProEt.topology Y)).hom.naturality
          (completedIntegralCommRingProjectionUnrestricted l E Y n)
    exact congrArg WY.map h

/-- The same coefficient identity with an arbitrary specified inverse. This form avoids
rewriting a morphism underneath its dependent `IsIso` instance. -/
private theorem podReindexingCoefficientRoundTripWithInverse {X Y : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ X) [IsIso g] [IsIso f] (hf : f = inv g) (s : Option ℕ) :
    letI := Functor.isContinuous_comp (proEtaleIsoPostcompose f)
      (proEtaleIsoPostcompose g) (ProEt.topology Y) (ProEt.topology X) (ProEt.topology Y)
    let e : proEtaleIsoPostcompose f ⋙ proEtaleIsoPostcompose g ≅ 𝟭 Y.ProEt :=
      (MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale f) (inferInstance : WeaklyEtale g)).symm ≪≫
        MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) Y
          (f ≫ g) (by rw [hf]; exact IsIso.inv_hom_id g)
    (isoSectionwiseInverseImage f CommRingCat.{u + 1}).map
        (podReindexingCoefficient l E g s).hom ≫
      (podReindexingCoefficient l E f s).hom =
        (Functor.sheafPushforwardContinuousId' e CommRingCat.{u + 1}
          (ProEt.topology Y)).hom.app (podReindexingRing l E Y s) := by
  subst f
  exact podReindexingCoefficientRoundTrip l E g s

/-- The derived equivalence obtained from the exact module equivalence. Its unit and
counit are the localizations of the termwise module unit and counit, by the existing
Equivalence.mapDerivedCategory construction.
Source: Stacks Tag 05RU (blueprint: lem-pod-reindexing-hom-resolution-model). -/
def podReindexingLiftedEquivalence {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ)
    (e : podReindexingModules l E Y s ≌ podReindexingModules l E X s)
    (hF : e.functor = podReindexingFunctor l E g s)
    (hG : e.inverse = podReindexingFunctor l E (inv g) s) :
    podReindexingDerived l E Y s ≌ podReindexingDerived l E X s :=
  letI := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E Y s)
  letI := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E X s)
  letI : e.functor.Additive := hF.symm ▸ inferInstance
  letI : e.inverse.Additive := hG.symm ▸ inferInstance
  e.mapDerivedCategory

private theorem podReindexingDerivedCongr
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

section

attribute [local irreducible] isoSectionwiseModuleInverseImage sfIntrinsicPullback

private theorem podReindexingFiniteComparison {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    Nonempty (podReindexingDerivedFunctor l E g (some n) ≅ finiteDerivedPullback l E n g) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let e := (AlgebraicGeometry.ProEtale.finiteSectionwiseAdjunction.{u,u} l E g n).leftAdjointUniq
    (sfIntrinsicConstantModuleAdjunction g A)
  let WX := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have hc : WX.mapIso (podReindexingCoefficient l E g (some n)) =
      asIso (AlgebraicGeometry.ProEtale.inverseImageFiniteCoefficientMap.{u,u} l E g n) := by
    apply Iso.ext
    exact (podReindexingCoefficient_existsUnique l E g).exists.choose_spec.1 n
  have hF : podReindexingFunctor l E g (some n) =
      AlgebraicGeometry.ProEtale.inverseImageFiniteModules.{u,u} l E g n :=
    congrArg (fun c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (podReindexingRing l E Y (some n))) ≅
        WX.obj (podReindexingRing l E X (some n)) ↦
      isoSectionwiseModuleInverseImage.{u,u} g c.hom) hc
  let := HasDerivedCategory.standard.{u + 1,u + 2} (podReindexingModules l E Y (some n))
  let := HasDerivedCategory.standard.{u + 1,u + 2} (podReindexingModules l E X (some n))
  let : (sfIntrinsicPullback A g).Additive := sfIntrinsicPullback_additive A g
  let : PreservesFiniteLimits (sfIntrinsicPullback A g) :=
    sfIntrinsicPullback_preservesFiniteLimits A g
  let : PreservesFiniteColimits (sfIntrinsicPullback A g) :=
    sfIntrinsicPullback_preservesFiniteColimits A g
  let e' : podReindexingFunctor l E g (some n) ≅ sfIntrinsicPullback A g := eqToIso hF ≪≫ e
  change Nonempty ((podReindexingFunctor l E g (some n)).mapDerivedCategory ≅
    (sfIntrinsicPullback A g).mapDerivedCategory)
  exact ⟨Functor.mapDerivedCategoryNatIso e'⟩

end

private theorem podRestrictionSource
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{z} R) {U V : C} (h : U = V) :
    (ModuleCat.restrictScalars (R.map (eqToHom h).op).hom).obj (M.obj (op U)) =
      M.obj (op V) := by
  subst V
  simp only [eqToHom_refl, op_id, R.map_id]
  rfl

private theorem podRestrictionApply
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{z} R) {U V : C} (h : U = V) (x : M.obj (op V)) :
    HEq (M.map (eqToHom h).op x) x := by
  subst V
  rw [eqToHom_refl, op_id, M.map_id]
  exact HEq.rfl

private theorem podRestrictScalarsIdHEq
    {R : Type w} [Ring R] (f : R →+* R) (hf : f = RingHom.id R) (M : ModuleCat.{z} R) :
    HEq ((ModuleCat.restrictScalarsId' f hf).inv.app M) (𝟙 M) := by
  subst f
  exact HEq.rfl

private theorem podRestrictionIdHEq
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{z} R) {U V : C} (h : U = V) :
    HEq (M.map (eqToHom h).op) (𝟙 (M.obj (op V))) := by
  subst V
  rw [eqToHom_refl, op_id, M.map_id]
  exact podRestrictScalarsIdHEq _ _ _

private theorem podModuleHomIdHEq
    {R : Type w} [Ring R] {M N : ModuleCat.{z} R} (h : M = N) (f : M ⟶ N)
    (hf : ∀ x : M, HEq (f x) x) : HEq f (𝟙 N) := by
  subst N
  apply heq_of_eq
  ext x
  exact eq_of_heq (hf x)

private theorem podModuleIdentityCongr
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{z} R) {U V : C} (h : U = V) :
    HEq (𝟙 (M.obj (op U))) (𝟙 (M.obj (op V))) := by
  subst V
  exact HEq.rfl

private theorem podReindexingModuleRoundTrip {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (s : Option ℕ) :
    ∃ (e : podReindexingModules l E Y s ≌ podReindexingModules l E X s)
      (_hF : e.functor = podReindexingFunctor l E g s)
      (_hG : e.inverse = podReindexingFunctor l E (inv g) s),
      (∀ (M : podReindexingModules l E Y s) (U : Y.ProEt)
          (a : M.val.obj (op U)),
        HEq ((e.unitIso.hom.app M).val.app (op U) a)
          (M.val.map ((podReindexingSiteRoundTrip g).hom.app U).op a)) ∧
      (∀ (M : podReindexingModules l E X s) (U : X.ProEt),
        HEq ((e.counitIso.hom.app M).val.app (op U))
          (M.val.map ((podReindexingSiteRoundTrip (inv g)).inv.app U).op)) := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let α : F ⋙ G ≅ 𝟭 X.ProEt :=
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale g) (inferInstance : WeaklyEtale (inv g))).symm ≪≫
      MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) X
        (g ≫ inv g) (IsIso.hom_inv_id g)
  let E₀ : X.ProEt ≌ Y.ProEt :=
    { functor := F
      inverse := G
      unitIso := α.symm
      counitIso := podReindexingSiteRoundTrip g
      functor_unitIso_comp U := by
        apply MorphismProperty.Over.Hom.ext
        change (𝟙 U.left ≫ 𝟙 U.left) ≫ (𝟙 U.left ≫ 𝟙 U.left) = 𝟙 U.left
        simp only [Category.id_comp] }
  let RY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (podReindexingRing l E Y s)
  let RX := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (podReindexingRing l E X s)
  let WX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let WY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c := WX.mapIso (podReindexingCoefficient l E g s)
  let d := WY.mapIso (podReindexingCoefficient l E (inv g) s)
  let φ := inv c.hom
  let ψ := inv d.hom
  let := Functor.isContinuous_comp G F (ProEt.topology Y)
    (ProEt.topology X) (ProEt.topology Y)
  let := Functor.isContinuous_comp F G (ProEt.topology X)
    (ProEt.topology Y) (ProEt.topology X)
  let τY := (Functor.sheafPushforwardContinuousId' (podReindexingSiteRoundTrip g)
    RingCat.{u + 1} (ProEt.topology Y)).app RY
  let τX := (Functor.sheafPushforwardContinuousId' α
    RingCat.{u + 1} (ProEt.topology X)).app RX
  have hY : (isoSectionwiseInverseImage (inv g) RingCat.{u + 1}).map c.hom ≫ d.hom =
      τY.hom := congrArg WY.map (podReindexingCoefficientRoundTrip l E g s)
  have hX : (isoSectionwiseInverseImage g RingCat.{u + 1}).map d.hom ≫ c.hom =
      τX.hom := by
    exact congrArg WX.map (podReindexingCoefficientRoundTripWithInverse l E
      (inv g) g (IsIso.inv_inv (f := g)).symm s)
  have hy : ψ ≫ (isoSectionwiseInverseImage (inv g) RingCat.{u + 1}).map φ = τY.inv := by
    simpa only [φ, ψ, IsIso.Iso.inv_hom, Iso.trans_inv, Functor.mapIso_inv] using
      congrArg Iso.inv (Iso.ext hY :
      ((isoSectionwiseInverseImage (inv g) RingCat.{u + 1}).mapIso c ≪≫ d) = τY)
  have hx : φ ≫ (isoSectionwiseInverseImage g RingCat.{u + 1}).map ψ = τX.inv := by
    simpa only [φ, ψ, IsIso.Iso.inv_hom, Iso.trans_inv, Functor.mapIso_inv] using
      congrArg Iso.inv (Iso.ext hX :
      ((isoSectionwiseInverseImage g RingCat.{u + 1}).mapIso d ≪≫ c) = τX)
  have H₁ : Functor.whiskerRight (NatTrans.op E₀.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    exact congrArg (fun f ↦ f.hom) hy.symm
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E₀.unit) RX.obj = 𝟙 RX.obj := by
    change (φ ≫ (isoSectionwiseInverseImage g RingCat.{u + 1}).map ψ).hom ≫ τX.hom.hom = _
    rw [hx]
    exact congrArg (fun f ↦ f.hom) τX.inv_hom_id
  let e : SheafOfModules.{u + 1} RY ≌ SheafOfModules.{u + 1} RX :=
    SheafOfModules.pushforwardPushforwardEquivalence E₀ (S := RX) (R := RY) φ ψ H₁ H₂
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro M U a
    exact HEq.rfl
  · intro M U
    have hrestrict (f : X ⟶ Y) [IsIso f] (hf : f = g)
        (hfg : f ≫ inv g = 𝟙 X) :
        HEq (M.val.map (α.inv.app U).op)
          (M.val.map (((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale f)
            (inferInstance : WeaklyEtale (inv g))).symm ≪≫
            MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) X
              (f ≫ inv g) hfg).inv.app U).op) := by
      subst f
      exact HEq.rfl
    have hsite : (F ⋙ G).obj U = U := by
      rcases U with ⟨⟨A, B, f⟩, hf⟩
      change (⟨⟨A, B, (f ≫ g) ≫ inv g⟩, _⟩ : X.ProEt) = ⟨⟨A, B, f⟩, hf⟩
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    let L : X.ProEt ⥤ Scheme.{u} :=
      MorphismProperty.Over.forget @WeaklyEtale ⊤ X ⋙ CategoryTheory.Over.forget X
    have hα : α.hom.app U = eqToHom hsite := by
      apply MorphismProperty.Over.Hom.ext
      change (𝟙 U.left ≫ 𝟙 U.left) = L.map (eqToHom hsite)
      have h := (eqToHom_map L hsite).symm
      change eqToHom (rfl : U.left = U.left) = L.map (eqToHom hsite) at h
      exact (Category.id_comp _).trans h
    have hαinv : α.inv.app U = eqToHom hsite.symm := by
      apply MorphismProperty.Over.Hom.ext
      change (𝟙 U.left ≫ 𝟙 U.left) = L.map (eqToHom hsite.symm)
      have h := (eqToHom_map L hsite.symm).symm
      change eqToHom (rfl : U.left = U.left) = L.map (eqToHom hsite.symm) at h
      exact (Category.id_comp _).trans h
    have hsource : (e.functor.obj (e.inverse.obj M)).val.obj (op U) =
        M.val.obj (op U) := calc
      _ = ((SheafOfModules.pushforward (F := F ⋙ G) τX.inv).obj M).val.obj (op U) :=
        congrArg (fun ρ : RX ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u + 1}
            (ProEt.topology X) (ProEt.topology X)).obj RX ↦
          ((SheafOfModules.pushforward.{u + 1} ρ).obj M).val.obj (op U)) hx
      _ = _ := by
        change (ModuleCat.restrictScalars (RX.obj.map (α.hom.app U).op).hom).obj
          (M.val.obj (op ((F ⋙ G).obj U))) = M.val.obj (op U)
        rw [hα]
        exact podRestrictionSource M.val hsite
    have hid : HEq ((e.counitIso.hom.app M).val.app (op U))
        (𝟙 (M.val.obj (op U))) := by
      apply podModuleHomIdHEq hsource
      intro x
      change HEq (M.val.map (α.inv.app U).op x) x
      rw [hαinv]
      exact podRestrictionApply M.val hsite.symm x
    have hm : HEq ((e.counitIso.hom.app M).val.app (op U))
        (M.val.map (α.inv.app U).op) := by
      apply hid.trans
      apply (podModuleIdentityCongr M.val hsite.symm).trans
      rw [hαinv]
      exact (podRestrictionIdHEq M.val hsite.symm).symm
    exact hm.trans (hrestrict (inv (inv g)) IsIso.inv_inv (IsIso.inv_hom_id (inv g)))

/-- Coefficient and action round trips, identity shift components, and termwise derived
unit and counit. The finite-stage functor agrees with the specified finite pullback.
Source: blueprint dual-Tate compatibility, Steps 1--2; Stacks Tags 09A5 and 05RU
(blueprint: lem-pod-reindexing-hom-resolution-model).

Proof (node Steps 3 and 11): the finite scalar maps and their reverses are identities
on constants; the completed composites have the same projections as the canonical
site round trip, so they are equal by the inverse-limit universal property. Thus
transporting the scalar action twice restores it. The module unit and counit are the
original restrictions along the identity-on-schemes site round trips. Apply these
maps in each cochain degree. Their naturality makes them chain maps and the module
triangle identities hold degreewise. Localize these termwise maps; exactness inverts
quasi-isomorphisms and gives the derived equivalence with the displayed unit/counit.
The shifted term is F(K^(i+n)) and the differential is (-1)^n F(d), so the comparison
is identity in every degree. Finally the finite coefficient identification is the
canonical one, hence this is precisely finiteDerivedPullback, whose definition is
exact termwise inverse image. The completed assertion is ordinary inverse image;
no quotient-tower derived-completion comparison is invoked. -/
theorem podReindexing_roundTrip_shift {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (s : Option ℕ) :
    (∀ (U : Y.ProEt)
        (a : (podReindexingRing l E Y s).obj.obj
          (op ((proEtaleIsoPostcompose g).obj ((proEtaleIsoPostcompose (inv g)).obj U)))),
      ((podReindexingCoefficient l E (inv g) s).hom.hom.app (op U))
        (((podReindexingCoefficient l E g s).hom.hom.app
          (op ((proEtaleIsoPostcompose (inv g)).obj U))) a) =
        (podReindexingRing l E Y s).obj.map
          ((podReindexingSiteRoundTrip g).inv.app U).op a) ∧
    (∃ (e : podReindexingModules l E Y s ≌ podReindexingModules l E X s)
        (hF : e.functor = podReindexingFunctor l E g s)
        (hG : e.inverse = podReindexingFunctor l E (inv g) s),
      (∀ (M : podReindexingModules l E Y s) (U : Y.ProEt)
          (a : M.val.obj (op U)),
        HEq ((e.unitIso.hom.app M).val.app (op U) a)
          (M.val.map ((podReindexingSiteRoundTrip g).hom.app U).op a)) ∧
      (∀ (M : podReindexingModules l E X s) (U : X.ProEt),
        HEq ((e.counitIso.hom.app M).val.app (op U))
          (M.val.map ((podReindexingSiteRoundTrip (inv g)).inv.app U).op)) ∧
      (podReindexingLiftedEquivalence l E g s e hF hG).functor =
        podReindexingDerivedFunctor l E g s ∧
      (podReindexingLiftedEquivalence l E g s e hF hG).inverse =
        podReindexingDerivedFunctor l E (inv g) s) ∧
    (∀ (K : CochainComplex (podReindexingModules l E Y s) ℤ) (n i : ℤ),
      (((podReindexingComplexFunctor l E g s).commShiftIso n).hom.app K).f i = 𝟙 _) ∧
    (∀ n : ℕ,
      Nonempty (podReindexingDerivedFunctor l E g (some n) ≅ finiteDerivedPullback l E n g)) := by
  refine ⟨?_, ?_, ?_, podReindexingFiniteComparison l E g⟩
  · intro U a
    exact congrArg (fun f ↦ f.hom.app (op U) a)
      (podReindexingCoefficientRoundTrip l E g s)
  · obtain ⟨e, hF, hG, hη, hε⟩ := podReindexingModuleRoundTrip l E g s
    let : e.functor.Additive := hF.symm ▸ inferInstance
    let : e.inverse.Additive := hG.symm ▸ inferInstance
    refine ⟨e, hF, hG, hη, hε, ?_, ?_⟩
    · change e.functor.mapDerivedCategory = _
      exact podReindexingDerivedCongr hF
    · change e.inverse.mapDerivedCategory = _
      exact podReindexingDerivedCongr hG
  · intro K n i
    exact Functor.mapHomologicalComplex_commShiftIso_hom_app_f _ K n i

/-- Exact module equivalence and preservation of resolutions at finite and completed stages.
The inverse is reverse reindexing, including its transported module action.
Source: blueprint dual-Tate compatibility, Steps 1--2; Stacks Tags 03EL and 079I
(blueprint: lem-pod-reindexing-hom-resolution-model).

Proof (node Steps 1--6): postcompose site objects by g and its inverse; the original
restriction identifications give inverse module functors. They are additive, preserve
all existing small limits and colimits, and hence are exact. Tensor comparisons on
pure tensors transport exact tensor functors, so flatness is preserved. The direct-sum
total tensor comparison transports the test against every acyclic complex, proving
K-flat preservation. For K-injectivity, transport any map from an acyclic complex to
I through the inverse equivalence, take its null homotopy, and reindex that homotopy.
Exactness preserves quasi-isomorphisms, so both sorts of resolution remain resolutions.
Use lem-weil-proetale-isomorphism-inverse-image, lem-pur-isomorphism-inverse-image-tensor-hom,
def-pc-flat-sheaf-modules, def-pc-kflat-complex and def-pur-kinjective-complex. -/
theorem podReindexing_resolution_preservation {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u+1} X.ProEt] [EssentiallySmall.{u+1} Y.ProEt] (s : Option ℕ) :
    (∃ e : podReindexingModules l E Y s ≌ podReindexingModules l E X s,
      e.functor = podReindexingFunctor l E g s ∧
      e.inverse = podReindexingFunctor l E (inv g) s) ∧
    (podReindexingFunctor l E g s).Additive ∧
    PreservesFiniteLimits (podReindexingFunctor l E g s) ∧
    PreservesFiniteColimits (podReindexingFunctor l E g s) ∧
    PreservesLimitsOfSize.{w,z} (podReindexingFunctor l E g s) ∧
    PreservesColimitsOfSize.{w,z} (podReindexingFunctor l E g s) ∧
    (∀ M : podReindexingModules l E Y s,
      SheafOfModules.IsFlatOnSite.{u+1,u,u+1,u+1} (J := ProEt.topology Y) (R := podReindexingRing
        l E Y s) M →
        SheafOfModules.IsFlatOnSite.{u+1,u,u+1,u+1} (J := ProEt.topology X) (R :=
          podReindexingRing l E X s)
          ((podReindexingFunctor l E g s).obj M)) ∧
    (∀ K : CochainComplex (podReindexingModules l E Y s) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u+1,u,u+1} (J := ProEt.topology Y) (R :=
        podReindexingRing l E Y s) K →
        CochainComplex.IsKFlatIndependentCoefficients.{u+1,u,u+1} (J := ProEt.topology X) (R :=
          podReindexingRing l E X s)
          (((podReindexingFunctor l E g s).mapHomologicalComplex (.up ℤ)).obj K)) ∧
    (∀ I : CochainComplex (podReindexingModules l E Y s) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
        (((podReindexingFunctor l E g s).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ (K L : CochainComplex (podReindexingModules l E Y s) ℤ) (a : K ⟶ L),
      QuasiIso a →
        QuasiIso (((podReindexingFunctor l E g s).mapHomologicalComplex (.up ℤ)).map a)) := by
  obtain ⟨e, hF, hG, _⟩ := (podReindexing_roundTrip_shift l E g s).2.1
  have hfe : (podReindexingFunctor l E g s).IsEquivalence := by
    rw [← hF]
    infer_instance
  let := hfe
  have hflat := isoSectionwiseModuleInverseImage_flat_kFlat g
    (podReindexingRing l E Y s) (podReindexingRing l E X s)
    (podReindexingCoefficient l E g s) (podReindexingFunctor l E g s) rfl
  refine ⟨⟨e, hF, hG⟩, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hflat.1, hflat.2, ?_, ?_⟩
  · intro I hI
    let := hI
    have : e.inverse.Additive := hG.symm ▸ inferInstance
    have : PreservesFiniteLimits e.inverse := hG.symm ▸ inferInstance
    have : PreservesFiniteColimits e.inverse := hG.symm ▸ inferInstance
    have adj₀ : e.inverse ⊣ podReindexingFunctor l E g s := by
      rw [← hF]
      exact e.symm.toAdjunction
    exact CochainComplex.isKInjective_map_of_adjunction
      (podReindexingFunctor l E g s) adj₀ I
  · intro K L a ha
    let := ha
    infer_instance

/-- Reindexing local families commutes with precomposition and postcomposition. -/
private theorem podReindexingHomNaturality {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (s : Option ℕ)
    (η : ∀ M N : podReindexingModules l E Y s,
      (podReindexingFunctor l E g s).obj (SheafOfModules.homObj
        (J := ProEt.topology Y) (R := podReindexingRing l E Y s) M N) ≅
      SheafOfModules.homObj (J := ProEt.topology X) (R := podReindexingRing l E X s)
        ((podReindexingFunctor l E g s).obj M)
        ((podReindexingFunctor l E g s).obj N))
    (hη : ∀ (M N : podReindexingModules l E Y s) (U V : X.ProEt) (a : V ⟶ U)
      (f : (SheafOfModules.homObj (J := ProEt.topology Y)
        (R := podReindexingRing l E Y s) M N).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj V))),
      ((η M N).hom.val.app (op U) f).app (op (Over.mk a)) x =
        f.app (op (Over.mk ((proEtaleIsoPostcompose g).map a))) x)
    {M M' N N' : podReindexingModules l E Y s} (a : M' ⟶ M) (b : N ⟶ N') :
    (podReindexingFunctor l E g s).map
        (SheafOfModules.homObjMap (R := podReindexingRing l E Y s) a b) ≫
      (η M' N').hom = (η M N).hom ≫
        SheafOfModules.homObjMap (R := podReindexingRing l E X s)
          ((podReindexingFunctor l E g s).map a) ((podReindexingFunctor l E g s).map b) := by
  let R := podReindexingRing l E Y s
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext f : 2
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  obtain ⟨U⟩ := U
  obtain ⟨⟨V, ⟨⟨⟩⟩, v⟩⟩ := V
  change ((η M' N').hom.val.app (op U)
    ((SheafOfModules.homObjMap (R := R) a b).val.app
      (op ((proEtaleIsoPostcompose g).obj U)) f)).app (op (Over.mk v)) x = _
  rw [hη]
  change _ = (b.val.app (op ((proEtaleIsoPostcompose g).obj V)))
    (((η M N).hom.val.app (op U) f).app (op (Over.mk v))
      (a.val.app (op ((proEtaleIsoPostcompose g).obj V)) x))
  rw [hη]
  rfl

/-- The inverse resolution model is the ordinary-to-derived Hom comparison. -/
private theorem podReindexingHomModel_inv (W : Scheme.{u}) (s : Option ℕ)
    (K I : CochainComplex (podReindexingModules l E W s) ℤ) (hI : I.IsKInjective) :
    (@podReindexingHomModel l _ E _ _ _ W s K I hI).inv =
      @ringedSiteOrdinaryHomComparison.{u+1,u,u+1,u+2} _ _ (ProEt.topology W) _ _
        (podReindexingRing l E W s) (HasDerivedCategory.standard.{u+1,u+2} _) K I := by
  rw [CategoryTheory.ordinaryHomComparison_eq.{u+1,u,u+1,u+2}]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The actual Hom-complex and derived localization comparisons, with their
projection, naturality, quasi-isomorphism, and resolution-model laws.
Source: the Hom-complex and localization parts of the proof of
`lem-pod-reindexing-hom-resolution-model`, Steps 7--10.
(blueprint: lem-pod-reindexing-derived-hom-data).

The supplied comparison is required to act on local families by reindexing. Evaluating
on every site object, slice object and section therefore proves its naturality in
both module arguments. Exact reindexing preserves integer products. The generic
product-Hom comparison applies this natural family to each product projection;
its two-term differential calculation gives an actual natural chain isomorphism.
Quasi-isomorphism invariance into K-injectives and exact reindexing prove the
quasi-isomorphism clause.

For descent, use the fixed functorial K-injective replacement on the source site.
Its augmentation becomes invertible after localization. The ordinary-to-derived
Hom comparisons on both resolved targets are invertible, since reindexing preserves
K-injectivity. The generic resolution-descent lemma then gives a natural derived
isomorphism and its comparison equation. The ordinary comparison is the localized
augmentation followed by the inverse localization factorization, which is exactly
`podReindexingHomModel.inv`. Substitute these identities in the descent equation
and multiply by the source model isomorphism. This gives the displayed formula,
including the contravariant transport in the first argument. -/
theorem podReindexing_derived_hom_data {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u+1} X.ProEt] [EssentiallySmall.{u+1} Y.ProEt] (s : Option ℕ)
    (η : ∀ M N : podReindexingModules l E Y s,
      (podReindexingFunctor l E g s).obj (SheafOfModules.homObj
        (J := ProEt.topology Y) (R := podReindexingRing l E Y s) M N) ≅
      SheafOfModules.homObj (J := ProEt.topology X) (R := podReindexingRing l E X s)
        ((podReindexingFunctor l E g s).obj M)
        ((podReindexingFunctor l E g s).obj N))
    (hη : ∀ (M N : podReindexingModules l E Y s) (U V : X.ProEt) (a : V ⟶ U)
      (f : (SheafOfModules.homObj (J := ProEt.topology Y)
        (R := podReindexingRing l E Y s) M N).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj V))),
      ((η M N).hom.val.app (op U) f).app (op (Over.mk a)) x =
        f.app (op (Over.mk ((proEtaleIsoPostcompose g).map a))) x) :
    ∃ χ : ∀ (K I : CochainComplex (podReindexingModules l E Y s) ℤ)
        (_hI : I.IsKInjective),
        (podReindexingComplexFunctor l E g s).obj
            (homComplex.{u+1,u,u+1,u+1} (R := podReindexingRing l E Y s) K I) ≅
          homComplex.{u+1,u,u+1,u+1} (R := podReindexingRing l E X s)
            ((podReindexingComplexFunctor l E g s).obj K)
            ((podReindexingComplexFunctor l E g s).obj I),
    ∃ δ : podReindexingDerivedHom l E Y s ⋙ podReindexingDerivedFunctor l E g s ≅
        ((podReindexingDerivedFunctor l E g s).op.prod
          (podReindexingDerivedFunctor l E g s)) ⋙ podReindexingDerivedHom l E X s,
      (∀ (K I : CochainComplex (podReindexingModules l E Y s) ℤ)
          (hI : I.IsKInjective) (r p : ℤ),
        (χ K I hI).hom.f r ≫ homComplexπ.{u+1,u,u+1,u+1}
            (R := podReindexingRing l E X s)
            ((podReindexingComplexFunctor l E g s).obj K)
            ((podReindexingComplexFunctor l E g s).obj I) r p (p+r) rfl =
          (podReindexingFunctor l E g s).map
              (homComplexπ.{u+1,u,u+1,u+1}
                (R := podReindexingRing l E Y s) K I r p (p+r) rfl) ≫
            (η (K.X p) (I.X (p+r))).hom) ∧
      (∀ (K K' I I' : CochainComplex (podReindexingModules l E Y s) ℤ)
          (hI : I.IsKInjective) (hI' : I'.IsKInjective) (a : K' ⟶ K) (b : I ⟶ I'),
        (podReindexingComplexFunctor l E g s).map
            (((podReindexingHom l E Y s).map a.op).app I ≫
              ((podReindexingHom l E Y s).obj (op K')).map b) ≫ (χ K' I' hI').hom =
          (χ K I hI).hom ≫
            ((podReindexingHom l E X s).map
              ((podReindexingComplexFunctor l E g s).map a).op).app
              ((podReindexingComplexFunctor l E g s).obj I) ≫
            ((podReindexingHom l E X s).obj
              (op ((podReindexingComplexFunctor l E g s).obj K'))).map
              ((podReindexingComplexFunctor l E g s).map b)) ∧
      (∀ (K K' I I' : CochainComplex (podReindexingModules l E Y s) ℤ)
          (_hI : I.IsKInjective) (_hI' : I'.IsKInjective) (a : K' ⟶ K) (b : I ⟶ I'),
        QuasiIso a → QuasiIso b →
          QuasiIso ((podReindexingComplexFunctor l E g s).map
            (((podReindexingHom l E Y s).map a.op).app I ≫
              ((podReindexingHom l E Y s).obj (op K')).map b))) ∧
      (∀ (K I : CochainComplex (podReindexingModules l E Y s) ℤ)
          (hI : I.IsKInjective),
        ∃ hFI : CochainComplex.IsKInjective
            ((podReindexingComplexFunctor l E g s).obj I),
          δ.hom.app
              (op ((podReindexingQ l E Y s).obj K), (podReindexingQ l E Y s).obj I) =
            (podReindexingDerivedFunctor l E g s).map
                (@podReindexingHomModel l _ E _ _ _ Y s K I hI).hom ≫
              (podReindexingDerivedFactors l E g s).hom.app
                (homComplex.{u+1,u,u+1,u+1}
                  (R := podReindexingRing l E Y s) K I) ≫
              (podReindexingQ l E X s).map (χ K I hI).hom ≫
              (@podReindexingHomModel l _ E _ _ _ X s
                ((podReindexingComplexFunctor l E g s).obj K)
                ((podReindexingComplexFunctor l E g s).obj I) hFI).inv ≫
              ((podReindexingDerivedHom l E X s).mapIso
                (((podReindexingDerivedFactors l E g s).app K).op.prod
                  ((podReindexingDerivedFactors l E g s).app I).symm)).hom) := by
  let R := podReindexingRing l E Y s
  let S := podReindexingRing l E X s
  let F := podReindexingFunctor l E g s
  let FC := podReindexingComplexFunctor l E g s
  let Q := podReindexingQ l E Y s
  let QX := podReindexingQ l E X s
  let FD := podReindexingDerivedFunctor l E g s
  let H := podReindexingDerivedHom l E Y s
  let HX := podReindexingDerivedHom l E X s
  let := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u+1,u+2} (podReindexingModules l E X s)
  have hp := podReindexing_resolution_preservation.{u,0,0} l E g s
  let : PreservesLimitsOfSize.{0,0} F := hp.2.2.2.2.1
  have hγdata := CategoryTheory.bundledProductHomRestrictionComparison F
    (CategoryTheory.nativeHomInterface.{u+1,u,u+1} (ProEt.topology Y) R)
    (CategoryTheory.nativeHomInterface.{u+1,u,u+1} (ProEt.topology X) S) η
    (fun a b ↦ podReindexingHomNaturality l E g s η hη a b)
  let γ := hγdata.choose
  have hγ := hγdata.choose_spec
  let : IsGrothendieckAbelian.{u+1} (podReindexingModules l E Y s) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology Y) R).1
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{u+1} (podReindexingModules l E Y s)
  let η₀ := CochainComplex.toKInjectiveResolution.{u+1} (podReindexingModules l E Y s)
  have hFI (I : CochainComplex (podReindexingModules l E Y s) ℤ) (hI : I.IsKInjective) :
      CochainComplex.IsKInjective (FC.obj I) := hp.2.2.2.2.2.2.2.2.1 I hI
  have hδdata := CategoryTheory.homRestrictionDescent Q QX FD FC
    ((HomologicalComplex.quasiIso _ (.up ℤ)).op.prod
      (HomologicalComplex.quasiIso _ (.up ℤ)))
    (Functor.uncurry.obj (podReindexingHom l E Y s))
    (Functor.uncurry.obj (podReindexingHom l E X s)) H HX
    (podReindexingDerivedFactors l E g s) γ
    (RingedHomUniverses.ordinaryComparison.{u+1,u,u+1,u+2} (ProEt.topology Y) R)
    (RingedHomUniverses.ordinaryComparison.{u+1,u,u+1,u+2} (ProEt.topology X) S)
    I₀ η₀
    (by
      intro M
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u+1} _ M).2)
    (by
      intro L M
      have : (I₀.obj M).IsKInjective :=
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u+1} _ M
      exact RingedHomUniverses.ordinaryComparison_isIso.{u+1,u,u+1,u+2}
        (ProEt.topology Y) R L (I₀.obj M))
    (by
      intro L M
      have : CochainComplex.IsKInjective (FC.obj (I₀.obj M)) := hFI _
        (CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u+1} _ M)
      exact RingedHomUniverses.ordinaryComparison_isIso.{u+1,u,u+1,u+2} (ProEt.topology X) S
        (FC.obj L) (FC.obj (I₀.obj M)))
  let δ := hδdata.choose
  have hδ := hδdata.choose_spec
  refine ⟨fun K I _ ↦ γ.app (op K, I), δ, ?_, ?_, ?_, ?_⟩
  · intro K I hI r p
    exact hγ K I r p (p+r) rfl
  · intro K K' I I' hI hI' a b
    exact γ.hom.naturality (Prod.mkHom a.op b)
  · intro K K' I I' hI hI' a b ha hb
    let := hI
    let := hI'
    let := ha
    let := hb
    have := quasiIso_homComplex_map.{u+1,u} (R := R) b a
    infer_instance
  · intro K I hI
    refine ⟨hFI I hI, ?_⟩
    have hd := hδ K I
    simp only [RingedHomUniverses.ordinaryComparison_app] at hd
    rw [← podReindexingHomModel_inv l E Y s K I hI,
      ← podReindexingHomModel_inv l E X s (FC.obj K) (FC.obj I) (hFI I hI)] at hd
    let κ := @podReindexingHomModel l _ E _ _ _ Y s K I hI
    exact (FD.mapIso κ).inv_comp_eq.mp hd

-- The theorem combines the two strictly smaller comparison packages above.
/-- Tensor and Hom comparisons, the actual unbounded product Hom-complex comparison,
and its natural derived descent with the specified K-injective resolution model.
Source: blueprint dual-Tate compatibility, Steps 1--2; Stacks Tags 03EL, 0GMX,
0A8X, 0A95, 079I and 08J7
(blueprint: lem-pod-reindexing-hom-resolution-model).

Proof (node Steps 4, 7--10): the tensor comparison comes from the sheafified
sectionwise tensor comparison of lem-pur-isomorphism-inverse-image-tensor-hom;
it sends s tensor t to Fs tensor Ft. The Hom comparison reindexes maps of slice
modules, sending f to Ff. For each integer r preserve the product over every integer
p, then compare its Hom factors. The p-th projection is F of the original projection
followed by the slice Hom comparison. Naturality and additivity identify the two
summands d_I f and -(-1)^r f d_K, so these components form an isomorphism of complexes.
The same computation with b f a proves joint naturality. By lem-pur-rhom-well-defined,
quasi-isomorphisms in either input induce quasi-isomorphisms when both targets are
K-injective. Exact reindexing preserves them and K-injectivity (Steps 2 and 6).
Use prop-pur-kinjective-resolutions-exist, and descend through the localization of
pairs of complexes used by def-pur-derived-internal-hom. Its factorization comparison
and the inverse of Hom(K,I→I₀(I)) give podReindexingHomModel; consequently the displayed
model square commutes. This also proves independence of representatives and resolution.
No boundedness or exactness of infinite products is used. -/
theorem podReindexing_hom_resolution_model {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u+1} X.ProEt] [EssentiallySmall.{u+1} Y.ProEt] (s : Option ℕ) :
    ∃ σ : ∀ M N : podReindexingModules l E Y s,
        (podReindexingFunctor l E g s).obj (podReindexingTensor l E Y s M N) ≅
          podReindexingTensor l E X s ((podReindexingFunctor l E g s).obj M)
            ((podReindexingFunctor l E g s).obj N),
    ∃ η : ∀ M N : podReindexingModules l E Y s,
        (podReindexingFunctor l E g s).obj (SheafOfModules.homObj (J := ProEt.topology Y) (R :=
          podReindexingRing l E Y s) M N) ≅
          SheafOfModules.homObj (J := ProEt.topology X) (R := podReindexingRing l E X s)
            ((podReindexingFunctor l E g s).obj M)
            ((podReindexingFunctor l E g s).obj N),
    ∃ χ : ∀ (K I : CochainComplex (podReindexingModules l E Y s) ℤ)
        (_hI : I.IsKInjective),
        (podReindexingComplexFunctor l E g s).obj
            (homComplex.{u+1,u,u+1,u+1} (R := podReindexingRing l E Y s) K I) ≅
          homComplex.{u+1,u,u+1,u+1} (R := podReindexingRing l E X s)
            ((podReindexingComplexFunctor l E g s).obj K)
            ((podReindexingComplexFunctor l E g s).obj I),
    ∃ δ : podReindexingDerivedHom l E Y s ⋙ podReindexingDerivedFunctor l E g s ≅
        ((podReindexingDerivedFunctor l E g s).op.prod
          (podReindexingDerivedFunctor l E g s)) ⋙ podReindexingDerivedHom l E X s,
      (∀ (M N : podReindexingModules l E Y s) (U : X.ProEt)
          (a : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
          (b : N.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (σ M N).hom.val.app (op U)
            (purTensorSection (podReindexingRing l E Y s) M N
              ((proEtaleIsoPostcompose g).obj U) a b) =
          purTensorSection (podReindexingRing l E X s)
            ((podReindexingFunctor l E g s).obj M)
            ((podReindexingFunctor l E g s).obj N) U a b) ∧
      (∀ (M N : podReindexingModules l E Y s) (U V : X.ProEt) (a : V ⟶ U)
          (f : (SheafOfModules.homObj (J := ProEt.topology Y) (R := podReindexingRing l E Y s) M
            N).val.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj V))),
        ((η M N).hom.val.app (op U) f).app (op (Over.mk a)) x =
          f.app (op (Over.mk ((proEtaleIsoPostcompose g).map a))) x) ∧
      (∀ (K I : CochainComplex (podReindexingModules l E Y s) ℤ)
          (hI : I.IsKInjective) (r p : ℤ),
        (χ K I hI).hom.f r ≫ homComplexπ.{u+1,u,u+1,u+1} (R := podReindexingRing l E X s)
            ((podReindexingComplexFunctor l E g s).obj K)
            ((podReindexingComplexFunctor l E g s).obj I) r p (p+r) rfl =
          (podReindexingFunctor l E g s).map
              (homComplexπ.{u+1,u,u+1,u+1} (R := podReindexingRing l E Y s) K I r p (p+r) rfl) ≫
            (η (K.X p) (I.X (p+r))).hom) ∧
      (∀ (K K' I I' : CochainComplex (podReindexingModules l E Y s) ℤ)
          (hI : I.IsKInjective) (hI' : I'.IsKInjective) (a : K' ⟶ K) (b : I ⟶ I'),
        (podReindexingComplexFunctor l E g s).map
            (((podReindexingHom l E Y s).map a.op).app I ≫
              ((podReindexingHom l E Y s).obj (op K')).map b) ≫ (χ K' I' hI').hom =
          (χ K I hI).hom ≫
            ((podReindexingHom l E X s).map
              ((podReindexingComplexFunctor l E g s).map a).op).app
              ((podReindexingComplexFunctor l E g s).obj I) ≫
            ((podReindexingHom l E X s).obj
              (op ((podReindexingComplexFunctor l E g s).obj K'))).map
              ((podReindexingComplexFunctor l E g s).map b)) ∧
      (∀ (K K' I I' : CochainComplex (podReindexingModules l E Y s) ℤ)
          (_hI : I.IsKInjective) (_hI' : I'.IsKInjective) (a : K' ⟶ K) (b : I ⟶ I'),
        QuasiIso a → QuasiIso b →
          QuasiIso ((podReindexingComplexFunctor l E g s).map
            (((podReindexingHom l E Y s).map a.op).app I ≫
              ((podReindexingHom l E Y s).obj (op K')).map b))) ∧
      (∀ (K I : CochainComplex (podReindexingModules l E Y s) ℤ)
          (hI : I.IsKInjective),
        ∃ hFI : CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I),
          δ.hom.app
              (op ((podReindexingQ l E Y s).obj K), (podReindexingQ l E Y s).obj I) =
            (podReindexingDerivedFunctor l E g s).map
                (@podReindexingHomModel l _ E _ _ _ Y s K I hI).hom ≫
              (podReindexingDerivedFactors l E g s).hom.app
                (homComplex.{u+1,u,u+1,u+1} (R := podReindexingRing l E Y s) K I) ≫
              (podReindexingQ l E X s).map (χ K I hI).hom ≫
              (@podReindexingHomModel l _ E _ _ _ X s
                ((podReindexingComplexFunctor l E g s).obj K)
                ((podReindexingComplexFunctor l E g s).obj I) hFI).inv ≫
              ((podReindexingDerivedHom l E X s).mapIso
                (((podReindexingDerivedFactors l E g s).app K).op.prod
                  ((podReindexingDerivedFactors l E g s).app I).symm)).hom) := by
  obtain ⟨σ, η, hσ, hη⟩ := podReindexing_tensor_hom_data l E g s
  obtain ⟨χ, δ, hχ⟩ := podReindexing_derived_hom_data l E g s η hη
  exact ⟨σ, η, χ, δ, hσ, hη, hχ⟩

end WeilConjectures
