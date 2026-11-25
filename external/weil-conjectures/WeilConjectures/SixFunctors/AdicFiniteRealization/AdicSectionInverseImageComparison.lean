/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicAlgebraicInverseImageUniqueness
import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence

/-! # Section presentation and module inverse image
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-sf-adic-section-inverse-image-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Sectionwise module encoding commutes with inverse image, up to its coefficient
isomorphism and restriction of scalars.
Source: Stacks Project, Tags 00YV and 03D2
(blueprint: lem-sf-adic-section-inverse-image-comparison).
Proof: the internal inverse image followed by section encoding and the specified
ordinary module inverse image both transport the underlying set sheaves and all
operation graphs under the same left exact set inverse image. Compare their
coefficient identifications. Inverse product comparison lifts each pair of sections;
the addition and multiplication graph equations make the induced bijection a ring
isomorphism. The analogous argument for module addition and scalar multiplication
makes the underlying module comparison a semilinear isomorphism. Restriction along
the coefficient isomorphism makes it linear. Naturality follows from the underlying
natural comparisons. This uses no coefficient flatness, immersion, noetherianity or
nonempty scheme hypothesis. -/
theorem sectionModule_inverseImage (X Y : Scheme.{u}) (f : X ⟶ Y)
    (A : Sheaf (ProEt.topology Y) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) A) :
    ∃ c : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology X) ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).obj A) ≅
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology Y) A),
      Nonempty
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            (ProEt.topology X)
            ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).obj A)).functor.obj
            (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod A).obj M) ≅
          (pbcRestrict c.hom).obj
            ((proEtaleModuleInverseImage f
              (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
                (ProEt.topology Y) A)).obj
              ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
                (ProEt.topology Y) A).functor.obj M))) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let L := proEtaleSheafInverseImage f (Type (u + 1))
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    ⟨fun J _ _ ↦ ⟨inferInstance⟩⟩
  have : PreservesFiniteLimits
      (U.op.lan : (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ _) :=
    CategoryTheory.preservesFiniteLimits_op_lan_of_flat U
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (ProEt.topology Y) A
  let A' := (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).obj A
  let EY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology Y) A
  let EX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) A'
  obtain ⟨I, ⟨eI⟩⟩ := AlgebraicGeometry.ProEtale.exists_sectionModuleAlgebraicInverseImage
    f A A' (𝟙 A')
  obtain ⟨J, hJ⟩ := proEtaleAlgebraicInverseImage_exists f R
  let J' := CategoryTheory.inverseImageUniverses.{u + 1, u + 1, u, u + 1, u} J
  obtain ⟨c, ⟨e⟩⟩ := algebraicInverseImage_unique L I J'
  refine ⟨c, ⟨?_⟩⟩
  let G := (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod A
  let k : (Mod.mapModComap (𝟙 A') (G :=
      AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f)).obj M ≅ G.obj M :=
    (Mod.comapId A').app (G.obj M)
  exact (EX.functor.mapIso k).symm ≪≫
    EX.functor.mapIso ((Mod.mapModComap (𝟙 A')).mapIso (EY.unitIso.app M)) ≪≫
    eI.app (EY.functor.obj M) ≪≫ e.app (EY.functor.obj M) ≪≫
    (pbcRestrict c.hom).mapIso
      (eqToIso (congrArg (fun F ↦ F.obj (EY.functor.obj M)) hJ))

end WeilConjectures.AdicFiniteRealization
