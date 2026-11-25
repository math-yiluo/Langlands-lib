/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Site.SiteAlgebraicCompositionUnitSupplement

/-! # Uniqueness of algebraic lifts of inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 00YV.
(blueprint: lem-sf-adic-algebraic-inverse-image-uniqueness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicFiniteRealization

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Two algebraic lifts of the same inverse image differ by the induced coefficient
isomorphism and its restriction of scalars.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 00YV
(blueprint: lem-sf-adic-algebraic-inverse-image-uniqueness).
Proof: compare the two underlying ring sheaves through their fixed identifications
with inverse image of the source ring. Lift each pair of sections to inverse image of
the product of the source underlying ring with itself. The addition and multiplication
graph equations show that the comparison is a ring equivalence. On modules, compare
through their underlying inverse-image identifications. The same product argument
shows additivity and semilinearity. The inverse underlying map yields the inverse
linear map, and naturality follows from the two underlying natural isomorphisms. -/
theorem algebraicInverseImage_unique
    {X Y : Scheme.{u}}
    (L : Sheaf (ProEt.topology Y) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology X) (Type (u + 1))) [PreservesFiniteLimits L]
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
      u + 1, u + 1} L R S)
    (I' : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
      u + 1, u + 1} L R S') :
    ∃ c : S ≅ S', Nonempty (I.modules ≅ I'.modules ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)) := by
  obtain ⟨c, hc, eM, heM, hsmul⟩ :=
    CategoryTheory.algebraicComparison (Iso.refl L) R S S' I I'
  let G := I'.modules ⋙ SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)
  let τ : I.modules ⟶ G :=
    { app M := ⟨PresheafOfModules.homMk (eM.hom.app M).hom (hsmul M)⟩
      naturality := by
        intro M N f
        ext V x
        exact congrArg (fun k ↦ k.hom.app V x) (eM.hom.naturality f) }
  have hτ (M) : IsIso (τ.app M) := by
    have : IsIso ((SheafOfModules.toSheaf _).map (τ.app M)) :=
      show IsIso (eM.hom.app M) from inferInstance
    exact isIso_of_reflects_iso (τ.app M) (SheafOfModules.toSheaf _)
  let := hτ
  exact ⟨c, ⟨NatIso.ofComponents (fun M ↦ asIso (τ.app M)) (fun f ↦ τ.naturality f)⟩⟩

end WeilConjectures.AdicFiniteRealization
