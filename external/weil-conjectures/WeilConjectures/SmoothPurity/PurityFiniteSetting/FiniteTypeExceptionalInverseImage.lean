/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Compactification.NagataCompactification

/-! # Finite-level constructible exceptional inverse image

Source: blueprint sec-smooth-purity/sk-def-sf-operations,
theorem-f-shriek-finite-coefficients (blueprint: theorem-f-shriek-finite-coefficients).

The functor is the published comparison transport of the etale right adjoint.
The Noetherian finite-type interface supplies its bounded-below instance without
postulating an ambient pro-etale right adjoint.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the actual positive coefficient quotient, including its standard size lift.
Source: blueprint finite coefficient setting (blueprint: theorem-f-shriek-finite-coefficients).
Proof: use finiteness of O_E/(varpi^n) and transport along ULift. -/
theorem finiteCoefficient (P : PurityFiniteSetting.{u}) : Finite P.Coefficient := by
  have : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  exact inferInstanceAs (Finite (ULift P.Ring))

attribute [instance] finiteCoefficient

/-- Bounded-below preservation for the etale right adjoint over a Noetherian target.
Source: blueprint theorem-f-shriek-finite-coefficients, defining properties paragraph
(blueprint: theorem-f-shriek-finite-coefficients).
Proof: the proper part of a compactification is finite type over a Noetherian scheme.
Its fibre dimensions have a finite global bound by quasi-compactness. Proper torsion
cohomology has amplitude at most twice this bound; open extension is exact.
The adjunction and t-structure orthogonality then bound the right adjoint below. -/
theorem exceptionalBoundedBelow (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [IsNoetherian Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    _root_.DerivedCategory.TStructure.t.plus ((Etale.rightDerivedUpperShriek Λ f).obj K) :=
  Etale.plus_rightDerivedUpperShriek_obj Λ f K hK

/-- A finite-type scheme over a field is Noetherian.
Source: blueprint theorem-f-shriek-finite-coefficients, initial setting
(blueprint: theorem-f-shriek-finite-coefficients).
Proof: fields are Noetherian, finite-type affine algebras are Noetherian, and a finite
cover of the scheme by these affine spectra gives a Noetherian scheme. -/
theorem noetherian (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType a] [QuasiCompact a] :
    IsNoetherian T := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace a
  exact ⟨⟩

/-- The actual finite-level constructible exceptional functor, with its required
bounded-below interface supplied from the finite-type field setting.
Source: blueprint theorem-f-shriek-finite-coefficients, finite-level displayed definition
(blueprint: theorem-f-shriek-finite-coefficients). -/
noncomputable def exceptional (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian aY
  ProEtale.rightDerivedUpperShriek P.Coefficient f

/-- The relative dualizing object is the exceptional inverse image of the coefficient unit.
Source: blueprint theorem-f-shriek-finite-coefficients and
proposition-exceptional-inverse-image-smooth-morphism (blueprint:
theorem-f-shriek-finite-coefficients). -/
noncomputable def dualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian aY
  ProEtale.dualizingComplex P.Coefficient f

/-- The published counit, with the same finite-type field interface.
Source: blueprint theorem-f-shriek-finite-coefficients, adjunction characterization
(blueprint: theorem-f-shriek-finite-coefficients). -/
noncomputable def counit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
      ((P.exceptional f aY).obj K) ⟶ K :=
  letI := P.noetherian aY
  ProEtale.rightDerivedUpperShriekCounit f K hK

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
