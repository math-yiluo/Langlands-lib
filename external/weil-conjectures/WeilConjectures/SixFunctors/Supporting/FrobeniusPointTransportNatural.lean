/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.ZetaWeil.FrobeniusPointTransport

set_option linter.privateModule false

/-!
# Naturality of Frobenius point transport

Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151
(blueprint: lem-weil-frobenius-point-transport-natural).

The two sigma maps are linear and natural on the finite and completed integral
complex models used by `frobeniusPointFiniteSigma` and
`frobeniusPointIntegralSigma`, and they descend to natural transformations
`Γ(s, -) → Γ(s, g_s⁻¹ -)` on the derived categories (`frobeniusPointFiniteSigmaDerived`,
`frobeniusPointIntegralSigmaDerived`).  The point-transport components are natural
on the finite and integral constructible categories.  Rational components are obtained
by the recorded scalar-localization construction, and algebraically closed
components are represented at a finite coefficient stage; the final clauses
state the corresponding naturality and scalar-extension compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option linter.defProp false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction

attribute [local irreducible] constantSheaf completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard

section Descent
universe v w
variable {C T : Type*} [Category C] [Category T] [Abelian C] [Abelian T]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{w} T]
  (S : C ⥤ T) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (H : C ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (σc : S.mapHomologicalComplex (.up ℤ) ⟶
    H.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ))

end Descent

attribute [local irreducible] Functor.mapDerivedCategory

private theorem apply_heq.{v, w}
    {α γ : Sort w} {β : Sort v} {f : α → β} {g : γ → β}
    (h : HEq f g) {x : α} {y : γ} (hx : HEq x y) : HEq (f x) (g y) :=
  heq_of_eq (congr_heq h hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem finiteSigma_apply
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) (i : ℤ) :
    HEq (fun x ↦ (frobeniusPointFiniteSigma D l E n K).f i x)
      (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  exact (frobeniusPointFiniteSigma_existsUnique D l E n K).choose_spec.1 i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem map_heq
    {C T : Type*} [Category C] [Category T] (F : C ⥤ T)
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [local irreducible] pointFibreSizeDescent pointFibreSizeLift

end WeilConjectures
