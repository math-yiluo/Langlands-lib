/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
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

/-! K-injective computation of the regular quotient trace.

Source: Stacks Tags 079P and 05RT;
(blueprint: lem-sf-regular-quotient-trace-on-k-injective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0,u,u+1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u,u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

/-- The normalized regular quotient trace is invertible on any (e.g. K-injective) complex,
given its invertibility on complexes with injective terms.
Source: Stacks Tags 079P and 05RT; functorial K-injective resolutions with injective terms
on a ringed site, and naturality of the trace.
(blueprint: lem-sf-regular-quotient-trace-on-k-injective).

Proof: the functorial K-injective resolution `η_I : I ⟶ R(I)` on the ringed site is a
quasi-isomorphism into a complex with injective terms, so `Q(η_I)` is an
isomorphism. By hypothesis the trace is invertible at `Q(R(I))`; naturality of the trace
transports invertibility along `Q(η_I)`.
-/
theorem reductionCoinductionTrace_isIso_onKInjective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (I : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (hterms : ∀ (J : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      [∀ i : ℤ, Injective (J.X i)],
      IsIso ((reductionCoinductionTrace.{u} l E T n).app (DerivedCategory.Q.obj J))) :
    IsIso ((reductionCoinductionTrace.{u} l E T n).app (DerivedCategory.Q.obj I)) := by
  obtain ⟨_, _, R, η, h⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
      u + 1, u, u + 1} (Scheme.ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)
  obtain ⟨hq, -, hinj⟩ := h I
  have : ∀ i : ℤ, Injective ((R.obj I).X i) := hinj
  exact (NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Q.map (η.app I)))).mpr
    (hterms (R.obj I))

end WeilConjectures
