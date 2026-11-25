/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! Transport of regular quotient trace invertibility from K-injective models.

Source: Stacks Tags 05RT and 0A70;
(blueprint: lem-sf-regular-quotient-trace-from-k-injective).
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

/-- Invertibility on K-injective representatives extends to every derived object.
Source: Stacks Tags 05RT and 0A70; naturality of the derived trace and essential
surjectivity of the K-injective localization model.
(blueprint: lem-sf-regular-quotient-trace-from-k-injective).

Proof: represent the object by a K-injective complex and transport the component
along the representing isomorphism using naturality. Isomorphisms are preserved by
functors and canceled in the resulting conjugation equation.
-/
theorem reductionCoinductionTrace_isIso_of_KInjective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T))
    (hK : ∀ (I : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      [I.IsKInjective],
      IsIso ((reductionCoinductionTrace.{u} l E T n).app (DerivedCategory.Q.obj I))) :
    IsIso ((reductionCoinductionTrace.{u} l E T n).app K) := by
  obtain ⟨I, hI, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  exact (NatTrans.isIso_app_iff_of_iso (reductionCoinductionTrace l E T n) e).mpr
    (hK I)

end WeilConjectures
