/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularScalarInjectiveDivisibility
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeChain

set_option linter.privateModule false

/-! # The actual ordinary quotient kernel and injective divisibility

Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and evaluation
of the ordinary coinduction adjunction.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

section Generic

universe w v r wR wS
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.RegularQuotientCone

variable {C : Type w} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (φ : R ⟶ S) (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [HasDerivedCategory.{wR} (Modules R)]
  [HasDerivedCategory.{wS} (Modules S)] in
/-- The coinduction counit is killed by the regular scalar.
Source: Stacks Tags 03D7 and 06YP; the scalar acts by zero on restricted modules
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem counit_scalar_zero
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    {G : Modules R ⥤ Modules S} (adj : restriction φ ⊣ G) (M : Modules R) :
    adj.counit.app M ≫ (scalar R t).app M = 0 := by
  have hn : adj.counit.app M ≫ (scalar R t).app M =
      (scalar R t).app ((restriction φ).obj (G.obj M)) ≫ adj.counit.app M :=
    (scalar R t).naturality (adj.counit.app M)
  rw [hn, scalar_restriction_zero t φ ht, zero_comp]

/-- The ordinary coinduction counit is the kernel of the regular scalar, and on an injective
module the scalar is moreover surjective: `0 → coind(M) → M → M → 0` is short exact after
restriction.
Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and
evaluation of the ordinary coinduction adjunction
(blueprint: lem-sf-regular-quotient-injective-kernel).

Proof: for a flat module `X` the sequence `X → X → X ⊗ S` is short exact, and every map from
`X` to a restricted module factors through its last map. Hence maps `X ⟶ coind(M)` correspond,
through the counit, exactly to maps `X ⟶ M` killed by the scalar. Every module is a quotient of
a flat one, which gives that the counit is a monomorphism and that the kernel of the scalar
lifts through it. Surjectivity of the scalar on injective modules is divisibility. -/
theorem counit_scalar_shortExact_of_injective
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    (hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap φ) ht).ShortExact)
    (d : DerivedChangeOfRingsCochainModel.{w, v, r, wR, wS} φ)
    {G : Modules R ⥤ Modules S} (adj : restriction φ ⊣ G) (M : Modules R) [Injective M] :
    (ShortComplex.mk (adj.counit.app M) ((scalar R t).app M)
      (counit_scalar_zero φ t ht adj M)).ShortExact := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  have hlift (X : Modules R) (hX : exactFunctor _ _ (tensorRight X)) (g : X ⟶ M)
      (hg : g ≫ (scalar R t).app M = 0) :
      ∃ h : X ⟶ (restriction φ).obj (G.obj M), h ≫ adj.counit.app M = g := by
    obtain ⟨Y, η, hz, hs, -⟩ := exists_scalar_shortExact_of_flat φ t ht hexact d X hX
    have : Epi η := hs.epi_g
    have hk : (scalar R t).app X ≫ g = 0 :=
      ((scalar R t).naturality g).symm.trans hg
    let g₁ := hs.exact.desc g hk
    refine ⟨η ≫ (restriction φ).map (adj.homEquiv _ _ g₁), ?_⟩
    have h2 : (restriction φ).map (adj.homEquiv _ _ g₁) ≫ adj.counit.app M = g₁ :=
      (adj.homEquiv_counit (g := adj.homEquiv _ _ g₁)).symm.trans
        ((adj.homEquiv _ _).symm_apply_apply g₁)
    rw [Category.assoc, h2]
    exact hs.exact.g_desc g hk
  have hzero (X : Modules R) (hX : exactFunctor _ _ (tensorRight X))
      (h : X ⟶ (restriction φ).obj (G.obj M)) (hh : h ≫ adj.counit.app M = 0) : h = 0 := by
    obtain ⟨Y, η, hz, hs, hfac⟩ := exists_scalar_shortExact_of_flat φ t ht hexact d X hX
    have : Epi η := hs.epi_g
    obtain ⟨h', rfl⟩ := hfac (G.obj M) h
    have h0 : (restriction φ).map h' ≫ adj.counit.app M = 0 := by
      rw [← cancel_epi η, comp_zero, ← Category.assoc, hh]
    have h1 : h' = 0 := by
      have h3 : (adj.homEquiv _ _).symm h' = 0 := (adj.homEquiv_counit _ _ _).trans h0
      apply (adj.homEquiv _ _).symm.injective
      rw [h3, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    rw [h1, Functor.map_zero, comp_zero]
  have hmono : Mono (adj.counit.app M) := by
    refine Preadditive.mono_of_cancel_zero _ fun {Z} k hk ↦ ?_
    obtain ⟨X, q, hq, hX⟩ := exists_flat_epi Z
    rw [← cancel_epi q, comp_zero]
    exact hzero X hX (q ≫ k) (by rw [Category.assoc, hk, comp_zero])
  have hepi : Epi ((scalar R t).app M) := epi_scalar_of_injective φ t ht hexact d M
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  obtain ⟨X, q, hq, hX⟩ := exists_flat_epi (kernel ((scalar R t).app M))
  obtain ⟨h, hh⟩ := hlift X hX (q ≫ kernel.ι _) (by rw [Category.assoc, kernel.condition,
    comp_zero])
  have hfac : h ≫ kernel.lift _ (adj.counit.app M) (counit_scalar_zero φ t ht adj M) = q := by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, hh]
  rw [← hfac] at hq
  exact epi_of_epi h _

end SheafOfModules.RegularQuotientCone

end Generic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale SheafOfModules SheafOfModules.RegularQuotientCone
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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)

/-- For an injective completed-coefficient module `M`, the ordinary coinduction counit and the
positive uniformizer scalar form a short exact sequence `0 → coind(M) → M → M → 0`.
Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and
evaluation of the ordinary coinduction adjunction
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem scalarReductionCoinduction_counit_shortExact
    (M : scalarReductionSource.{u, u} l E T) [Injective M] :
    (ShortComplex.mk ((scalarReductionCoinductionAdjunction.{u} l E T n).counit.app M)
      ((scalar (completedIntegralCommRingSheafUnrestricted l E T)
        (reductionScalarSection l E T n)).app M)
      (counit_scalar_zero _ _ (reductionScalar_zero l E T n)
        (scalarReductionCoinductionAdjunction.{u} l E T n) M)).ShortExact :=
  counit_scalar_shortExact_of_injective _ _ (reductionScalar_zero l E T n)
    (reductionScalar_shortExact l E T n) (reductionCochainModel l E T n)
    (scalarReductionCoinductionAdjunction.{u} l E T n) M

end WeilConjectures
