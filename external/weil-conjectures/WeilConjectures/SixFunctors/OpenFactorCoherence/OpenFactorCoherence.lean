/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
-- Existing reduction and open scalar mate: def-sf-open-reduction-coefficient-mate.
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherenceData
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorOpenRealization
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorProjectionRealization
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorExchangeRealization

/-! # Completion coherence for the open factor

Source: blueprint main-20261015, proposition-composition-base-change-rf-shriek--1, base-change
paragraph; Bhatt--Scholze, Definition 3.4.10 and Lemmas 6.5.5, 6.5.8; Stacks 099N, 09BN, 0GL1
(blueprint: lem-sf-pf-open-factor-coherence).

All operations are the published operations. The records below present their
normalizations, rather than assuming preservation or choosing new operation functors.
Natural-number level n always means exponent n+1. A tower comparison is an isomorphism
of strict complex-valued functors, with its components fixed before localization.

## Main definitions

- `Open` and `Assertion`: the normalized open-factor assertions.
- `gamma` and `beta`: completed projection and exchange, with their actual units.

## Main statements

- `openFactorCoherence`: the three clauses of the source node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport

namespace WeilConjectures.OpenFactorCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option genSizeOf false in
set_option genInjectivity false in
/-- The complete open-factor assertion. Its data are conclusions, and every displayed
map is fixed by a quotient unit, a strict-tower comparison, or an open-unit transpose.
Source: blueprint proposition-composition-base-change-rf-shriek--1, base-change paragraph
(blueprint: lem-sf-pf-open-factor-coherence). -/
structure Assertion {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare a j' j h) where
  openData : Open l E j
  openData' : Open l E j'
  tensorU : Tensor l E U
  tensorX : Tensor l E X
  horizontal : Pull l E h
  horizontalU : Pull l E a
  ambientExchange : OrdinaryExchange l E sq
  tensor_complete : ∀ (M N : D l E X), sfIntegralConstructible l E X M →
    sfIntegralConstructible l E X N → IsIso ((tensorX.chi l E).app (M, N))
  tensor_completeU : ∀ (M N : D l E U), sfIntegralConstructible l E U M →
    sfIntegralConstructible l E U N → IsIso ((tensorU.chi l E).app (M, N))
  gamma_unit : ∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X P →
    (tensorX.chi l E).app ((J l E j).obj K, P) ≫ gamma l E openData tensorU tensorX K P =
      (openProjectionIso (completed l E) j tensorU.ordinary tensorX.ordinary K P).hom ≫
        (J l E j).map ((tensorU.chi l E).app (K, (star l E j).obj P))
  gamma_iso : ∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X P → IsIso (gamma l E openData tensorU tensorX K P)
  tensorRestriction :
    integralCompletedTensor.{u, u} l E X ⋙ star l E j ≅
      ((star l E j).prod (star l E j)) ⋙ integralCompletedTensor.{u, u} l E U
  restriction_unit : ∀ (M N : D l E X), sfIntegralConstructible l E X M →
    sfIntegralConstructible l E X N →
    (star l E j).map ((tensorX.chi l E).app (M, N)) ≫
        tensorRestriction.hom.app (M, N) =
      (proEtaleCanonicalTensorComparison j ((completed l E).ring X)
        ((completed l E).ring U) ((completed l E).pull j)
        tensorX.ordinary tensorU.ordinary).hom.app (M, N) ≫
          (tensorU.chi l E).app ((star l E j).obj M, (star l E j).obj N)
  gamma_restriction : ∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X P →
    (star l E j).map (gamma l E openData tensorU tensorX K P) ≫
        openData.restrictionIso.hom.app ((integralCompletedTensor.{u, u} l E U).obj
          (K, (star l E j).obj P)) =
      tensorRestriction.hom.app ((J l E j).obj K, P) ≫
        (integralCompletedTensor.{u, u} l E U).map
          (Prod.mkHom (openData.restrictionIso.hom.app K) (𝟙 _))
  completedSquare : integralDerivedPullback.{u, u} l E h ⋙ star l E j' ≅
    star l E j ⋙ integralDerivedPullback.{u, u} l E a
  square_unit : ∀ K : D l E X,
    (star l E j').map ((horizontal.unit l E).app K) ≫ completedSquare.hom.app K =
      (theta l E sq).hom.app K ≫ (horizontalU.unit l E).app ((star l E j).obj K)
  beta_iso : ∀ K : D l E U, sfIntegralConstructible l E U K →
    IsIso (beta l E ambientExchange horizontal horizontalU openData' K)
  beta_unit : ∀ K : D l E U, sfIntegralConstructible l E U K →
    (horizontal.unit l E).app ((J l E j).obj K) ≫
        beta l E ambientExchange horizontal horizontalU openData' K =
      ambientExchange.comparison.hom.app K ≫
        (J l E j').map ((horizontalU.unit l E).app K)
  beta_unique : ∀ (K : D l E U), sfIntegralConstructible l E U K →
    ∀ v : (integralDerivedPullback.{u, u} l E h).obj ((J l E j).obj K) ⟶
        (J l E j').obj ((integralDerivedPullback.{u, u} l E a).obj K),
      (horizontal.unit l E).app ((J l E j).obj K) ≫ v =
        ambientExchange.comparison.hom.app K ≫
          (J l E j').map ((horizontalU.unit l E).app K) →
      v = beta l E ambientExchange horizontal horizontalU openData' K
  beta_restriction : ∀ K : D l E U, sfIntegralConstructible l E U K →
    (star l E j').map (beta l E ambientExchange horizontal horizontalU openData' K) ≫
        openData'.restrictionIso.hom.app ((integralDerivedPullback.{u, u} l E a).obj K) =
      completedSquare.hom.app ((J l E j).obj K) ≫
        (integralDerivedPullback.{u, u} l E a).map (openData.restrictionIso.hom.app K)

private theorem gamma_unit_formal {U X : Scheme.{u}} {j : U ⟶ X}
    [IsOpenImmersion j] (o : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X)
    (K : D l E U) (P : D l E X) :
    (tX.chi l E).app ((J l E j).obj K, P) ≫ gamma l E o tU tX K P =
      (openProjectionIso (completed l E) j tU.ordinary tX.ordinary K P).hom ≫
        (J l E j).map ((tU.chi l E).app (K, (star l E j).obj P)) := by
  simp only [Tensor.chi, gamma, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← (eta l E X).naturality_assoc]
  simpa only [Functor.id_map, Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦
      (openProjectionIso (completed l E) j tU.ordinary tX.ordinary K P).hom ≫ f ≫
        (J l E j).map (tU.comparison.hom.app (K, (star l E j).obj P)))
      (o.unit_commutes (tU.ordinary.tensor.obj (K, (star l E j).obj P)))

private theorem gamma_isIso_formal {U X : Scheme.{u}} {j : U ⟶ X}
    [IsOpenImmersion j] (o : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X)
    (K : D l E U) (P : D l E X) : IsIso (gamma l E o tU tX K P) := by
  dsimp only [gamma]
  infer_instance

private theorem beta_unit_formal {U' U X' X : Scheme.{u}} {a : U' ⟶ U}
    {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    {sq : OpenImmersionSquare a j' j h} (b : OrdinaryExchange l E sq)
    (oh : Pull l E h) (oa : Pull l E a) (oj' : Open l E j') (K : D l E U) :
    (oh.unit l E).app ((J l E j).obj K) ≫ beta l E b oh oa oj' K =
      b.comparison.hom.app K ≫ (J l E j').map ((oa.unit l E).app K) := by
  simp only [Pull.unit, beta, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← (eta l E X').naturality_assoc]
  simpa only [Functor.id_map, Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ b.comparison.hom.app K ≫ f ≫
      (J l E j').map (oa.comparison.hom.app K))
      (oj'.unit_commutes ((star l E a).obj K))

private theorem beta_isIso_formal {U' U X' X : Scheme.{u}} {a : U' ⟶ U}
    {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    {sq : OpenImmersionSquare a j' j h} (b : OrdinaryExchange l E sq)
    (oh : Pull l E h) (oa : Pull l E a) (oj' : Open l E j') (K : D l E U) :
    IsIso (beta l E b oh oa oj' K) := by
  dsimp only [beta]
  infer_instance

private theorem fixedOpen_exists (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    (U X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] : Nonempty (Open l E j.left) := by
  let : U.left.Over (Spec (.of F.k)) := ⟨U.hom⟩
  let : X.left.Over (Spec (.of F.k)) := ⟨X.hom⟩
  let : j.left.IsOver (Spec (.of F.k)) := ⟨j.w⟩
  have : LocallyOfFiniteType (U.left ↘ Spec (.of F.k)) := by
    change LocallyOfFiniteType U.hom
    infer_instance
  have : QuasiCompact (U.left ↘ Spec (.of F.k)) := by
    change QuasiCompact U.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of F.k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of F.k)) := by
    change QuasiCompact X.hom
    infer_instance
  obtain ⟨SX, SU, _, _, o, st, AX, AU, m, c, ⟨q⟩⟩ :=
    OpenTensorQuotient.openTensorQuotientAugmentation l E j.left F hl
  have hr := OpenRoos.openRoosUnitAdjunction l E j.left F hl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rX, rU, _⟩ := hr
  exact openFactorOpenRealization l E j.left SX SU o st AX AU m c q F hl rX rU

/-- Completed open restriction, constructibility, and normalization of the actual open maps.
Source: blueprint main-20261015, proposition-composition-base-change-rf-shriek--1, base-change
paragraph; Bhatt--Scholze 3.4.10, 3.5.1--3.5.2, 6.5.5, 6.5.8; Stacks 099M, 099N, 09BN, 09BP, 0GL1
(blueprint: lem-sf-pf-open-factor-coherence).

Proof plan (the eleven steps of this DAG node):
1. Finite type over Spec k implies Noetherian and qcqs. Every open is quasi-compact.
   The coefficient DVR has finite quotients and their two-term finite-free resolutions;
   its uniformizer ideal therefore satisfies def-weil-pbc-adic-coefficient-datum.
   Open localization identifies coefficients by every quotient projection.
2. lem-weil-pbc-constant-completion-equivalence and the ringed Koszul reflector identify
   the quotient completion and its unit with intrinsic completion. The Roos-triangle
   predicate IsSfDerivedComplete is equivalent to invertibility of that actual unit:
   two fibers of the same product-shift are isomorphic, hence intrinsically complete;
   reflection then makes the actual unit invertible. Do not choose an arbitrary fiber map.
3. Exact restriction preserves countable products. The augmentation-normalized comparison
   lem-cbc-exact-product-functor-strict-limit passes it through Roos and its unit. Tensor
   pullback identifies the entire reduction towers. This gives Pull and open.pull_unit.
4. lem-sf-open-tensor-normalization fixes the open unit and ambient full faithfulness.
   lem-cbc-completed-extension-zero-comparison preserves completeness. Restrict this
   adjunction to the full complete categories to obtain the stated Hom bijection.
5. Apply the ambient open tensor normalization to B to A_n. Its scalar-adjunction mate is
   the augmentation-normalized strict comparison. Scalar restriction commutes with
   direct sums and sheafification defining extension. These are strict-tower maps,
   yielding Open.tower and tower_unit; tensor generation gives tower_unique.
6. Exact extension preserves cohomology and each cohomological interval. Extend the finite
   constructible stratification by the reduced closed complement, on which the extension
   is zero, using ringed open/closed localization. The same interval works for every
   reduction. Restricting a partition proves restriction_constructible. No Tor condition.
7. The ordinary gamma is the inverse open-unit transpose. Its reductions are the finite
   gamma maps, and tensor balancing (x tensor y) tensor a goes to
   (x tensor a) tensor (y tensor 1). This formula commutes with every quotient map,
   including the strict quotient augmentation, before applying derived limits.
8. proposition-extension-zero-restriction-closed-subscheme and exact countable products give
Open.commutes,
   normalized by the actual augmentation. Apply functorial Roos to the strict maps of
   step 7. The resulting completed map is gamma as defined here. The quotient-augmentation
   square gives gamma_unit, with precisely the chi of constructible tensor completion.
9. lem-fix-constructible-tensor-completion makes both chi maps invertible on the domains
   of step 6. Restrict gamma_unit; ordinary gamma restricts to identity and restriction
   preserves the actual completion unit. Cancel chi to obtain gamma_restriction.
10. Apply lem-cbc-completed-extension-zero-comparison to the square. The strict finite
    exchanges are the inverse open-unit transposes, compatible with every coefficient
    quotient by lem-cbc-finite-open-exchange-scalars. Pull.tower and Open.commutes retain
    those strict models and units, so their transported Roos composite is exactly beta.
11. Reflection makes precomposition with the actual pull-completion unit bijective
    for the complete target. Thus beta_unique identifies the preceding strict-reduction
    map with the displayed completion composite, before any evaluation at reductions.
    Restrict the strict finite inverse-unit formula. Pullback composition and the open
    units give identity on that system; functorial Roos preserves its equality. The
    restricted extension/limit comparison is identity on every product projection and
    both Roos summands. This gives square_unit and beta_restriction as actual equalities,
    without using evaluation at finite reductions to detect completed morphisms. -/
theorem openFactorCoherence (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (U' U X' X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (sq : OpenImmersionSquare a.left j'.left j.left h.left) :
    Nonempty (Assertion l E sq) := by
  let : U.left.Over (Spec (.of F.k)) := ⟨U.hom⟩
  let : X.left.Over (Spec (.of F.k)) := ⟨X.hom⟩
  let : j.left.IsOver (Spec (.of F.k)) := ⟨j.w⟩
  have : LocallyOfFiniteType (U.left ↘ Spec (.of F.k)) := by
    change LocallyOfFiniteType U.hom
    infer_instance
  have : QuasiCompact (U.left ↘ Spec (.of F.k)) := by
    change QuasiCompact U.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of F.k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of F.k)) := by
    change QuasiCompact X.hom
    infer_instance
  obtain ⟨SX, SU, _, _, o, st, AX, AU, m, c, ⟨q⟩⟩ :=
    OpenTensorQuotient.openTensorQuotientAugmentation l E j.left F _hl
  have hr := OpenRoos.openRoosUnitAdjunction l E j.left F _hl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rX, rU, _⟩ := hr
  obtain ⟨od⟩ :=
    openFactorOpenRealization l E j.left SX SU o st AX AU m c q F _hl rX rU
  obtain ⟨od'⟩ := fixedOpen_exists l E F _hl U' X' j'
  have hp := OpenProjectionRoos.openProjectionRoosCompletion
    l E j.left o SX SU AX AU st m c q F _hl
  obtain ⟨tx, tu, tr, htr, hgr⟩ :=
    openFactorProjectionRealization l E j.left SX SU o st AX AU m c q F _hl od hp
  have hb := OpenExchangeRoos.openExchangeRoosRestriction l E F _hl U' U X' X a j' j h sq
  obtain ⟨oh, oa, b, r, hr, hbr, hi⟩ :=
    openFactorExchangeRealization l E F _hl U' U X' X a j' j h sq od od' hb
  refine ⟨{
    openData := od
    openData' := od'
    tensorU := q.tensorU
    tensorX := q.tensorX
    horizontal := oh
    horizontalU := oa
    ambientExchange := b
    tensor_complete := tx
    tensor_completeU := tu
    gamma_unit := fun K P _ _ ↦ gamma_unit_formal l E od q.tensorU q.tensorX K P
    gamma_iso := fun K P _ _ ↦ gamma_isIso_formal l E od q.tensorU q.tensorX K P
    tensorRestriction := tr
    restriction_unit := htr
    gamma_restriction := hgr
    completedSquare := r
    square_unit := hr
    beta_iso := fun K _ ↦ beta_isIso_formal l E b oh oa od' K
    beta_unit := fun K _ ↦ beta_unit_formal l E b oh oa od' K
    beta_unique := ?_
    beta_restriction := hbr }⟩
  intro K hK v hv
  apply hi K hK
  exact hv.trans (beta_unit_formal l E b oh oa od' K).symm

end WeilConjectures.OpenFactorCoherence
