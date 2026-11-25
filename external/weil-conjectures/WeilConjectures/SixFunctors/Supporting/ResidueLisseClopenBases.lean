/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.Supporting.CompleteTopResidueCellCone
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all WeilConjectures.SixFunctors.Sf.SfClopenLisseCompleteLocalization
import WeilConjectures.SixFunctors.Clopen.ClopenCompletePullbackComparison
import WeilConjectures.SixFunctors.Clopen.ClopenResidueFreeRestriction
import all WeilConjectures.SixFunctors.Supporting.CompleteResidueCohomologyBounds
import all WeilConjectures.SixFunctors.Supporting.FieldTorAmplitude
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Fintype.Order

/-! # Residue bases on a common clopen partition

Source: Stacks Project, proetale.tex, Tag 09C3, the clopen trivialization in
`lemma-local-structure-constructible-complex`
(blueprint: lem-sf-residue-lisse-clopen-bases).
-/

@[expose] public section
set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] HasDerivedCategory.standard

universe u v w x y
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private noncomputable instance (priority := 10000) residueBasesAbSheafify
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

private instance (priority := 10000) residueBasesAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

private noncomputable def exactDerivedHomologyIso
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    {B : Type x} [Category.{y} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A) (q : ℤ) :
    (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor A q).obj K) := by
  exact (F.mapDerivedCategoryHomologyFunctorIso q).symm.app K

private theorem constructibleFiniteStalks
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : IsConstructibleProEtaleModuleSheaf X A F)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A) F) := by
  classical
  obtain ⟨S, _, hS⟩ := hF
  have hx : x (IsLocalRing.closedPoint Ω) ∈ ⋃ i, S.stratum i := by
    rw [S.iUnion_stratum_eq_univ]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [← S.range_immersion i] at hi
  obtain ⟨z, hz⟩ := Scheme.exists_comp_eq_of_mem_range (S.immersion i) x
    (by simpa using hi)
  have hfin := (hS i).2 Ω z
  let e := (proEtalePullbackStalkComparison A (S.immersion i) z).app F
  have hfin' : Finite (proEtaleGeometricModuleStalk (z ≫ S.immersion i)
      (proEtaleConstantRing X A) F) :=
    @Finite.of_equiv _ _ hfin e.toLinearEquiv.toEquiv
  exact (congrArg (fun t : Spec (.of Ω) ⟶ X ↦
    Finite (proEtaleGeometricModuleStalk t (proEtaleConstantRing X A) F)) hz).mp hfin'

private theorem constructibleLisseFiniteModels
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hc : IsConstructibleProEtaleModuleSheaf X A F)
    (hl : IsLocallyConstantProEtaleModuleSheaf X A F) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L) F := by
  classical
  let B := ULift.{u + 1, u} A
  let J := ProEt.topology X
  let R := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
  let F' := (proEtaleModuleRestriction X A).obj F
  obtain ⟨I, U, f, hf, he⟩ := ProEtale.finiteModels_over B F' (by
    obtain ⟨ι, W, g, hW, hM⟩ :=
      (finiteLocal_iff X A F).mpr ⟨hl, constructibleFiniteStalks X A F hc⟩
    exact ⟨ι, W, g, hW, fun i ↦ let ⟨M, _, e⟩ := hM i; ⟨M, Module.finite_of_finite B, e⟩⟩)
  refine ⟨I, U, f, hf, fun i ↦ ?_⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := he i
  let := hL
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit X A)
  have h := proEtaleConstantRingUnit_over_locallyBijective X A (U i)
  have : Presheaf.IsLocallyInjective (J.over (U i)) a := h.1
  have : Presheaf.IsLocallySurjective (J.over (U i)) a := h.2
  have hc' := ConstantScalarComparison.constantComparisonHom_isIso
    (J.over (U i)) B (R.over (U i)) a L
  refine ⟨L, Module.Finite.of_finite, ⟨?_⟩⟩
  exact (ConstantScalarComparison.restrictionFullyFaithful
    (J.over (U i)) B (R.over (U i)) a).preimageIso
      (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
        (J.over (U i)) B (R.over (U i)) a L))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private noncomputable def residueBasisFreeProductIso (X : Scheme.{u}) (r : ℕ) :
    topCellIntegralFree.{u} l E X r ≅
      ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) := by
  let R := completedIntegralCoefficientSheafUnrestricted.{u, u} l E X
  let F : Fin r → SheafOfModules.{u + 1} R := fun _ ↦ SheafOfModules.unit R
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact Sigma.reindex Equiv.ulift F ≪≫ (biproduct.isoCoproduct F).symm ≪≫
    biproduct.isoProduct F

private theorem residueBasisCompleteIso (X : Scheme.{u})
    {K L : IntegralOnSlice.D.{u, u} l E X none} (e : K ≅ L)
    (hL : IsDerivedCompleteUnrestricted.{u, u} l E X L) :
    IsDerivedCompleteUnrestricted.{u, u} l E X K := by
  open IntegralOnSlice in
    have hu := (canonicalCompletionUnitCriterion.{u, u} l E X L).mpr hL
    let := hu
    apply (canonicalCompletionUnitCriterion.{u, u} l E X K).mp
    have h := (completionUnit.{u, u} l E X none).naturality e.hom
    have : IsIso ((completionUnit.{u, u} l E X none).app K ≫
        (completion.{u, u} l E X none).map e.hom) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((completion.{u, u} l E X none).map e.hom)

/-- Choose residue bases on clopen members, preserving completeness and a common Tor interval.
This asserts only restriction and cohomology data, with no integral complex model.

Source: Stacks Project, proetale.tex, Tags 09C3 and 098F; sites-cohomology.tex,
Tags 0946 and 08FZ (blueprint: lem-sf-residue-lisse-clopen-bases).

Proof: choose an ordered interval for the finite residue Tor amplitude. Testing with
its coefficient unit puts all nonzero residue cohomology in this interval. The residue
ring is a field by the extension-integers DVR theorem. Each cohomology sheaf is lisse
and constructible, so its locally constant module models are finite-dimensional.
Apply lem-sf-clopen-lisse-complete-localization to the finite family indexed by the
integer interval. Its finite disjoint cover has compact, weakly contractible members.
Its free constant models, the equivalence between the slice site and the member's
pro-etale site, and exactness of ordinary restriction identify the local cohomology
with the stated finite free residue sheaves. Choose their finite ranks; extend the
rank function by zero outside the interval. Exact evaluation on each member makes
its completed-coefficient unit projective; finite sums are therefore projective.
The coefficient and quotient-tower comparisons in that localization theorem preserve
completeness. On a complete object the completed derived pullback along the open
immersion agrees with this ordinary restriction, since the latter is already complete.
The same normalized coefficient comparisons commute with residue reduction. Finally,
exact restriction and exact pullback preserve cohomological vanishing outside the
interval on every object of each component's pro-etale site. Over the residue field,
tensor cohomology identifies this boundedness with the required Tor interval. If the base is empty,
the empty partition gives the assertion. Zero ranks give zero free residue sheaves.
No basis of integral cohomology and no integral projective model is chosen here. -/
theorem residue_lisse_clopen_bases
    (S : Scheme.{u}) (hS : IsAffine S)
    (hweak : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 S)))
    (K : DerivedCategory (integralTowerModules.{u, u} l E S))
    (hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E S K)
    (hresidue : intrinsicFiniteTorsionConstructible l E 1 (by omega) S
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K))
    (hlisse : ∀ q : ℤ, IsLocallyConstantProEtaleModuleSheaf S
      (Padic.coefficientExtensionRing l E 1)
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S
          (Padic.coefficientExtensionRing l E 1))) q).obj
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)))
    (hTor : HasFiniteProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing l E 1)
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)) :
    ∃ (n : ℕ) (U : Fin n → S.Opens),
      (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        CompactSpace (U i).toScheme ∧
        (∀ (F G : Sheaf (ProEt.topology (U i).toScheme) (Type (u + 1)))
          (f : F ⟶ G), Epi f →
            Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 (U i).toScheme))))) ∧
        (∀ r : ℕ, Projective (topCellIntegralFree.{u} l E (U i).toScheme r)) ∧
        IsDerivedCompleteUnrestricted.{u, u} l E (U i).toScheme
          ((integralDerivedPullback.{u, u} l E (U i).ι).obj K) ∧
        ∃ (a b : ℤ) (r : ℤ → ℕ), a ≤ b ∧
          (∀ q : Set.Icc a b, Nonempty
            (topCellResidueFree.{u} l E (U i).toScheme (r q.val) ≅
              (DerivedCategory.homologyFunctor
                (scalarReductionTarget.{u, u} l E (U i).toScheme 0) q.val).obj
                ((scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).obj
                  ((integralDerivedPullback.{u, u} l E (U i).ι).obj K)))) ∧
          (∀ V : (U i).toScheme.ProEt,
            HasProEtaleTorAmplitude V.left (Padic.coefficientExtensionRing l E 1)
              ((proEtaleRingDerivedPullback V.hom
                (proEtaleConstantRing (U i).toScheme (Padic.coefficientExtensionRing l E 1))
                (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
                (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
                  (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
                ((scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).obj
                  ((integralDerivedPullback.{u, u} l E (U i).ι).obj K))) a b) := by
  classical
  have : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := residue_ideal_maximal l E
  let : Field (Padic.coefficientExtensionRing l E 1) :=
    Ideal.Quotient.field (Padic.coefficientExtensionIdeal l E 1)
  let R := (scalarReductionDerivedExtension.{u, u} l E S 0).obj K
  let H (q : ℤ) := (DerivedCategory.homologyFunctor
    (scalarReductionTarget.{u, u} l E S 0) q).obj R
  obtain ⟨a, b, ht⟩ := hTor
  have hab : a ≤ b := ht.1
  have hb (q : ℤ) (hq : q < a ∨ b < q) : IsZero (H q) :=
    tor_cohomology_bounds S _ R a b ht q hq
  have hm (q : Set.Icc a b) :
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S
        (Padic.coefficientExtensionRing l E 1)
        (fun M ↦ Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) M)
        (H q.val) :=
    constructibleLisseFiniteModels S _ (H q.val) (hresidue.2 q.val) (hlisse q.val)
  have hw : ∀ (F G : Sheaf (ProEt.topology S) (Type (u + 1)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 S)))) := by
    intro F G f hf
    exact hweak f ((Sheaf.isLocallySurjective_iff_epi' _ f).mpr hf)
  obtain ⟨n, U, hcover, hdisjoint, hlocal⟩ :=
    sf_clopen_lisse_complete_localization.{u, u, 0, u} S hS hw
      (Set.Icc a b) (fun q ↦ H q.val) hm
  refine ⟨n, U, hcover, hdisjoint, fun i ↦ ?_⟩
  obtain ⟨hc, hcompact, hweakU, hfree, hproj, d, ⟨c⟩⟩ := hlocal i
  obtain ⟨eK⟩ := sf_clopen_complete_pullback_comparison l E S (U i) hc d K hcomplete
  let eR : (scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).obj
      ((integralDerivedPullback.{u, u} l E (U i).ι).obj K) ≅
      (sfClopenFiniteDerivedRestriction.{u, u} d 0).obj R :=
    (scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).mapIso eK ≪≫
      ((c.reduction 0).app K).symm
  let F : scalarReductionTarget.{u, u} l E S 0 ⥤
      scalarReductionTarget.{u, u} l E (U i).toScheme 0 :=
    sfClopenModuleRestriction (U i) _ _ (d.finite 0)
  let : F.Additive := d.finite_additive 0
  let : PreservesFiniteLimits F := d.finite_limits 0
  let : PreservesFiniteColimits F := d.finite_colimits 0
  let eH (q : ℤ) := (DerivedCategory.homologyFunctor _ q).mapIso eR ≪≫
    exactDerivedHomologyIso F R q
  refine ⟨isCompact_iff_compactSpace.mp hcompact, hweakU, ?_, ?_, ?_⟩
  · intro r
    exact Projective.of_iso (residueBasisFreeProductIso l E (U i).toScheme r).symm
      ((hproj (completedIntegralCommRingSheafUnrestricted.{u, u} l E (U i).toScheme)).2 r)
  · exact residueBasisCompleteIso l E (U i).toScheme eK (c.complete K hcomplete)
  · choose ranks hranks using hfree
    let r (q : ℤ) : ℕ := if h : q ∈ Set.Icc a b then ranks ⟨q, h⟩ else 0
    refine ⟨a, b, r, hab, ?_, ?_⟩
    · intro q
      have er : r q.val = ranks q := dite_eq_left q.property
      rw [er]
      obtain ⟨ef⟩ := sf_clopen_residue_free_restriction l E S (U i) d
        (H q.val) (ranks q) (hranks q)
      exact ⟨ef ≪≫ (eH q.val).symm⟩
    · intro V
      let FV := proEtaleRingModulePullback V.hom
        (proEtaleConstantRing (U i).toScheme (Padic.coefficientExtensionRing l E 1))
        (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
        (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)
      apply bounded_field_tor V.left _ _ a b hab
      intro q hq
      let eV := exactDerivedHomologyIso FV
        ((scalarReductionDerivedExtension.{u, u} l E (U i).toScheme 0).obj
          ((integralDerivedPullback.{u, u} l E (U i).ι).obj K)) q
      exact ((FV.map_isZero ((F.map_isZero (hb q hq)).of_iso (eH q))).of_iso eV)

end WeilConjectures
