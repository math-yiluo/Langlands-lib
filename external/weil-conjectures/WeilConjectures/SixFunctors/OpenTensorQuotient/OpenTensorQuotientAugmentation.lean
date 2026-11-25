/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentatives
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientGeometry
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientCochains
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Algebra.CharP.CharAndCard

/-! # Open reduction and the augmented strict tensor square

Source: Stacks Project, sites-modules.tex Tag 0E8I; sites-cohomology.tex Tag 0GL1;
Bhatt--Scholze, Lemma 6.5.8(2),(3), p.50.
(blueprint: lem-sf-open-tensor-quotient-augmentation).

The index n denotes the positive exponent n+1. The square is imposed on strict
augmented towers of complexes, before applying localization. All total tensors
are the published signed direct-sum total tensors, including for unbounded inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [IsOpenImmersion j] in
private theorem restrictionPartitions_proof : RestrictionPartitions j := by
  intro S hc
  let S' : Scheme.Stratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      isConstructible_stratum := hc
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  let T' := S'.pullback j
  let T : FiniteLocallyClosedStratification U :=
    { n := T'.n
      stratum := T'.stratum
      isLocallyClosed_stratum := T'.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := T'.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := T'.pairwise_disjoint_stratum
      domain := T'.domain
      immersion := T'.immersion
      isImmersion := T'.isImmersion
      range_immersion := T'.range_immersion }
  refine ⟨T, Equiv.refl _, fun _ ↦ rfl, T'.isConstructible_stratum, ?_⟩
  intro k
  exact ⟨pullback.fst (S.immersion k) j, IsPullback.of_hasPullback _ _⟩

private theorem finiteGeometry_proof [IsNoetherian X]
    (hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (K : DerivedCategory (scalarReductionSource l E U))
    (hK : sfIntegralConstructible l E U K) (n : ℕ) (a b : ℤ) (hab : a ≤ b)
    (hs : proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E U n).obj K) ⊆
      Set.Icc a b) :
    FiniteGeometry l E j (n + 1) (Nat.succ_le_succ n.zero_le) a b
      ((scalarReductionDerivedExtension l E U n).obj K) := by
  obtain ⟨_, c, d, _, hred⟩ := hK
  exact open_finite_constructibility_interval l E (n + 1) (Nat.succ_le_succ n.zero_le)
    j hlX a b hab _ (hred n).1 hs

/-- Canonical open reduction and the strict augmented tensor square, with
constructibility, unchanged intervals and partition compatibility. No finite-Tor
condition is imposed; all complexes and total tensors are unbounded.

Source: Stacks Project, sites-modules.tex Tag 0E8I; sites-cohomology.tex Tag 0GL1;
Bhatt--Scholze, Lemma 6.5.8(2),(3), p.50.
(blueprint: lem-sf-open-tensor-quotient-augmentation).

Proof:
1. Choose flat-term K-flat resolutions (lem-pc-kflat-resolution). Apply
lem-sf-open-semilinear-tensor-model and lem-sf-open-tensor-normalization: termwise
open extension computes j_! and its total tensor map is the inverse-open-unit
transpose. Restriction and coefficient pullback preserve these representatives
by lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
2. The simultaneous scalar map sends [x] tensor a to [x tensor a restricted to U].
It respects every quotient and scalar unit. Its inverse has the prescribed
open-unit transpose normalization (def-sf-open-reduction-coefficient-mate).
lem-sf-integral-open-reduction-comparison identifies its localization with r_j(K)
and proves completeness of j_!K.
3. Scalar restriction retains the same additive sheaves and summand maps before
and after extension, hence commutes with extension on entire strict systems.
4. Finite type over k makes X Noetherian and j quasi-compact. Apply
lem-sf-open-finite-constructibility-interval to every quotient: cohomology
commutes with exact extension, its same interval works, and add the reduced
closed complement with zero sheaf to any partition. Intersect partitions with U.
lem-sf-immersion-completed-pullback-comparison gives restriction completeness
and the same uniform interval, proving both integral constructibility claims.
5. Balancing sends (x tensor y) tensor a to (x tensor a) tensor (y tensor 1);
the inverse multiplies the coefficients. These preserve bidegrees and commute
with d(x tensor y)=dx tensor y+(-1)^deg(x) x tensor dy and every quotient.
Thus they compute the canonical tensor change of rings on K-flat representatives.
6. Compose the finite open tensor map with r on the first factor. Both it and
reduction of the integral map send ([x] tensor y) tensor a to
[(x tensor a|_U) tensor (j^*y tensor 1)], before localization, for every quotient.
Sheafification and total-summand uniqueness give the strict tensor comparison.
7. Both augmented routes send [x] tensor y to
[(x tensor 1) tensor (j^*y tensor 1)]. All quotient maps preserve 1, so these are
equal strict complex-system maps, hence equal after localization. The first
Roos coordinate is this tensor and the shifted coordinate is zero, exactly as
in def-sf-tensor-completion-comparison and the normalized strict-limit comparison
lem-cbc-exact-product-functor-strict-limit. No commutation of j_! with limits or
faithfulness of separate derived evaluations is used. -/
theorem openTensorQuotientAugmentation (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))] :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SU : CoefficientDerivedSystemCalculus l E U)
      (_cX : CoefficientDerivedSystemCoherence l E X SX)
      (_cU : CoefficientDerivedSystemCoherence l E U SU)
      (o : IntegralOpenReduction.Operations l E j)
      (st : IntegralOpenReduction.TensorComparison l E j o)
      (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
      (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
      (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
      (c : IntegralOpenReduction.Comparison l E j o SX SU st),
      Nonempty (Comparison l E j o SX SU AX AU st m c) := by
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of D.k))
  let : CompactSpace U :=
    QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of D.k))
  let : IsNoetherian U := ⟨⟩
  have hunit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
      IsUnit (l : Γ(W, ⊤)) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hu : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hl.symm).isUnit
    let g := (W ↘ Spec (.of D.k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
    simpa only [map_natCast] using
      hu.map ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop).hom
  have hlX := hunit X
  have hlU := hunit U
  have hstalk (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    simpa only [map_natCast] using hlX.map (X.presheaf.germ ⊤ x trivial).hom
  obtain ⟨C, _, _⟩ := CompletedOpenTensor.completedOpenTensorRepresentatives l E j hlX hlU
  obtain ⟨hfinite, hgeom⟩ := openQuotientModelGeometry l E j hlX hlU C
  obtain ⟨tX, tU, sc, r, hsq⟩ := openQuotientNormalizedCochains l E j hlX hlU C
  refine ⟨C.ambient, C.openSite, C.ambientCoherence, C.openCoherence,
    C.operations, C.coefficients, C.ordinaryV, C.ordinaryU, C.strictOpen, C.completeOpen,
    ⟨{ tensorX := tX
       tensorU := tU
       scalar := sc
       strictScalar := r
       completeAgreement := fun K ↦ (C.sameOpen K).symm
       finiteModel := hfinite
       integralGeometry := hgeom
       finiteGeometry := ?_
       restrictionPartitions := restrictionPartitions_proof j
       squares := hsq }⟩⟩
  exact finiteGeometry_proof l E j hstalk

end WeilConjectures.OpenTensorQuotient
