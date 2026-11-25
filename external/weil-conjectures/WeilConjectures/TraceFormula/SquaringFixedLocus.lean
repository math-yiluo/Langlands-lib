/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingGraphCriterion
public import WeilConjectures.TraceFormula.Specialization.ContractingIdeals
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# The fixed locus of squaring on the line
Blueprint `example-contracting-squaring`: the fixed scheme of the squaring map `x ↦ x²` of the line
`Spec k[x]` is `Spec k[x]/(x² - x)`
(`ProEtale.CondensedRing.Correspondence.squaringFixedLocus`), the equalizer of `𝟙` and squaring,
since `Spec` turns the coequalizer `k[x] ⇉ k[x] ⟶ k[x]/(x² - x)` of rings into an equalizer. Its
point `0` is an open and closed subscheme `Spec k` (`specPolynomialOver.originComponent`):
`k[x]/(x² - x) ⟶ k` is the localization away from the idempotent `1 - x`. Hence the local term
at the origin of the graph correspondence of squaring is the trace of the stalk map
(`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_squaringFixedLocus`).
(`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_squaringFixedLocus`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Polynomial

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

namespace specPolynomialOver

variable (k : Type u) [Field k]

/-- The ideal `(x² - x)` of the fixed points of squaring. -/
noncomputable abbrev fixedIdeal : Ideal k[X] :=
  Ideal.span {(X : k[X]) ^ 2 - X}

lemma mk_comp_expand :
    (Ideal.Quotient.mk (fixedIdeal k)).comp (expand k 2 : k[X] →+* k[X]) =
      Ideal.Quotient.mk (fixedIdeal k) := by
  refine Polynomial.ringHom_ext (fun a ↦ by simp) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, expand_X]
  exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)

/-- The quotient map `k[x] ⟶ k[x]/(x² - x)`. -/
noncomputable abbrev fixedπ : CommRingCat.of k[X] ⟶ CommRingCat.of (k[X] ⧸ fixedIdeal k) :=
  CommRingCat.ofHom (Ideal.Quotient.mk (fixedIdeal k))

lemma fixedπ_condition :
    𝟙 (CommRingCat.of k[X]) ≫ fixedπ k =
      CommRingCat.ofHom (expand k 2 : k[X] →+* k[X]) ≫ fixedπ k := by
  rw [Category.id_comp]
  exact CommRingCat.hom_ext (mk_comp_expand k).symm

lemma fixedπ_op_condition :
    (fixedπ k).op ≫ (𝟙 (CommRingCat.of k[X])).op =
      (fixedπ k).op ≫ (CommRingCat.ofHom (expand k 2 : k[X] →+* k[X])).op := by
  rw [← op_comp, ← op_comp, fixedπ_condition]

lemma SpecMap_fixedπ_condition :
    Scheme.Spec.map (fixedπ k).op ≫ Scheme.Spec.map (𝟙 (CommRingCat.of k[X])).op =
      Scheme.Spec.map (fixedπ k).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (expand k 2 : k[X] →+* k[X])).op := by
  rw [← Functor.map_comp, ← Functor.map_comp, fixedπ_op_condition]

/-- `k[x]/(x² - x)` is the coequalizer of `𝟙` and `x ↦ x²`. -/
noncomputable def isColimitFixedCofork :
    IsColimit (Cofork.ofπ (fixedπ k) (fixedπ_condition k)) :=
  Cofork.IsColimit.mk' _ fun s ↦ by
    have hX : s.π.hom (X ^ 2) = s.π.hom X := by
      have := congrArg (fun f ↦ f.hom X) s.condition
      simpa using this.symm
    refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift (fixedIdeal k) s.π.hom fun a ha ↦ ?_), ?_, ?_⟩
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, map_sub, hX, sub_self, mul_zero]
    · exact CommRingCat.hom_ext (RingHom.ext fun p ↦ rfl)
    · intro m hm
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_))
      exact congrArg (fun f ↦ f.hom p) hm

/-- `Spec k[x]/(x² - x)` is the equalizer of `𝟙` and squaring on `Spec k[x]`. -/
noncomputable def isLimitFixedFork :
    IsLimit (Fork.ofι (Scheme.Spec.map (fixedπ k).op) (SpecMap_fixedπ_condition k)) :=
  isLimitForkMapOfIsLimit Scheme.Spec (fixedπ_op_condition k)
    ((Cofork.isColimitOfπEquivIsLimitOp (fixedπ k) (fixedπ k) (fixedπ_condition k)
      (fixedπ_op_condition k) rfl) (isColimitFixedCofork k))

instance : IsClosedImmersion (Spec.map (fixedπ k)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The fixed scheme `Spec k[x]/(x² - x)` of squaring, over `Spec k`. -/
noncomputable abbrev fixedScheme : Over (Spec (.of k)) :=
  Over.mk (Spec.map (fixedπ k) ≫ (specPolynomialOver k).hom)

instance : LocallyOfFiniteType (fixedScheme k).hom :=
  inferInstanceAs (LocallyOfFiniteType (Spec.map (fixedπ k) ≫ (specPolynomialOver k).hom))

instance : QuasiCompact (fixedScheme k).hom :=
  inferInstanceAs (QuasiCompact (Spec.map (fixedπ k) ≫ (specPolynomialOver k).hom))

instance : IsSeparated (fixedScheme k).hom :=
  inferInstanceAs (IsSeparated (Spec.map (fixedπ k) ≫ (specPolynomialOver k).hom))

/-- The evaluation at `0`, `k[x]/(x² - x) ⟶ k`. -/
noncomputable def evalZero : k[X] ⧸ fixedIdeal k →+* k :=
  Ideal.Quotient.lift (fixedIdeal k) (evalRingHom 0) fun a ha ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp

lemma evalZero_mk (p : k[X]) : evalZero k (Ideal.Quotient.mk _ p) = p.eval 0 :=
  rfl

lemma isIdempotentElem_mk_one_sub_X :
    IsIdempotentElem (Ideal.Quotient.mk (fixedIdeal k) (1 - X)) := by
  rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton'.mpr ⟨1, by ring⟩

lemma ker_evalZero :
    RingHom.ker (evalZero k) = Ideal.span {1 - Ideal.Quotient.mk (fixedIdeal k) (1 - X)} := by
  have h1 : 1 - Ideal.Quotient.mk (fixedIdeal k) (1 - X) = Ideal.Quotient.mk (fixedIdeal k) X := by
    simp
  rw [h1]
  ext q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [RingHom.mem_ker, evalZero_mk, Ideal.mem_span_singleton']
  constructor
  · intro hp
    obtain ⟨r, rfl⟩ : X ∣ p := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
    exact ⟨Ideal.Quotient.mk _ r, by rw [← map_mul, mul_comm]⟩
  · rintro ⟨c, hc⟩
    have := congrArg (evalZero k) hc
    rw [map_mul, evalZero_mk, evalZero_mk, eval_X, mul_zero] at this
    exact this.symm

/-- The origin `Spec k ⟶ Spec k[x]/(x² - x)` of the fixed scheme. -/
noncomputable def originComponent : ProEtale.CondensedRing.point k ⟶ fixedScheme k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (evalZero k))) <| by
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    simp [evalZero_mk]

/-- The origin is an open point of the fixed scheme: `k[x]/(x² - x) ⟶ k` is the localization away
from the idempotent `1 - x`. -/
instance : IsOpenImmersion (originComponent k).left := by
  let := (evalZero k).toAlgebra
  have : IsLocalization.Away (Ideal.Quotient.mk (fixedIdeal k) (1 - X)) k :=
    IsLocalization.away_of_isIdempotentElem (isIdempotentElem_mk_one_sub_X k) (ker_evalZero k)
      fun a ↦ ⟨Ideal.Quotient.mk _ (C a), by simp [RingHom.algebraMap_toAlgebra, evalZero_mk]⟩
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk (fixedIdeal k) (1 - X))

instance : IsClosedImmersion (originComponent k).left :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨Ideal.Quotient.mk _ (C a), by simp [evalZero_mk]⟩

instance : IsProper (ProEtale.CondensedRing.point k).hom :=
  inferInstanceAs (IsProper (𝟙 _))

end specPolynomialOver

namespace ProEtale.CondensedRing

attribute [local instance] boundedConstructibleBraiding

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {K : Dᵇc((specPolynomialOver k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (specPolynomialOver.squaring k)).obj K ⟶ K)

open specPolynomialOver

/-- (blueprint `example-contracting-squaring`) The fixed locus `Spec k[x]/(x² - x)` of the graph
correspondence of squaring on the line. -/
noncomputable def squaringFixedLocus :
    (ofGraph K (specPolynomialOver.squaring k) v).FixedLocus where
  F := fixedScheme k
  ι := Over.homMk (Spec.map (fixedπ k)) rfl
  w := by
    ext1
    change Spec.map (fixedπ k) ≫ 𝟙 _ = Spec.map (fixedπ k) ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_id, ← Spec.map_comp]
    congr 1
    exact fixedπ_condition k
  isLimit := Fork.IsLimit.mk' _ fun s ↦ by
    have hs : s.ι.left ≫ Scheme.Spec.map (𝟙 (CommRingCat.of k[X])).op =
        s.ι.left ≫ Scheme.Spec.map (CommRingCat.ofHom (expand k 2 : k[X] →+* k[X])).op := by
      have := congrArg CommaMorphism.left s.condition
      simpa [ofGraph, specPolynomialOver.squaring] using this
    let t := Fork.ofι (P := s.pt.left) s.ι.left hs
    have hl : (isLimitFixedFork k).lift t ≫ Spec.map (fixedπ k) = s.ι.left :=
      Fork.IsLimit.lift_ι (isLimitFixedFork k)
    refine ⟨Over.homMk ((isLimitFixedFork k).lift t) ?_, ?_, ?_⟩
    · change _ ≫ Spec.map (fixedπ k) ≫ _ = _
      rw [← Category.assoc, hl]
      exact Over.w s.ι
    · ext1
      exact hl
    · intro m hm
      ext1
      exact Fork.IsLimit.hom_ext (isLimitFixedFork k)
        ((congrArg CommaMorphism.left hm).trans hl.symm)

lemma originComponent_ι :
    originComponent k ≫ (squaringFixedLocus v).ι = specPolynomialOver.origin k := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

lemma liftPoint_squaringFixedLocus :
    (squaringFixedLocus v).liftPoint (specPolynomialOver.origin k)
      (isContractingAt_ofGraph_squaring v).comp_c₁_eq_comp_c₂ = originComponent k :=
  Fork.IsLimit.hom_ext (squaringFixedLocus v).isLimit
    ((FixedLocus.liftPoint_ι _ _ _).trans (originComponent_ι v).symm)

/-- **Local term of squaring at the origin** (blueprint `example-contracting-squaring`): for the
graph correspondence of `x ↦ x²` on the line with any coefficient map, with its fixed locus
`Spec k[x]/(x² - x)` and the open and closed component `{0}`, the local term at the origin is the
trace of the stalk map: `LT_0(u) = tr(u_0 | K_0)`. -/
theorem localTerm_traceClass_squaringFixedLocus
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (specPolynomialOver.origin k)).obj K)] :
    ((ofGraph K (specPolynomialOver.squaring k) v).traceClass (squaringFixedLocus v)).localTerm
        (originComponent k) =
      End.of (trace (graphStalkMap K (specPolynomialOver.squaring k) v (specPolynomialOver.origin k)
        (specPolynomialOver.origin_comp_squaring k))) := by
  refine localTerm_traceClass_ofGraph_squaring v (squaringFixedLocus v) (originComponent k) ?_
  rw [liftPoint_squaringFixedLocus]
  exact RationalPoint.range_left_eq_singleton (originComponent k)

end Correspondence

end ProEtale.CondensedRing

end AlgebraicGeometry
