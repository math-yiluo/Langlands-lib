/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingGraph
public import WeilConjectures.TraceFormula.Specialization.ContractingSquaring

/-!
# A criterion for graph correspondences to be contracting

A graph correspondence `(𝟙, h)` is contracting at a rational point `x` fixed by `h` as soon as the
stalk map of `h` at `x` sends the maximal ideal `𝔪` of `𝒪_{X,x}` into `𝔪²`
(`ProEtale.CondensedRing.Correspondence.isContractingAt_ofGraph_of_map_maximalIdeal_le_sq`). On an
affine scheme `Spec S`, this holds for `Spec φ` at a prime `𝔮` with `φ(φ⁻¹ 𝔮) ⊆ 𝔮²`
(`Scheme.map_maximalIdeal_stalkMap_SpecMap_le_sq`).

Blueprint `example-contracting-squaring`: the squaring map `x ↦ x²` of the line
`Spec k[x]` (`specPolynomialOver.squaring`) is contracting at the origin
(`ProEtale.CondensedRing.Correspondence.isContractingAt_ofGraph_squaring`), so that the local term
at the origin of its graph correspondence is the trace of the stalk map
(`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_ofGraph_squaring`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory IsLocalRing Polynomial

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The stalk map of `Spec φ : Spec S ⟶ Spec R` at a prime `𝔮` of `S` sends the maximal ideal into
the square of the maximal ideal as soon as `φ(φ⁻¹ 𝔮) S ⊆ 𝔮²`. -/
lemma Scheme.map_maximalIdeal_stalkMap_SpecMap_le_sq {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (q : Spec S) (hq : ((Spec.map φ).base q).asIdeal.map φ.hom ≤ q.asIdeal ^ 2) :
    (maximalIdeal ((Spec R).presheaf.stalk ((Spec.map φ).base q))).map
        ((Spec.map φ).stalkMap q).hom ≤ maximalIdeal ((Spec S).presheaf.stalk q) ^ 2 := by
  set p : Spec R := (Spec.map φ).base q
  have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let : Algebra R ((Spec R).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  let : Algebra S ((Spec S).presheaf.stalk q) := StructureSheaf.stalkAlgebra S q
  have : IsLocalization.AtPrime ((Spec S).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk S q
  have hR : maximalIdeal ((Spec R).presheaf.stalk p) =
      p.asIdeal.map (StructureSheaf.toStalk R p).hom :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal _).symm
  have hS : maximalIdeal ((Spec S).presheaf.stalk q) =
      q.asIdeal.map (StructureSheaf.toStalk S q).hom :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal _).symm
  have hc : ((Spec.map φ).stalkMap q).hom.comp (StructureSheaf.toStalk R p).hom =
      (StructureSheaf.toStalk S q).hom.comp φ.hom :=
    RingHom.ext fun a ↦ stalkMap_toStalk_apply φ q a
  rw [hR, hS]
  refine (Ideal.map_map _ _).le.trans ?_
  refine (le_of_eq (congrArg (fun g ↦ Ideal.map g p.asIdeal) hc)).trans ?_
  refine (Ideal.map_map _ _).symm.le.trans ?_
  refine le_trans ?_ (Ideal.map_pow _ _ _).le
  exact Ideal.map_mono hq

variable (k : Type u) [Field k]

/-- The affine line `Spec k[x]` over `Spec k`. -/
noncomputable abbrev specPolynomialOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (C : k →+* k[X])))

instance : LocallyOfFiniteType (specPolynomialOver k).hom := by
  change LocallyOfFiniteType (Spec.map _)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance : QuasiCompact (specPolynomialOver k).hom :=
  inferInstanceAs (QuasiCompact (Spec.map _))

instance : IsSeparated (specPolynomialOver k).hom :=
  inferInstanceAs (IsSeparated (Spec.map _))

/-- (blueprint `example-contracting-squaring`) The squaring map `x ↦ x²` of the line `Spec k[x]`,
induced by `expand k 2 : x ↦ x²`. -/
noncomputable def specPolynomialOver.squaring : specPolynomialOver k ⟶ specPolynomialOver k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (expand k 2 : k[X] →+* k[X]))) <| by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun a ↦ expand_C 2 a

/-- (blueprint `example-contracting-squaring`) The origin of the line `Spec k[x]`, given by the
evaluation `k[x] ⟶ k` at `0`. -/
noncomputable def specPolynomialOver.origin : ProEtale.CondensedRing.RationalPoint
    (specPolynomialOver k) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (evalRingHom (0 : k)))) <| by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact RingHom.ext fun a ↦ by simp

/-- The origin is fixed by squaring. -/
lemma specPolynomialOver.origin_comp_squaring : origin k ≫ squaring k = origin k := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun a ↦ (expand_eval 2 a 0).trans (by rw [zero_pow two_ne_zero]; rfl)

/-- The origin of `Spec k[x]` is the prime `(x)`. -/
lemma specPolynomialOver.origin_asIdeal :
    ((origin k).left (default : Spec (.of k))).asIdeal = Ideal.span {(X : k[X])} := by
  change Ideal.comap (evalRingHom (0 : k)) (default : Spec (.of k)).asIdeal = _
  rw [@Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime (default : Spec (.of k))),
    ← RingHom.ker_eq_comap_bot,
    ker_evalRingHom, map_zero, sub_zero]

/-- (blueprint `example-contracting-squaring`) The stalk map of squaring at the origin sends the
maximal ideal into its square. -/
lemma specPolynomialOver.map_maximalIdeal_stalkMap_squaring_le_sq :
    (maximalIdeal ((specPolynomialOver k).left.presheaf.stalk
        ((squaring k).left ((origin k).left (default : Spec (.of k)))))).map
        ((squaring k).left.stalkMap ((origin k).left (default : Spec (.of k)))).hom ≤
      maximalIdeal ((specPolynomialOver k).left.presheaf.stalk
        ((origin k).left (default : Spec (.of k)))) ^ 2 := by
  refine Scheme.map_maximalIdeal_stalkMap_SpecMap_le_sq
    (CommRingCat.ofHom (expand k 2 : k[X] →+* k[X])) _ ?_
  change Ideal.map _ (Ideal.comap _ _) ≤ _
  rw [origin_asIdeal]
  exact map_comap_expand_span_X_le_sq k

namespace ProEtale.CondensedRing

attribute [local instance] boundedConstructibleBraiding

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Criterion

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- **A criterion for graph correspondences to be contracting** (blueprint
`example-contracting-squaring`, generalising the Frobenius case
`isContractingAt_ofGraph_frobeniusIterate`): the graph correspondence `(𝟙, h)` is contracting at
a rational point `x` fixed by `h` as soon as the stalk map `h^♯ : 𝒪_{X,x} ⟶ 𝒪_{X,x}` sends the
maximal ideal `𝔪` into `𝔪²` (the contraction condition with `n = 1`). -/
theorem isContractingAt_ofGraph_of_map_maximalIdeal_le_sq (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (x : RationalPoint X) (hx : x ≫ h = x)
    (hle : (maximalIdeal (X.left.presheaf.stalk (h.left (x.left (default : Spec (.of k)))))).map
        (h.left.stalkMap (x.left (default : Spec (.of k)))).hom ≤
      maximalIdeal (X.left.presheaf.stalk (x.left (default : Spec (.of k)))) ^ 2) :
    (ofGraph K h v).IsContractingAt x := by
  refine ⟨?_, ?_, 1, le_rfl, ?_⟩
  · change x ≫ 𝟙 X = x ≫ h
    rw [Category.comp_id, hx]
  · have : IsIso (ofGraph K h v).c₁ := inferInstanceAs (IsIso (𝟙 X))
    exact IsPullback.of_vert_isIso ⟨by rw [Category.id_comp]⟩
  · refine (pow_one _).le.trans (le_of_le_of_eq hle ?_)
    exact congrArg (· ^ 2) (Scheme.map_maximalIdeal_stalkMap_id X.left _).symm

end Criterion

variable {K : Dᵇc((specPolynomialOver k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- (blueprint `example-contracting-squaring`) The graph correspondence of squaring `x ↦ x²` on
the line `Spec k[x]` is contracting at the origin, for any coefficient map. -/
theorem isContractingAt_ofGraph_squaring
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (specPolynomialOver.squaring k)).obj K ⟶ K) :
    (ofGraph K (specPolynomialOver.squaring k) v).IsContractingAt
      (specPolynomialOver.origin k) :=
  isContractingAt_ofGraph_of_map_maximalIdeal_le_sq _ v _
    (specPolynomialOver.origin_comp_squaring k)
    (specPolynomialOver.map_maximalIdeal_stalkMap_squaring_le_sq k)

/-- (blueprint `example-contracting-squaring`) For the graph correspondence of squaring
`x ↦ x²` on the line, the local term at the origin is the trace of the stalk map:
`LT_0(u) = tr(u_0 | K_0)`. -/
theorem localTerm_traceClass_ofGraph_squaring
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (specPolynomialOver.squaring k)).obj K ⟶ K)
    (F : (ofGraph K (specPolynomialOver.squaring k) v).FixedLocus) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left]
    (hB : Set.range j.left.base = {((F.liftPoint (specPolynomialOver.origin k)
      (isContractingAt_ofGraph_squaring v).comp_c₁_eq_comp_c₂).left.base
        (default : Spec (.of k)))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (specPolynomialOver.origin k)).obj K)] :
    ((ofGraph K (specPolynomialOver.squaring k) v).traceClass F).localTerm j =
      End.of (trace (graphStalkMap K (specPolynomialOver.squaring k) v (specPolynomialOver.origin k)
        (specPolynomialOver.origin_comp_squaring k))) :=
  localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt _ v F _
    (isContractingAt_ofGraph_squaring v) j hB

end Correspondence

end ProEtale.CondensedRing

end AlgebraicGeometry
