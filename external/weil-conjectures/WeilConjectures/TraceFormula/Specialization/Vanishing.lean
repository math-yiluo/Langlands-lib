/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Basic
public import WeilConjectures.TraceFormula.Specialization.DeformationExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesVerdierDual

/-!

# Varshavsky's vanishing lemma

Let `c = (c₁, c₂) : C ⟶ X × X` be contracting at the `k`-point `y` of its support, with
`x = c₁(y) = c₂(y)`, let `B` be an open and closed subscheme of the fixed locus, proper over `k`,
with underlying set `{y}`, and assume that the stalk `K_x` vanishes. Then the trait class of `c`
restricted to `B` vanishes, whatever the coefficient map `u`
(`ProEtale.CondensedRing.Correspondence.restrict_traceClass_eq_zero_of_isContractingAt`, blueprint
`theorem-contracting-correspondences-local-terms`; Varshavsky, *Lefschetz–Verdier trace formula and
a generalization of a theorem of Fujiwara*, Thm. 2.1.3).

The proof is Varshavsky's specialization to the normal cone, over the strictly henselian trait
`Spec k̄⟦t⟧`:
* the exchange maps of nearby cycles specialize the trace class of `c` to the fixed locus of the
  specialized correspondence `c' = (γ₁, γ₂)`, and the specialization is injective on `B`
  (`ProEtale.CondensedRing.Correspondence.IsContractingAt.exists_traceSpecialization`);
* the specialized trace class vanishes as soon as `Rc'^! Ψ_{X×X}(K ⊠ D K)` does
  (`ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass_eq_zero`);
* by Gabber's theorems `Ψ_{X×X}(K ⊠ D K) ≅ Ψ_X K ⊠ D Ψ_X K`
  (`ProEtale.CondensedRing.nonempty_specializationProd_externalProduct_iso`), so that by external
  duality `Rc'^! Ψ_{X×X}(K ⊠ D K) ≅ RHom(γ₂^* Ψ_X K, γ₁^! Ψ_X K)`;
* `γ₂` lands in the zero section (`IsContractingAt.range_specialLeg₂_subset`, blueprint
  `lemma-normal-cones-contracting-ideals`), on which `Ψ_X K` vanishes by Verdier's zero-section
  theorem (`ProEtale.CondensedRing.isZero_upperStar_zeroSection_specialization`), so
  `γ₂^* Ψ_X K = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- Transport of a zero object along an equality of functors. -/
private lemma isZero_obj_obj_of_eq {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    [HasZeroMorphisms 𝒞] {G G' : 𝒜 ⥤ ℬ} (h : G = G') (H : ℬ ⥤ 𝒞) (P : 𝒜)
    (hz : IsZero (H.obj (G'.obj P))) : IsZero (H.obj (G.obj P)) := by
  subst h
  exact hz

namespace Correspondence

variable {c : Correspondence ℓ K}

namespace IsContractingAt

variable {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k']
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

/-- **Specialization of the trace class to the normal cone** (blueprint
`sec-Base-change-for-nearby-cycles`, `prose-E-15`,
`corollary-specialization-when-fixed-point-scheme--1`, `lemma-fixed-point-scheme-deformation--1`;
Varshavsky, §1.4–§2): the nearby cycles of the deformation of `c` to the normal cones carry exchange
maps `σ, θ, χ, β` with the coherences of `TraceSpecialization` (the unit identity, the composition
law for `θ` and the fixed-square identity), relating the trace class of `c` to the specialized
correspondence `c'`; and since the deformed fixed locus is the constant family `F × S` up to
nilpotents (`lemma-fixed-point-scheme-deformation--1`), the specialization of Borel–Moore sections
is the base change to `k'` on the component `B = {y}` of the fixed locus
(`corollary-specialization-when-fixed-point-scheme--1`), so it is injective there. The exchange maps
`β` and `θ` are built from compactifications of the deformed schemes over the trait. -/
theorem exists_traceSpecialization (F : c.FixedLocus) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    ∃ T : c.TraceSpecialization F (hc.specialCorrespondence k') (hc.specialFixedLocus k'),
      T.ΨXX = specializationProd k' (y ≫ c.c₁) ∧
      ∀ z : BorelMooreSection ℓ F.F, T.sp z = 0 → z.restrict j = 0 := by
  have hS := specializesComponentClass_deformation (ℓ := ℓ) (X := X) (c := c) (y := y) hc k' F j hB
  refine ⟨hc.deformationTraceSpecialization k' (hc.supportCompactSupportExchange k')
    (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F, ?_, ?_⟩
  · exact hc.deformationTraceSpecialization_ΨXX k' _ _ F
  · intro z hz
    exact hc.restrict_eq_zero_of_sp_eq_zero k' j hB hS z hz

include k' in
/-- The vanishing lemma `restrict_traceClass_eq_zero_of_isContractingAt`, proved with nearby
cycles over the trait `Spec k'⟦t⟧` for any separably closed extension `k'` of `k`. -/
theorem restrict_traceClass_eq_zero (F : c.FixedLocus) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (y ≫ c.c₁)).obj K)) :
    (c.traceClass F).restrict j = 0 := by
  obtain ⟨T, hXX, hinj⟩ := hc.exists_traceSpecialization k' F j hB
  refine hinj _ (T.sp_traceClass_eq_zero ?_)
  have he := nonempty_specializationProd_externalProduct_iso (ℓ := ℓ) k' (y ≫ c.c₁) K
  refine isZero_obj_obj_of_eq hXX _ _ (IsZero.of_iso ?_
    ((boundedConstructibleUpperShriek ℓ
      (hc.specialCorrespondence k').support).mapIso he.some))
  refine isZero_upperShriek_externalProduct_of_isZero ?_
  exact isZero_boundedConstructibleUpperStar_obj_of_range_subset ℓ
    _ _
    (hc.range_specialLeg₂_subset k') _
    (isZero_upperStar_zeroSection_specialization (ℓ := ℓ) k' (y ≫ c.c₁) K hK)

end IsContractingAt

variable (c)

/-- **Vanishing of the trace class at a contracting point with zero stalk** (blueprint
`theorem-contracting-correspondences-local-terms` for the closed subscheme `Z = {x}` of the rational
point `x = c₁(y)`; Varshavsky, *Lefschetz–Verdier trace formula and a generalization of a theorem of
Fujiwara*, Thm. 2.1.3, the case `K|_Z = 0` of its proof): let `c` be contracting at `y` and let
`B` be an open and closed subscheme of the fixed locus, proper over `s`, with underlying set
`{y}`. If the stalk `K_x` vanishes, the restriction of the trace class of `c` to `B` is zero,
whatever the coefficient map `u`. The proof specializes to the normal cone over the trait
`Spec k̄⟦t⟧` (`IsContractingAt.restrict_traceClass_eq_zero`). -/
theorem restrict_traceClass_eq_zero_of_isContractingAt (F : c.FixedLocus)
    {y : RationalPoint c.C} (hc : c.IsContractingAt y) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (y ≫ c.c₁)).obj K)) :
    (c.traceClass F).restrict j = 0 :=
  haveI : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
  haveI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
  hc.restrict_traceClass_eq_zero (AlgebraicClosure k) F j hB hK

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
