/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.IntegralModelPointStalk
public import WeilConjectures.TraceFormula.CurveLocal.ReductionTransfer
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegralPerfect
public import WeilConjectures.TraceFormula.SupportedRestrictionIntegral
public import WeilConjectures.TraceFormula.SupportedRestrictionRational

/-!

# The supported restriction is zero for Frobenius, with `ℚ̄_ℓ`-coefficients

This file proves the `ℚ̄_ℓ`-form of blueprint `lemma-vanishing-local-term-zero-stalk`
(`ProEtale.CondensedRing.Correspondence.upperStar_map_supportedRestriction_frobeniusGraph_eq_zero`)
from the classical finite-coefficient computation
(`AlgebraicGeometry.Etale.CurveLocalModel.restrictionZero`):

* `K` has an integral model `M` over `𝒪_E` with `M_x = 0`
  (`ProEtale.CondensedRing.exists_integralModel_isZero_upperStar`), and
  `K ⊠ D_X K ≅ ℚ̄_ℓ ⊗ (M ⊠ D_X M)`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgClExternalProductVerdierDualIso`);
* the reductions modulo every `ℓⁿ` of the point fibre `f₀` of the integral supported restriction
  factor through classical supported restrictions
  (`ProEtale.CondensedRing.Correspondence.exists_reduction_pointIntegralSupportedRestriction`),
  which vanish; `f₀` is a morphism of perfect `𝒪_E`-complexes
  (`ProEtale.CondensedRing.isPerfect_pointFiberFunctorIntegral_obj`), so it vanishes by the Krull
  intersection theorem;
* the vanishing passes from `𝒪_E` to `E` to `ℚ̄_ℓ`
  (`ProEtale.CondensedRing.Correspondence.FixedLocus.map_supportedRestrictionIntegral_comp`,
  `FixedLocus.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE` in the same
  namespace),
  the point fibre functor being faithful.

-/

@[expose] public section

universe u

namespace CategoryTheory.Preadditive

/-- If `a ≫ b ≫ c = d ≫ e ≫ f` with `a = 0` and `d`, `e` isomorphisms, then `f = 0`. -/
lemma eq_zero_of_comp_eq_comp_of_eq_zero {C : Type*} [Category* C] [Preadditive C]
    {A B B' B'' D D' : C} {a : A ⟶ B} {b : B ⟶ B'} {c : B' ⟶ B''} {d : A ⟶ D} {e : D ⟶ D'}
    {f : D' ⟶ B''} [IsIso d] [IsIso e] (h : a ≫ b ≫ c = d ≫ e ≫ f) (ha : a = 0) : f = 0 := by
  rw [ha, Limits.zero_comp] at h
  exact (IsIso.comp_left_eq_zero _ _).1 ((IsIso.comp_left_eq_zero _ _).1 h.symm)

end CategoryTheory.Preadditive

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

variable (ℓ k) in
/-- **Integral point-fibre vanishing passes to `ℚ̄_ℓ`**: if the integral point fibre
`Fib_s(g)` of a morphism `g` of bounded constructible `𝒪_E`-complexes on the separably closed
point vanishes, so does its extension of scalars `ℚ̄_ℓ ⊗ g`, the point fibre functor being
faithful. -/
theorem boundedConstructibleIntegersToPadicAlgCl_map_eq_zero [IsSepClosed k]
    {E : FiniteIntermediateField ℓ}
    {A B : Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧} (g : A ⟶ B)
    (h : (pointFiberFunctorIntegral ℓ k E).map g = 0) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map g = 0 := by
  have : (pointFiberFunctor ℓ k).Additive := by unfold pointFiberFunctor; infer_instance
  have : (pointFiberFunctor ℓ k).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  apply (bijective_pointFiberFunctor_map ℓ k _ _).1
  dsimp only
  rw [Functor.map_zero]
  refine NatIso.map_eq_zero_of_map_eq_zero (pointFiberFunctorIntegralExtendScalarsIso ℓ k E).symm
    (f := g) ?_
  have : (ModuleCat.derivedExtendScalars (integersToULift.{u} ℓ E.1)
      (flat_integersToULift.{u} ℓ E.1)).Additive := by
    unfold ModuleCat.derivedExtendScalars
    infer_instance
  have h' := congrArg (ModuleCat.derivedExtendScalars (integersToULift.{u} ℓ E.1)
    (flat_integersToULift.{u} ℓ E.1)).map h
  rw [Functor.map_zero] at h'
  exact h'

namespace Correspondence

namespace FixedLocus

variable {c : Correspondence ℓ K}

/-- **Vanishing of a stalk of the supported restriction is invariant under isomorphism**: the
supported restriction is natural in `P` (a mate component), so if the stalk along
`z : T ⟶ Fix(c)` of `ρ_P` vanishes, so does the stalk of `ρ_Q` for `P ≅ Q`. -/
theorem upperStar_map_supportedRestriction_eq_zero_of_iso (F : c.FixedLocus)
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (z : T ⟶ F.F) {P Q : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : P ≅ Q)
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction P) = 0) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction Q) = 0 := by
  have hn := (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ F.d)
    (TwoSquare.mk _ _ _ _ F.lowerShriekBaseChangeIso.inv)).naturality e.hom
  rw [← F.supportedRestriction_eq_mateEquiv, ← F.supportedRestriction_eq_mateEquiv] at hn
  dsimp only [Functor.comp_map] at hn
  have h1 := congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map hn
  simp only [Functor.map_comp, h, Limits.zero_comp] at h1
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).1 h1

/-- **Transport of the vanishing of a stalk of the supported restriction from `𝒪_E` to `ℚ̄_ℓ`**:
if the stalk along `z : T ⟶ Fix(c)` of the extension of scalars `T_E = ℚ̄_ℓ ⊗ -` of the
`𝒪_E`-supported restriction of `P` vanishes, so does the stalk of the `ℚ̄_ℓ`-supported
restriction of `T_E P`. -/
theorem upperStar_map_supportedRestriction_eq_zero_of_integersToPadicAlgCl (F : c.FixedLocus)
    (E : FiniteIntermediateField ℓ) {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom] (z : T ⟶ F.F)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      ((boundedConstructibleIntegersToPadicAlgCl ℓ E F.F).map
        (F.supportedRestrictionIntegral E P)) = 0) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
      (F.supportedRestriction ((boundedConstructibleIntegersToPadicAlgCl ℓ E (X ⨯ X)).obj P)) =
        0 := by
  refine F.upperStar_map_supportedRestriction_eq_zero_of_supportedRestrictionE E z _ ?_
  have := isIso_boundedConstructibleUpperShriekExtendScalars ℓ E c.support
  have h1 := congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
    z).map ((boundedConstructibleToPadicAlgCl F.F.left ℓ E).map f))
    (F.map_supportedRestrictionIntegral_comp E P)
  simp only [Functor.map_comp] at h1
  exact Preadditive.eq_zero_of_comp_eq_comp_of_eq_zero h1 h

end FixedLocus

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- The prime `ℓ` is invertible in `k`, as `ringChar k ≠ ℓ` is prime. -/
lemma natCast_ne_zero_of_ringChar_ne : (ℓ : k) ≠ 0 := by
  intro h
  have hd := (ringChar.spec k ℓ).1 h
  exact (Fact.out : ringChar k ≠ ℓ)
    ((Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) (Fact.out : ℓ.Prime)).1 hd)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Krull vanishing from classical reductions**: a morphism `f₀ : A₀ ⟶ B₀` of perfect
`𝒪_E`-complexes whose reductions modulo every `ℓⁿ` factor through classical supported
restrictions on a strictly local model vanishes, if `RestrictionZero` holds: the reductions
vanish, so `f₀` is divisible by every `ℓⁿ`, hence zero by the Krull intersection theorem. -/
lemma eq_zero_of_forall_reduction [IsAlgClosed k] {M : Etale.CurveLocalModel k}
    {E : FiniteIntermediateField ℓ}
    {A₀ B₀ : DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1)))}
    {f₀ : A₀ ⟶ B₀} (hA : A₀.IsPerfect) (hB : B₀.IsPerfect)
    (hRZ : Etale.CurveLocalModel.RestrictionZero k ℓ)
    (hred : ∀ n : ℕ, ∃ (D : M.CoefficientDatum ℓ)
      (φ : Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1) →+* D.Λ)
      (πA : A₀ ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.source)
      (πB : B₀ ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target)
      (δ : (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target ⟶ B₀⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (((ℓ : ℤ) ^ n) • 𝟙 B₀) πB δ ∈ distTriang _ ∧
      πA ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map D.supportedRestriction =
        f₀ ≫ πB) :
    f₀ = 0 := by
  refine DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul hA hB
    (PadicAlgCl.natCast_mem_maximalIdeal_shrink ℓ E.1) fun n ↦ ?_
  have hn := hred n
  obtain ⟨D, hn⟩ := hn
  obtain ⟨φ, hn⟩ := hn
  obtain ⟨πA, πB, δ, hn⟩ := hn
  obtain ⟨hT, hcomm⟩ := hn
  have h0 := D.supportedRestriction_eq_zero hRZ
  simp only [h0, Functor.map_zero, Limits.comp_zero] at hcomm
  have hex := Pretriangulated.Triangle.coyoneda_exact₂ _ hT f₀ hcomm.symm
  exact ⟨hex.choose, hex.choose_spec.trans (Linear.comp_zsmul_natCast_pow_id hex.choose ℓ n)⟩

/-- **The point fibre of the integral supported restriction vanishes**: for bounded constructible
`𝒪_E`-complexes `M`, `N` on the curve `X` with `M_x = 0`, the point fibre `f₀` of the integral
supported restriction of `M ⊠ N` at `z` is zero. Its reductions modulo every `ℓⁿ` factor through
classical supported restrictions, which vanish, so `f₀` is divisible by every `ℓⁿ`; it is a
morphism of perfect `𝒪_E`-complexes, hence zero by the Krull intersection theorem. -/
theorem pointIntegralSupportedRestriction_hom_eq_zero [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (E : FiniteIntermediateField ℓ) (M N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hM : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (z ≫ F.ι)).obj M)) :
    (pointIntegralSupportedRestriction ℓ F z E M N).hom = 0 :=
  eq_zero_of_forall_reduction (isPerfect_pointFiberFunctorIntegral_obj ℓ k E _)
    (isPerfect_pointFiberFunctorIntegral_obj ℓ k E _)
    (Etale.CurveLocalModel.restrictionZero natCast_ne_zero_of_ringChar_ne)
    (exists_reduction_pointIntegralSupportedRestriction hΦ hm v F z E M N hM)

/-- **The supported restriction is zero for Frobenius** (SGA 5, III B, §§2–4). Let `X` be
smooth of relative dimension one over the algebraically closed field `k`, with the model
Frobenius `Φ` of a model over a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K` arbitrary, and let `z`
be a point of the fixed locus of the graph correspondence `(𝟙, Φ_m)` whose image `x` in `X`
has `K_x = 0`. Then the stalk at `z` of the supported restriction
`ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P`, `P = K ⊠ D_X K`
(`Correspondence.FixedLocus.supportedRestriction`), vanishes.

This is the `ℚ̄_ℓ`-form of the blueprint statement: the stalk of `ρ_P` at `z` is the supported
restriction `ρ_{a,b} : RΓ_a(T, P) ⟶ RΓ_x(b, b^* P)` on the strict localization `T` of `X ⨯ X`
at `(x, x)`, from the Frobenius graph `a` to the diagonal `b`. The blueprint shows
`ρ_{a,b} = 0` in `D(A)` for every finite `ℓ`-primary ring `A` (localization to the punctured
diagonal, covers of degree prime to `ℓ`, and the blowup argument of
`lemma-vanishing-restrictions-after-blowing-up--1`); the `ℚ̄_ℓ`-form follows by the integral models
of `lemma-integral-models-rational-frobenius-correspondences`. The coefficient map `v` plays no
role: `ρ_P` only depends on the correspondence and on `P`. -/
theorem upperStar_map_supportedRestriction_frobeniusGraph_eq_zero [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (z ≫ F.ι)).obj K)) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
    (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ K))) = 0 := by
  obtain ⟨E, M, ⟨e⟩, hM⟩ := exists_integralModel_isZero_upperStar K (z ≫ F.ι) hK
  have h0 := pointIntegralSupportedRestriction_hom_eq_zero hΦ hm v F z E M
    (PadicIntegersRingObj.boundedConstructibleVerdierDual ℓ E.1 (toPoint X) M) hM
  have hT := boundedConstructibleIntegersToPadicAlgCl_map_eq_zero ℓ k
    ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ z).map
      (F.supportedRestrictionIntegral E
        (PadicIntegersRingObj.boundedConstructibleExternalProduct ℓ E.1 M
          (PadicIntegersRingObj.boundedConstructibleVerdierDual ℓ E.1 (toPoint X) M)))) h0
  have hz := NatIso.map_eq_zero_of_map_eq_zero
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E z) hT
  exact F.upperStar_map_supportedRestriction_eq_zero_of_iso z
    (boundedConstructibleIntegersToPadicAlgClExternalProductVerdierDualIso ℓ E e)
    (F.upperStar_map_supportedRestriction_eq_zero_of_integersToPadicAlgCl E z _ hz)

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
