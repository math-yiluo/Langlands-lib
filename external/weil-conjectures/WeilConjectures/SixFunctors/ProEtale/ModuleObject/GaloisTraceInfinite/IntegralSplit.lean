/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTowerMoebius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerUnique
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitTransportExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegersModPowFinal
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsReductionComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMonoTorsion

/-!
# The derived unit of an infinite Galois extension with `𝒪_E`-coefficients splits

Let `Ω/L` be a Galois extension whose finite Galois subextensions have degrees prime to `ℓ`
(for instance a pro-`p` extension, `p ≠ ℓ`), `h : G ⟶ Spec L` and `g : G ×_L Ω ⟶ G`. For a
derived complete `𝒪_E`-complex `K` on `G` whose reductions modulo `ℓⁿ⁺¹` are bounded below of
étale origin, the unit `K ⟶ Rg_* Lg^* K` is a split monomorphism
(`ProEtale.CondensedRing.isSplitMono_derivedUnit_galois_padicIntegers`): this is the integral form
of the Hochschild–Serre splitting of SGA 4½, [Th. finitude], Lemme 3.4.

The proof lifts the torsion splittings with
`ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`.
Modulo `ℓⁿ⁺¹` the reduction of the unit is the unit with coefficients `𝒪_E/ℓⁿ⁺¹`
(`ProEtale.CondensedRing.map_unit_comp_derivedPushPullExtendScalarsHom`, the push comparison
being invertible by `isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app`), compatibly
with the Galois actions. There it has a `Gal(Ω/L)`-invariant retraction
(`ProEtale.exists_invariant_retraction_derivedUnit_galois`), which is unique
(`ProEtale.eq_of_invariant_retraction_derivedUnit_galois`, from the Möbius decomposition of the
infinite level, `ProEtale.exists_galoisTowerMoebiusDecomposition`). The reduction of an invariant
retraction is invariant, the Galois action being defined with integral coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- A natural number prime to `ℓ` is a unit in `𝒪_E ⧸ ℓⁿ`. -/
lemma isUnit_natCast_integersModPow (n : ℕ) {d : ℕ} (hd : ¬ ℓ ∣ d) :
    IsUnit (d : integersModPow ℓ E n) := by
  have hcop : Nat.Coprime d (ℓ ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hd))
  have h := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (integersModPow ℓ E n))
  have h0 : ((ℓ ^ n : ℕ) : integersModPow ℓ E n) = 0 := by
    change integersModPowMk ℓ E n ((ℓ ^ n : ℕ) : integers ℓ E) = 0
    rw [Nat.cast_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  simp only [eq_intCast, Int.cast_natCast, h0] at h
  exact isCoprime_zero_right.1 h

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-- **The Galois invariant retraction of the derived unit is unique** (torsion coefficients in
which the degrees of the finite Galois subextensions of `Ω/L` are invertible): two retractions of
`C ⟶ Rg_* Lg^* C` fixed by the derived unit transports along all the `Spec σ`, `σ ∈ Gal(Ω/L)`,
are equal, for `C` bounded below of étale origin. -/
theorem eq_of_invariant_retraction_derivedUnit_galois (T₀ : Type) [TopologicalSpace T₀]
    [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) G)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) G
      ((finiteCoefficientDerivedEquivalence G T₀).functor.obj C))
    {R R' : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj T₀⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.continuousMapRingObj T₀⟧).obj C) ⟶ C}
    (hR : (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app C ≫ R = 𝟙 _)
    (hR' : (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app C ≫ R' = 𝟙 _)
    (hinv : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.continuousMapRingObj T₀)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) C ≫ R = R)
    (hinv' : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.continuousMapRingObj T₀)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) C ≫ R' = R') :
    R = R' := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ C hC
  choose F₀ hF₀ using hterms
  have hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) G)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 N) := fun j N ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) N
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  obtain ⟨D, hD⟩ := exists_galoisTowerMoebiusDecomposition h (Profinite.continuousMapRingObj T₀) hd
    K hc
  have key (S : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj T₀⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.continuousMapRingObj T₀⟧).obj C) ⟶ C)
      (hS : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.continuousMapRingObj T₀)
        (pullbackAction h _ specGaloisAction_comp σ)
        (pullbackAction_fst h _ specGaloisAction_comp σ)
        (pullbackAction_fst h _ specGaloisAction_comp σ) C ≫ S = S) (i : D.ι) (b : D.A i) :
      derivedUnitTransport (Profinite.continuousMapRingObj T₀) (D.σ i b) (D.hσ i b) (D.hσ i b)
        C ≫ S = S := by
    obtain ⟨σ, hσ⟩ := hD i b
    have gen : ∀ (s : _ ⟶ _)
        (hs : s ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) =
          pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))),
        s = pullbackAction h _ specGaloisAction_comp σ →
          derivedUnitTransport (Profinite.continuousMapRingObj T₀) s hs hs C ≫ S = S := by
      rintro s hs rfl
      exact hS σ
    exact gen _ _ hσ
  exact D.eq_of_retraction_derivedUnit_of_iso a hK e hR hR' (key R hinv) (key R' hinv')

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- **Transport of unique invariant retractions along an isomorphism.** Let `c : B ⟶ B'` be an
isomorphism intertwining endomorphisms `a σ` of `B` and `a' σ` of `B'`, and `t ≫ c = η`. If the
retractions of `η` fixed by all the `a' σ` are unique, so are those of `t` fixed by the `a σ`. -/
lemma _root_.CategoryTheory.eq_of_retraction_of_iso {C : Type*} [Category C] {A B B' : C}
    {t : A ⟶ B} {c : B ⟶ B'} [IsIso c] {η : A ⟶ B'} (e : t ≫ c = η) {ι : Type*}
    {a : ι → (B ⟶ B)} {a' : ι → (B' ⟶ B')} (ea : ∀ σ, a σ ≫ c = c ≫ a' σ)
    (H : ∀ R R' : B' ⟶ A, η ≫ R = 𝟙 A → η ≫ R' = 𝟙 A → (∀ σ, a' σ ≫ R = R) →
      (∀ σ, a' σ ≫ R' = R') → R = R')
    {r r' : B ⟶ A} (hr : ∀ σ, a σ ≫ r = r) (hr' : ∀ σ, a σ ≫ r' = r') (h₁ : t ≫ r = 𝟙 A)
    (h₁' : t ≫ r' = 𝟙 A) : r = r' := by
  have he : η ≫ inv c = t := by rw [← e, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hea (σ) : a' σ ≫ inv c = inv c ≫ a σ := by
    rw [IsIso.comp_inv_eq, Category.assoc, ea, IsIso.inv_hom_id_assoc]
  have key := H (inv c ≫ r) (inv c ≫ r') (by rw [← Category.assoc, he, h₁])
    (by rw [← Category.assoc, he, h₁']) (fun σ ↦ by rw [← Category.assoc, hea, Category.assoc, hr])
    (fun σ ↦ by rw [← Category.assoc, hea, Category.assoc, hr'])
  exact (cancel_epi _).1 key

/-- A composite `t ≫ c ≫ R` is the identity if `t ≫ c = η` and `η ≫ R = 𝟙`. -/
lemma _root_.CategoryTheory.comp_comp_eq_id_of_comp_eq {C : Type*} [Category C] {A B B' : C}
    {t : A ⟶ B} {c : B ⟶ B'} {η : A ⟶ B'} {R : B' ⟶ A} (e : t ≫ c = η) (hR : η ≫ R = 𝟙 A) :
    t ≫ c ≫ R = 𝟙 A := by
  rw [← Category.assoc, e, hR]

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-- `ProEtale.exists_invariant_retraction_derivedUnit_galois` for the coefficient ring
`(𝒪_E ⧸ ℓⁿ)̲` written as `Profinite.integersModPowRingObj`. -/
theorem exists_invariant_retraction_derivedUnit_galois_integersModPow (n : ℕ)
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω,
      IsUnit ((Module.finrank L L' : ℕ) : integersModPow ℓ E.1 n))
    (X : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 n) G)))
    (hX : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) G
      ((finiteCoefficientDerivedEquivalence G (integersModPow ℓ E.1 n)).functor.obj X)) :
    ∃ R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.integersModPowRingObj ℓ E.1 n⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.integersModPowRingObj ℓ E.1 n⟧).obj X) ⟶ X,
      (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app X ≫ R =
        𝟙 _ ∧
      ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.integersModPowRingObj ℓ E.1 n)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) X ≫ R = R := by
  exact_mod_proofs exists_invariant_retraction_derivedUnit_galois h (integersModPow ℓ E.1 n) hp X hX

/-- `ProEtale.eq_of_invariant_retraction_derivedUnit_galois` for the coefficient ring
`(𝒪_E ⧸ ℓⁿ)̲` written as `Profinite.integersModPowRingObj`. -/
theorem eq_of_invariant_retraction_derivedUnit_galois_integersModPow (n : ℕ)
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω,
      IsUnit ((Module.finrank L L' : ℕ) : integersModPow ℓ E.1 n))
    (X : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 n) G)))
    (hX : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) G
      ((finiteCoefficientDerivedEquivalence G (integersModPow ℓ E.1 n)).functor.obj X))
    (R R' : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.integersModPowRingObj ℓ E.1 n⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.integersModPowRingObj ℓ E.1 n⟧).obj X) ⟶ X)
    (hR : (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E.1 n)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app X ≫ R = 𝟙 _)
    (hR' : (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E.1 n)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app X ≫ R' = 𝟙 _)
    (hinv : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.integersModPowRingObj ℓ E.1 n)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) X ≫ R = R)
    (hinv' : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.integersModPowRingObj ℓ E.1 n)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) X ≫ R' = R') :
    R = R' := by
  have key := @eq_of_invariant_retraction_derivedUnit_galois L Ω _ _ _ _ G h
    (integersModPow ℓ E.1 n) _ _ _ _ _ hp X hX
  exact_mod_proofs key hR hR' hinv hinv'


omit [IsGalois L Ω] in
/-- The comparison of the reduction of `Rg_* Lg^* K` with `Rg_* Lg^*` of the reduction is an
isomorphism, for `K` bounded below. -/
lemma isIso_derivedPushPullExtendScalarsHom_integersModPow (n : ℕ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) G))) (m : ℤ) [K.IsGE m] :
    IsIso (derivedPushPullExtendScalarsHom
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1)
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K m
  have := isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app ℓ E.1 n
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
    ((L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
      Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) m
  infer_instance

-- the retraction is matched against the large types of the reductions
/-- **Existence of invariant torsion retractions**: the reduction modulo `ℓⁿ` of the unit
`K ⟶ Rg_* Lg^* K` has a retraction invariant under the reductions of the Galois action. -/
lemma exists_retraction_map_unit_integersModPow (n : ℕ)
    (hunit : ∀ L' : FiniteGaloisIntermediateField L Ω,
      IsUnit ((Module.finrank L L' : ℕ) : integersModPow ℓ E.1 n))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) G)))
    (hred : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) G
      ((finiteCoefficientDerivedEquivalence G (integersModPow ℓ E.1 n)).functor.obj
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K))) :
    ∃ r, (∀ σ : Ω ≃ₐ[L] Ω, L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        (derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) K) ≫ r = r) ∧
      L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) ≫ r =
        𝟙 _ := by
  have hR := exists_invariant_retraction_derivedUnit_galois_integersModPow E h n hunit _ hred
  refine ⟨derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K ≫ hR.choose,
    fun σ ↦ ?_, ?_⟩
  · have e : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        (derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) K) ≫
        derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K =
      derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K ≫
        derivedUnitTransport (Profinite.integersModPowRingObj ℓ E.1 n)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K) := by
      exact_mod_proofs (map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom
        (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
        (pullbackAction h _ specGaloisAction_comp σ)
        (pullbackAction_fst h _ specGaloisAction_comp σ)
        (pullbackAction_fst h _ specGaloisAction_comp σ) K)
    exact_mod_proofs (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hR.choose) e).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hR.choose_spec.2 σ))))
  · have e : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) ≫
        derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K =
      (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K) := by
      exact_mod_proofs (map_unit_comp_derivedPushPullExtendScalarsHom
        (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K)
    exact comp_comp_eq_id_of_comp_eq e hR.choose_spec.1

-- the retractions are compared through the large types of the reductions
/-- **Uniqueness of invariant torsion retractions**: two retractions of the reduction modulo `ℓⁿ`
of the unit `K ⟶ Rg_* Lg^* K`, invariant under the reductions of the Galois action, are equal. -/
lemma eq_of_retraction_map_unit_integersModPow (n : ℕ)
    (hunit : ∀ L' : FiniteGaloisIntermediateField L Ω,
      IsUnit ((Module.finrank L L' : ℕ) : integersModPow ℓ E.1 n))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) G))) (m : ℤ) [K.IsGE m]
    (hred : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) G
      ((finiteCoefficientDerivedEquivalence G (integersModPow ℓ E.1 n)).functor.obj
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K)))
    (r r' : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj
        (R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
          Profinite.padicIntegersRingObj ℓ E.1⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.padicIntegersRingObj ℓ E.1⟧).obj K)) ⟶
      L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K)
    (hr : ∀ σ : Ω ≃ₐ[L] Ω, L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        (derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) K) ≫ r = r)
    (hr' : ∀ σ : Ω ≃ₐ[L] Ω, L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        (derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) K) ≫ r' = r')
    (h₁ : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) ≫ r =
        𝟙 _)
    (h₁' : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) ≫ r' =
        𝟙 _) :
    r = r' := by
  have := isIso_derivedPushPullExtendScalarsHom_integersModPow (Ω := Ω) E h n K m
  have e : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) ≫
        derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K =
      (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K) := by
    exact_mod_proofs (map_unit_comp_derivedPushPullExtendScalarsHom
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K)
  have ea (σ : Ω ≃ₐ[L] Ω) : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).map
        (derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) K) ≫
        derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K =
      derivedPushPullExtendScalarsHom (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K ≫
        derivedUnitTransport (Profinite.integersModPowRingObj ℓ E.1 n)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 n)).obj K) := by
    exact_mod_proofs (map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) K)
  refine eq_of_retraction_of_iso e ea ?_ hr hr' h₁ h₁'
  exact eq_of_invariant_retraction_derivedUnit_galois_integersModPow E h n hunit _ hred

-- the torsion retractions are matched against the large types of the reductions
/-- **The derived unit of an infinite Galois extension of degrees prime to `ℓ` splits with
`𝒪_E`-coefficients** at every derived complete complex whose reductions modulo `ℓⁿ⁺¹` are bounded
below of étale origin. -/
theorem isSplitMono_derivedUnit_galois_padicIntegers
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, ¬ ℓ ∣ Module.finrank L L')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) G)))
    (hK : derivedCompleteIntegers ℓ E G K) (m : ℤ) [K.IsGE m]
    (hred : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 (n + 1)))) G
      ((finiteCoefficientDerivedEquivalence G (integersModPow ℓ E.1 (n + 1))).functor.obj
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).obj K))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) := by
  have hunit (n : ℕ) : ∀ L' : FiniteGaloisIntermediateField L Ω,
      IsUnit ((Module.finrank L L' : ℕ) : integersModPow ℓ E.1 n) := fun L' ↦
    isUnit_natCast_integersModPow E.1 n (hp L')
  refine ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions
    ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) hK
    (fun n r ↦ ∀ σ : Ω ≃ₐ[L] Ω, L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).map
        (derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) K) ≫ r = r)
    ?_ ?_ ?_
  · intro n
    exact exists_retraction_map_unit_integersModPow E h (n + 1) (hunit _) K (hred n)
  · intro n
    exact eq_of_retraction_map_unit_integersModPow E h (n + 1) (hunit _) K m (hred n)
  · intro n r hr _ σ
    exact (Mod.derivedExtendScalarsReduction_map_comp _ _ _ _ _ r).symm.trans
      (congrArg (Mod.derivedExtendScalarsReduction _ _ _ _) (hr σ))

end AlgebraicGeometry.ProEtale.CondensedRing
