/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.PopescuStandardizerSmoothOpens
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth
import WeilConjectures.RingTheory.ImprovePresentation
import WeilConjectures.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
import WeilConjectures.RingTheory.StrictlyStandardBaseChange
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The universal standardizer before choosing parameters

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-generators through item-strictly-standard and item-first-solve.
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace Algebra

private theorem strictlyStandard_zero
    {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]
    [FinitePresentation R D] : IsStrictlyStandardElement (R := R) (0 : D) := by
  classical
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin R D
  refine ⟨n, m, 0, P, Nat.zero_le _, fun _ ↦ 0, by simp, ?_⟩
  intro j _
  apply Ideal.mem_sup_right
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    exact P.aeval_val_σ 0
  · exact Ideal.subset_span ⟨j, rfl⟩

private theorem strictlyStandard_power_of_free
    {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]
    [FinitePresentation R D] (x : D)
    [Smooth R (Localization.Away x)]
    [Module.Free (Localization.Away x) (KaehlerDifferential R (Localization.Away x))] :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (x ^ e) := by
  classical
  let T := Localization.Away x
  let M := KaehlerDifferential R T
  let b := Module.Free.chooseBasis T M
  let n := Fintype.card (Module.Free.ChooseBasisIndex T M)
  let b' : Module.Basis (Fin n) T M := b.reindex (Fintype.equivFin _)
  let e : (M × (Fin 0 →₀ T)) ≃ₗ[T] (Fin n →₀ T) :=
    (LinearEquiv.prodUnique (R := T) (M := M) (M₂ := Fin 0 →₀ T)).trans b'.repr
  exact smooth_free_differentials_strictly_standard_power R D x 0 n ⟨e⟩

/-- The universal algebra with relations `x_i^(2N) = sum_j z_ij a_j` has an
improved presentation whose standard powers and singular-ideal inclusion survive
every polynomial base change. This lemma chooses no parameters in the target ring
and no Artinian solution.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-generators, item-standardizer, item-elkik, item-strictly-standard,
and the justification of item-first-solve.
(blueprint: lem-weil-pbc-popescu-universal-standardizer).

Proof: Since A is finitely presented over the field k, it is Noetherian. Choose
finite generators a_j of its singular ideal. Construct B as the quotient of the
polynomial algebra over A on x_i,z_ij by the displayed d relations; its presentation
P is the quotient presentation. Give B the k[x]-structure sending X_i to x_i.
On each a_j-open, eliminate z_ij to identify the localization with a polynomial
algebra over A localized at a_j, after extending scalars to k[x]. This is smooth.
The relations show that the a_j generate the unit ideal on each x_i-open, so these
opens are smooth too. Apply 07CE to obtain C₀ and its retraction ρ. The improved
differentials are finite free on each x_i-open. Over the Noetherian base k[x], C₀
is finitely presented; 07EZ(e) supplies a common positive c for which every x_i^c
is strictly standard. Define β₀ by A → B → C₀. The retraction gives ρβ₀ = A → B.
For any base change, smoothness on the a_j-opens persists, so the extended singular
ideal of A lies in the singular ideal of the base-changed C₀. Extend along hρ and
take radicals to get the Popescu-ideal inclusion. Strict standardness persists by
07CC. Zero is strictly standard using any finite presentation, c = 0 in the
definition and zero coefficients of the minors: the lift of zero differs from
zero by an element of the relation ideal, so its product with a relation is in
the square of that ideal. All carriers can be the finite polynomial quotients
and the explicit symmetric algebra used by 07CE, in Type(max u v). -/
theorem exists_popescu_universal_standardizer
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] (d N : ℕ) (hN : 0 < N) :
    let S := MvPolynomial (Fin d) k
    ∃ (s : ℕ) (a : Fin s → A), Ideal.span (Set.range a) = singularIdeal k A ∧
      ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra k B)
        (_ : Algebra A B) (_ : IsScalarTower k A B)
        (_ : Algebra S B) (_ : IsScalarTower k S B)
        (P : Presentation A B (Fin d ⊕ (Fin d × Fin s)) (Fin d)),
        (∀ i, P.val (Sum.inl i) = algebraMap S B (MvPolynomial.X i)) ∧
        (∀ i : Fin d, P.relation i =
          ((MvPolynomial.X (Sum.inl i) :
            MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A) ^ (2 * N) -
            ∑ j : Fin s, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j) :
              MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A)) ∧
      ∃ (C₀ : Type (max u v)) (_ : CommRing C₀) (_ : Algebra k C₀)
        (_ : Algebra S C₀) (_ : IsScalarTower k S C₀)
        (_ : FinitePresentation S C₀)
        (β₀ : A →ₐ[k] C₀) (ρ : C₀ →ₐ[S] B) (c : ℕ),
        0 < c ∧ (ρ.restrictScalars k).comp β₀ = IsScalarTower.toAlgHom k A B ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra S R]
          [IsScalarTower k S R] [Algebra R Λ] [IsScalarTower k R Λ]
          [Algebra S Λ] [IsScalarTower S R Λ] [IsScalarTower k S Λ]
          (h : B →ₐ[S] Λ),
          let C := R ⊗[S] C₀
          let γ := AlgHom.liftEquiv S R C₀ Λ (h.comp ρ)
          popescuIdeal ((h.restrictScalars k).comp (IsScalarTower.toAlgHom k A B)) ≤
              popescuIdeal γ ∧
            ∀ x : R, (x = 0 ∨ ∃ i : Fin d,
              x = algebraMap S R (MvPolynomial.X i ^ c)) →
              IsStrictlyStandardElement (R := R) (algebraMap R C x) := by
  classical
  let S := MvPolynomial (Fin d) k
  have : IsNoetherianRing A := FiniteType.isNoetherianRing k A
  obtain ⟨s, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (singularIdeal k A))
  change Ideal.span (Set.range a) = singularIdeal k A at ha
  let f : Fin d → MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A := fun i ↦
    MvPolynomial.X (Sum.inl i) ^ (2 * N) -
      ∑ j : Fin s, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j)
  let Q := MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A ⧸ Ideal.span (Set.range f)
  let B := ULift.{u} Q
  let : Algebra k B := inferInstance
  let : Algebra A B := inferInstance
  have : IsScalarTower k A B := inferInstance
  let P : Presentation A B (Fin d ⊕ (Fin d × Fin s)) (Fin d) :=
    (Presentation.naive (v := f)).ofAlgEquiv (ULift.algEquiv (R := A)).symm
  let φ : S →ₐ[k] B := MvPolynomial.aeval fun i ↦ P.val (Sum.inl i)
  let : Algebra S B := φ.toRingHom.toAlgebra
  have : IsScalarTower k S B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hval : ∀ i, P.val (Sum.inl i) = algebraMap S B (MvPolynomial.X i) := by
    intro i
    change P.val (Sum.inl i) = φ (MvPolynomial.X i)
    exact (MvPolynomial.aeval_X (R := k)
      (fun i : Fin d ↦ P.val (Sum.inl i)) i).symm
  have hrel : ∀ i, P.relation i = f i := fun _ ↦ rfl
  refine ⟨s, a, ha, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, P, hval, hrel, ?_⟩
  have : FinitePresentation A B := P.finitePresentation_of_isFinite
  have : FiniteType k B := FiniteType.trans (inferInstance : FiniteType k A)
    (inferInstance : FiniteType A B)
  have : FiniteType S B := FiniteType.of_restrictScalars_finiteType k S B
  have : FinitePresentation S B :=
    FinitePresentation.of_finiteType.mp (inferInstance : FiniteType S B)
  have haj := popescu_standardizer_coefficient_smooth N hN a ha P hval hrel
  have hxi (i : Fin d) : Smooth S
      (Localization.Away (algebraMap S B (MvPolynomial.X i))) := by
    apply smooth_localization_of_mem_singularIdeal S B
    have hz := P.aeval_val_relation i
    rw [hrel i] at hz
    simp only [f, map_sub, map_pow, map_sum, map_mul, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C] at hz
    rw [hval i] at hz
    apply singularIdeal_isRadical S B
    apply Ideal.mem_radical_iff.mpr
    refine ⟨2 * N, ?_⟩
    rw [sub_eq_zero.mp hz]
    apply Ideal.sum_mem
    intro j _
    exact (singularIdeal S B).mul_mem_left _ (Ideal.le_radical (Ideal.subset_span (haj j)))
  obtain ⟨C₀, _, _, hC, ρ, hρ, hloc⟩ :=
    exists_finiteType_retract_smooth_free_differentials S B
  let : Algebra S C₀ := ((algebraMap B C₀).comp (algebraMap S B)).toAlgebra
  have : IsScalarTower S B C₀ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k C₀ := ((algebraMap S C₀).comp (algebraMap k S)).toAlgebra
  have : IsScalarTower k S C₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k B C₀ := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    simp only [IsScalarTower.algebraMap_apply k S B, IsScalarTower.algebraMap_apply k S C₀,
      IsScalarTower.algebraMap_apply S B C₀])
  have : FiniteType B C₀ := hC
  have : FiniteType S C₀ := FiniteType.trans (inferInstance : FiniteType S B) hC
  have : FinitePresentation S C₀ :=
    FinitePresentation.of_finiteType.mp (inferInstance : FiniteType S C₀)
  let β₀ : A →ₐ[k] C₀ :=
    (IsScalarTower.toAlgHom k B C₀).comp (IsScalarTower.toAlgHom k A B)
  let ρS : C₀ →ₐ[S] B := ρ.restrictScalars S
  have hcomp : (ρS.restrictScalars k).comp β₀ = IsScalarTower.toAlgHom k A B := by
    apply AlgHom.ext
    intro x
    exact hρ (algebraMap A B x)
  have hpowers (i : Fin d) : ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := S) ((algebraMap S C₀ (MvPolynomial.X i)) ^ e) := by
    obtain ⟨hs, hf⟩ := hloc (algebraMap S B (MvPolynomial.X i)) (hxi i)
    rw [← IsScalarTower.algebraMap_apply S B C₀] at hs hf
    have : Smooth S (Localization.Away (algebraMap S C₀ (MvPolynomial.X i))) := hs
    have : Module.Free (Localization.Away (algebraMap S C₀ (MvPolynomial.X i)))
        (KaehlerDifferential S (Localization.Away (algebraMap S C₀ (MvPolynomial.X i)))) := hf
    exact strictlyStandard_power_of_free _
  choose e hepos he using hpowers
  let c := max 1 (Finset.univ.sup e)
  have hc : 0 < c := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hstandard (i : Fin d) : IsStrictlyStandardElement (R := S)
      (algebraMap S C₀ (MvPolynomial.X i ^ c)) := by
    rw [map_pow]
    exact he i c ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _))
  refine ⟨C₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, β₀, ρS, c, hc, hcomp, ?_⟩
  intro R _ _ _ _ _ _ _ _ _ h
  let C := R ⊗[S] C₀
  let γ := AlgHom.liftEquiv S R C₀ Λ (h.comp ρS)
  constructor
  · have hsing : Ideal.map β₀.toRingHom (singularIdeal k A) ≤ singularIdeal S C₀ := by
      rw [← ha, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro x ⟨_, ⟨j, rfl⟩, rfl⟩
      apply Ideal.le_radical
      apply Ideal.subset_span
      exact (hloc (algebraMap A B (a j)) (haj j)).1
    let κ : C₀ →ₐ[S] C := TensorProduct.includeRight
    have hbase : Ideal.map κ.toRingHom (singularIdeal S C₀) ≤ singularIdeal R C := by
      unfold singularIdeal
      refine (Ideal.map_radical_le κ.toRingHom).trans (Ideal.radical_mono ?_)
      rw [Ideal.map_le_iff_le_comap]
      apply Ideal.span_le.mpr
      intro x hx
      apply Ideal.subset_span
      change Smooth R (Localization.Away (κ x))
      have : Smooth S (Localization.Away x) := hx
      exact Smooth.of_equiv
        (IsLocalization.Away.tensorProductEquivTMulRight S R x (Localization.Away x))
    have hγ : γ.toRingHom.comp κ.toRingHom = (h.comp ρS).toRingHom := by
      ext x
      change AlgHom.liftEquiv S R C₀ Λ (h.comp ρS) (1 ⊗ₜ[S] x) = _
      rw [AlgHom.liftEquiv_tmul, one_smul]
      rfl
    have hmap : γ.toRingHom.comp (κ.toRingHom.comp β₀.toRingHom) =
        ((h.restrictScalars k).comp (IsScalarTower.toAlgHom k A B)).toRingHom := by
      rw [← RingHom.comp_assoc, hγ]
      change ((h.restrictScalars k).comp ((ρS.restrictScalars k).comp β₀)).toRingHom = _
      rw [hcomp]
    unfold popescuIdeal
    apply Ideal.radical_mono
    have hh := (Ideal.map_mono (f := κ.toRingHom) hsing).trans hbase
    have hh' := Ideal.map_mono (f := γ.toRingHom) hh
    rwa [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hmap] at hh'
  · intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · simpa only [map_zero] using (strictlyStandard_zero (R := R) (D := C))
    · have hs := (standardElements_baseChange
        (R := S) (R' := R) (algebraMap S C₀ (MvPolynomial.X i ^ c))).2 (hstandard i)
      convert hs using 1
      change algebraMap R C (algebraMap S R (MvPolynomial.X i ^ c)) =
        (TensorProduct.includeRight : C₀ →ₐ[S] C)
          (algebraMap S C₀ (MvPolynomial.X i ^ c))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S R C]

end Algebra
