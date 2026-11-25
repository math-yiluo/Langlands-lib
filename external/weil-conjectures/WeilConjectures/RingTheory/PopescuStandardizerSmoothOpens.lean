/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Extension.Presentation.Basic
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

/-!
# Smooth opens of the polynomial standardizer

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-standardizer and item-elkik.
-/

@[expose] public section

universe u v t
namespace Algebra

private theorem lift_presentation
    {A : Type v} {B : Type t} {T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] {ι σ : Type*} (P : Presentation A B ι σ)
    (g : A →+* T) (x : ι → T)
    (hr : ∀ i, MvPolynomial.eval₂Hom g x (P.relation i) = 0) :
    ∃ φ : B →+* T,
      (∀ a, φ (algebraMap A B a) = g a) ∧ (∀ i, φ (P.val i) = x i) := by
  let ev := MvPolynomial.eval₂Hom g x
  have hker : P.ker ≤ RingHom.ker ev := by
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hr i
  let φ : B →+* T :=
    (Ideal.Quotient.lift P.ker ev hker).comp P.quotientEquiv.symm.toRingHom
  have hφ (p : P.Ring) : φ (algebraMap P.Ring B p) = ev p := by
    change Ideal.Quotient.lift P.ker ev hker
      (P.quotientEquiv.symm (algebraMap P.Ring B p)) = ev p
    rw [← P.quotientEquiv_mk p, P.quotientEquiv.symm_apply_apply]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro a
    have hh := hφ (MvPolynomial.C a)
    simpa only [ev, P.algebraMap_apply, MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C] using hh
  · intro i
    have hh := hφ (MvPolynomial.X i)
    simpa only [ev, P.algebraMap_apply, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X'] using hh

/-- The coefficient opens of the standardizer are smooth over the
polynomial parameter ring.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-standardizer and item-elkik.
(blueprint: lem-weil-pbc-popescu-standardizer-smooth-opens).

Proof: The coefficient localization A[1/a_j] is smooth over k because a_j
belongs to the singular ideal. B[1/a_j] is finitely presented over S: B is of
finite type over k, hence over S, the polynomial ring S is Noetherian, and a
principal localization preserves finite presentation. Use the square-zero
lifting criterion for formal smoothness. Given B[1/a_j] → T/I over S with
I²=0, extend its coefficient map to A[1/a_j] and lift that map over k to T.
This gives a lifted coefficient map α with α(a_j) invertible. Choose arbitrary
lifts z_il of the given auxiliary generators. In each relation, the discrepancy
ε_i = X_i^(2N) - sum_l z_il α(a_l) maps to zero in T/I. Replace z_ij by
z_ij + ε_i α(a_j)^(-1), keeping all other generators unchanged. All relations
now hold exactly, and every corrected generator has the prescribed reduction.
The universal property of the presentation gives B → T. This map respects S
because its x_i-values were fixed by S, and extends to B[1/a_j] because α(a_j)
is a unit. Checking coefficients and generators shows that its reduction is
the given map. Thus B[1/a_j] is formally smooth and finitely presented over S.
If s=0 there is no coefficient-open assertion; d=0 gives the same proof with
no auxiliary relations to correct. No ring is assumed nontrivial. -/
theorem popescu_standardizer_coefficient_smooth
    {k : Type u} {A : Type v} {B : Type t}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B]
    [FinitePresentation k A] {d s : ℕ} (N : ℕ) (_hN : 0 < N)
    (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    [Algebra (MvPolynomial (Fin d) k) B]
    [IsScalarTower k (MvPolynomial (Fin d) k) B]
    (P : Presentation A B (Fin d ⊕ (Fin d × Fin s)) (Fin d))
    (hval : ∀ i, P.val (Sum.inl i) =
      algebraMap (MvPolynomial (Fin d) k) B (MvPolynomial.X i))
    (hrel : ∀ i : Fin d, P.relation i =
      (MvPolynomial.X (Sum.inl i)) ^ (2 * N) -
        ∑ j : Fin s, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j)) :
    ∀ j, Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A B (a j))) := by
  classical
  let S := MvPolynomial (Fin d) k
  have : FinitePresentation A B := P.finitePresentation_of_isFinite
  have : FiniteType k B := FiniteType.trans
    (inferInstance : FiniteType k A) (inferInstance : FiniteType A B)
  have : FiniteType S B := FiniteType.of_restrictScalars_finiteType k S B
  have : FinitePresentation S B := FinitePresentation.of_finiteType.mp inferInstance
  intro j
  let b := algebraMap A B (a j)
  let L := Localization.Away b
  have ha' : a j ∈ singularIdeal k A := ha ▸ Ideal.subset_span ⟨j, rfl⟩
  have : Smooth k (Localization.Away (a j)) :=
    smooth_localization_of_mem_singularIdeal k A (a j) ha'
  have : FormallySmooth S L := by
    apply FormallySmooth.iff_comp_surjective.mpr
    intro T _ _ I hI f
    let : Algebra k T := ((algebraMap S T).comp (algebraMap k S)).toAlgebra
    have : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' rfl
    let g : A →ₐ[k] T ⧸ I :=
      (f.restrictScalars k).comp (IsScalarTower.toAlgHom k A L)
    have hgunit : IsUnit (g (a j)) := by
      exact (IsLocalization.Away.algebraMap_isUnit (S := L) b).map f
    let gloc : Localization.Away (a j) →ₐ[k] T ⧸ I :=
      IsLocalization.Away.liftAlgHom (a j) hgunit
    obtain ⟨αloc, hαloc⟩ := FormallySmooth.exists_lift I ⟨2, hI⟩ gloc
    let α : A →ₐ[k] T := αloc.comp (IsScalarTower.toAlgHom k A (Localization.Away (a j)))
    have hα (x : A) : Ideal.Quotient.mk I (α x) = f (algebraMap A L x) := by
      have hh := DFunLike.congr_fun hαloc (algebraMap A (Localization.Away (a j)) x)
      change Ideal.Quotient.mk I
        (αloc (algebraMap A (Localization.Away (a j)) x)) = _
      change Ideal.Quotient.mk I
        (αloc (algebraMap A (Localization.Away (a j)) x)) =
        gloc (algebraMap A (Localization.Away (a j)) x) at hh
      rw [hh]
      exact IsLocalization.Away.lift_eq (a j) hgunit x
    obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (a j)) (a j)).map αloc
    have hu' : (u : T) = α (a j) := hu
    choose z hz using fun ij : Fin d × Fin s ↦
      Ideal.Quotient.mk_surjective (f (algebraMap B L (P.val (Sum.inr ij))))
    let ε (i : Fin d) := algebraMap S T (MvPolynomial.X i) ^ (2 * N) -
      ∑ l : Fin s, z (i, l) * α (a l)
    have hε (i : Fin d) : Ideal.Quotient.mk I (ε i) = 0 := by
      have hh := congrArg (fun x ↦ f (algebraMap B L x)) (P.aeval_val_relation i)
      rw [hrel i] at hh
      simp only [map_sub, map_pow, map_sum, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, map_zero, hval] at hh
      simp only [ε, map_sub, map_pow, map_sum, map_mul, hz, hα]
      rw [← IsScalarTower.algebraMap_apply S B L, f.commutes] at hh
      simp only [← IsScalarTower.algebraMap_apply A B L] at hh
      simpa only [← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply S T (T ⧸ I)] using hh
    let z' (i : Fin d) (l : Fin s) :=
      z (i, l) + if l = j then ε i * ↑u⁻¹ else 0
    have hz' (i : Fin d) (l : Fin s) : Ideal.Quotient.mk I (z' i l) =
        f (algebraMap B L (P.val (Sum.inr (i, l)))) := by
      simp only [z', map_add, hz]
      split_ifs <;> simp [map_mul, hε]
    let xs : Fin d ⊕ (Fin d × Fin s) → T :=
      Sum.elim (fun i ↦ algebraMap S T (MvPolynomial.X i)) (fun ij ↦ z' ij.1 ij.2)
    have hr (i : Fin d) : MvPolynomial.eval₂Hom α.toRingHom xs (P.relation i) = 0 := by
      rw [hrel i]
      simp only [map_sub, map_pow, map_sum, map_mul, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_C, xs, Sum.elim_inl, Sum.elim_inr,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      simp only [z', add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← hu', mul_assoc, Units.inv_mul, mul_one]
      dsimp only [ε]
      ring
    obtain ⟨φ, hφA, hφx⟩ := lift_presentation P α.toRingHom xs hr
    have hφS : φ.comp (algebraMap S B) = algebraMap S T := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change φ (algebraMap S B (algebraMap k S r)) =
          algebraMap S T (algebraMap k S r)
        rw [← IsScalarTower.algebraMap_apply k S B,
          IsScalarTower.algebraMap_apply k A B, hφA,
          ← IsScalarTower.algebraMap_apply k S T]
        exact α.commutes r
      · intro i
        rw [RingHom.comp_apply, ← hval, hφx]
        rfl
    let φS : B →ₐ[S] T := { φ with commutes' := DFunLike.congr_fun hφS }
    have hφunit : IsUnit (φS b) := by
      rw [show φS b = α (a j) from hφA (a j), ← hu']
      exact u.isUnit
    let ψ : L →ₐ[S] T := IsLocalization.Away.liftAlgHom b hφunit
    refine ⟨ψ, ?_⟩
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers b)
    apply RingHom.ext
    intro x
    change Ideal.Quotient.mk I (ψ (algebraMap B L x)) = f (algebraMap B L x)
    rw [show ψ (algebraMap B L x) = φ x from
      IsLocalization.Away.lift_eq b hφunit x]
    obtain ⟨p, rfl⟩ := P.aeval_val_surjective x
    have hv (i : Fin d ⊕ (Fin d × Fin s)) :
        Ideal.Quotient.mk I (φ (P.val i)) = f (algebraMap B L (P.val i)) := by
      rw [hφx]
      cases i with
      | inl i =>
        change Ideal.Quotient.mk I (algebraMap S T (MvPolynomial.X i)) = _
        rw [hval, ← IsScalarTower.algebraMap_apply S B L, f.commutes]
        exact (IsScalarTower.algebraMap_apply S T (T ⧸ I) (MvPolynomial.X i)).symm
      | inr ij => exact hz' ij.1 ij.2
    induction p using MvPolynomial.induction_on with
    | C x =>
      rw [MvPolynomial.aeval_C, hφA]
      exact hα x
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X, hp, hv]
  exact ⟨inferInstance, inferInstance⟩

end Algebra
