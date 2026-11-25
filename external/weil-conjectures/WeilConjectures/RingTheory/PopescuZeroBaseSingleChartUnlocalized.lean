/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # The unlocalized zero-base single-chart presentation

Source: Stacks Project, Tag 07CP, the coefficient reduction in the calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-unlocalized).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial scalar extension commutes with taking a quotient. -/
private theorem baseChangeQuotient
    (S : Type*) (B : Type*) [CommRing S] [CommRing B] [Algebra S B]
    (σ : Type*) (J : Ideal (MvPolynomial σ S)) :
    ∃ e : B ⊗[S] (MvPolynomial σ S ⧸ J) ≃ₐ[B]
        MvPolynomial σ B ⧸ J.map (MvPolynomial.map (algebraMap S B)),
      ∀ p, e (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk J p)) =
        Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap S B) p) := by
  let t := MvPolynomial.algebraTensorAlgEquiv S B (σ := σ)
  let K := J.map (Algebra.TensorProduct.includeRight (R := S) (A := B))
  have ht : t.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := S) (A := B)).toRingHom =
      MvPolynomial.map (algebraMap S B) := by
    apply RingHom.ext
    intro p
    simp [t, Algebra.TensorProduct.includeRight_apply]
  have hK : J.map (MvPolynomial.map (algebraMap S B)) = K.map t.toRingHom := by
    change _ = (J.map
      (Algebra.TensorProduct.includeRight (R := S) (A := B)).toRingHom).map _
    rw [Ideal.map_map, ht]
  let e := (Algebra.TensorProduct.tensorQuotientEquiv (R := S) B
    (MvPolynomial σ S) B J).trans (Ideal.quotientEquivAlg K _ t hK)
  refine ⟨e, ?_⟩
  intro p
  change Ideal.quotientEquivAlg K _ t hK
    ((Algebra.TensorProduct.tensorQuotientEquiv (R := S) B
      (MvPolynomial σ S) B J) (1 ⊗ₜ[S] Ideal.Quotient.mk J p)) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk]
  simp [t]

set_option backward.isDefEq.respectTransparency false in
/-- Adjoining variables and then quotienting can be done in two stages. -/
private theorem iteratedQuotient
    (B : Type*) (A : Type*) [CommRing B] [CommRing A] [Algebra B A]
    (σ : Type*) (F : Ideal A) (G : Ideal (MvPolynomial σ A)) :
    let q := MvPolynomial.map (σ := σ) (Ideal.Quotient.mk F)
    ∃ e : (MvPolynomial σ (A ⧸ F) ⧸ G.map q) ≃ₐ[B]
        MvPolynomial σ A ⧸ (F.map MvPolynomial.C ⊔ G),
      ∀ p, e (Ideal.Quotient.mk _ (q p)) = Ideal.Quotient.mk _ p := by
  dsimp only
  let q := MvPolynomial.mapAlgHom (σ := σ) (Ideal.Quotient.mkₐ B F)
  let E := G.map q.toRingHom
  let D := F.map (MvPolynomial.C (σ := σ)) ⊔ G
  let φ := (Ideal.Quotient.mkₐ B E).comp q
  have hq : Function.Surjective q :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective.comp hq
  have hker : RingHom.ker φ.toRingHom = D := by
    rw [show φ.toRingHom = (Ideal.Quotient.mk E).comp q.toRingHom from rfl,
      ← RingHom.comap_ker, Ideal.mk_ker]
    dsimp only [E]
    rw [Ideal.comap_map_of_surjective q.toRingHom hq, ← RingHom.ker_eq_comap_bot]
    change G ⊔ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk F)) = D
    rw [MvPolynomial.ker_map, Ideal.mk_ker, sup_comm]
  let e := (Ideal.quotientEquivAlgOfEq B hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ)
  change ∃ e' : (MvPolynomial σ (A ⧸ F) ⧸ E) ≃ₐ[B]
      (MvPolynomial σ A ⧸ D),
    ∀ p, e' (Ideal.Quotient.mk E (q p)) = Ideal.Quotient.mk D p
  refine ⟨e.symm, ?_⟩
  intro p
  apply e.injective
  rw [e.apply_symm_apply]
  change φ p = e (Ideal.Quotient.mk D p)
  dsimp only [e, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := φ) hφ p).symm

set_option backward.isDefEq.respectTransparency false in
/-- Before localization, scalar extension removes precisely the pi terms.

Source: Stacks Project, Tag 07CP (lemma-lifting), the first line of the calculation
modulo pi, before inverting the chart element.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-unlocalized).

Proof: Tensor the original polynomial quotient with B. The tensor-quotient equivalence
identifies this with the quotient of B[x,z] by the coefficient images of the original
equations; the canonical ULift equivalence removes ULift. Since pi maps to zero,
the equations become f_l(x) and a_k(x)z_l minus the sum h_klj(x)z_j. Split the x and
z variables, and first quotient the coefficient polynomial ring B[x] by all f_l.
This yields the polynomial ring in z over B[x]/(f_l), modulo the displayed linear
relations. The map R to B factors through R/(pi squared), so the tensor-quotient and
polynomial base-change equivalences identify B[x]/(f_l) with
B tensor over R/(pi squared) with reducedQuotient. These maps send every polynomial
p(x) to its reduced coefficient class and each auxiliary variable to its own class.
The reverse maps are polynomial evaluation followed by the tensor and quotient
universal properties. Check the two composites on B, each x, and each z; polynomial,
tensor, and quotient extensionality gives identities and the stated coefficient
compatibility. This argument neither inverts a_k nor eliminates any variable and
requires no normalization or smoothness hypotheses. -/
theorem zero_base_single_chart_unlocalized (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    let L := B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] d.reducedQuotient
    let β : MvPolynomial (Fin d.n) R →+* L :=
      (Algebra.TensorProduct.includeRight (R := R ⧸ Ideal.span ({π ^ 2} : Set R))
        (A := B)).toRingHom.comp ((Ideal.Quotient.mk d.reducedIdeal).comp
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R)))))
    let I : Ideal (MvPolynomial (Fin d.m) L) := Ideal.span (Set.range (fun l ↦
      MvPolynomial.C (β (d.a k)) * MvPolynomial.X l -
        ∑ j : d.E k, MvPolynomial.C (β (d.h k l j)) * MvPolynomial.X (j : Fin d.m)))
    ∃ e : (MvPolynomial (Fin d.m) L ⧸ I) ≃ₐ[B]
        B ⊗[R] ULift (d.polynomial ⧸ J),
      ∀ p : MvPolynomial (Fin d.n) R,
        e (Ideal.Quotient.mk I (MvPolynomial.C (β p))) =
          Algebra.TensorProduct.includeRight (R := R) (A := B)
            (ULift.up (Ideal.Quotient.mk J (d.includeX p))) := by
  classical
  intro J L β I
  let Rbar := R ⧸ Ideal.span ({π ^ 2} : Set R)
  let mapB := MvPolynomial.map (σ := Fin d.n) (algebraMap R B)
  let F : Ideal (MvPolynomial (Fin d.n) B) :=
    Ideal.span (Set.range (fun j ↦ mapB (d.f j)))
  let q := MvPolynomial.map (σ := Fin d.m) (Ideal.Quotient.mk F)
  let linear (l : Fin d.m) : MvPolynomial (Fin d.m) (MvPolynomial (Fin d.n) B) :=
    MvPolynomial.C (mapB (d.a k)) * MvPolynomial.X l -
      ∑ j : d.E k, MvPolynomial.C (mapB (d.h k l j)) * MvPolynomial.X (j : Fin d.m)
  let G := Ideal.span (Set.range linear)
  let D := F.map (MvPolynomial.C (σ := Fin d.m)) ⊔ G
  have hred : (algebraMap Rbar B).comp (Ideal.Quotient.mk
      (Ideal.span ({π ^ 2} : Set R))) = algebraMap R B := by
    exact (IsScalarTower.algebraMap_eq R Rbar B).symm
  have hmapred (p : MvPolynomial (Fin d.n) R) :
      MvPolynomial.map (algebraMap Rbar B) (d.reduced p) = mapB p := by
    calc
      _ = MvPolynomial.map ((algebraMap Rbar B).comp
          (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R)))) p :=
        MvPolynomial.map_map _ _ _
      _ = mapB p := congrArg (fun f : R →+* B ↦ MvPolynomial.map f p) hred
  have hF : d.reducedIdeal.map (MvPolynomial.map (algebraMap Rbar B)) = F := by
    simp only [reducedIdeal, Ideal.map_span, ← Set.range_comp,
      Function.comp_def]
    exact congrArg Ideal.span (congrArg Set.range (funext (fun j ↦ hmapred (d.f j))))
  -- Select the equivalences directly to avoid existential elimination over the large goal.
  let c₀ := (baseChangeQuotient Rbar B (Fin d.n) d.reducedIdeal).choose
  have hc₀ := (baseChangeQuotient Rbar B (Fin d.n) d.reducedIdeal).choose_spec
  let c : L ≃ₐ[B] (MvPolynomial (Fin d.n) B ⧸ F) :=
    c₀.trans (Ideal.quotientEquivAlgOfEq B hF)
  have hc (p : MvPolynomial (Fin d.n) R) : c (β p) = Ideal.Quotient.mk F (mapB p) := by
    change Ideal.quotientEquivAlgOfEq B hF
      (c₀ (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk d.reducedIdeal
        (d.reduced p)))) = _
    rw [hc₀, Ideal.quotientEquivAlgOfEq_mk]
    rw [hmapred]
  let cp := MvPolynomial.mapAlgEquiv (Fin d.m) c
  have hI : G.map q = I.map cp.toRingHom := by
    simp only [G, I, Ideal.map_span, ← Set.range_comp]
    congr 1
    funext l
    simp [Function.comp_def, linear, q, cp, MvPolynomial.mapAlgEquiv_apply, hc]
  let ec := Ideal.quotientEquivAlg I (G.map q) cp hI
  let ei := (iteratedQuotient B (MvPolynomial (Fin d.n) B) (Fin d.m) F G).choose
  have hei := (iteratedQuotient B (MvPolynomial (Fin d.n) B) (Fin d.m) F G).choose_spec
  let u := (MvPolynomial.renameEquiv B (Equiv.sumComm (Fin d.n) (Fin d.m))).trans
    (MvPolynomial.sumAlgEquiv B (Fin d.m) (Fin d.n))
  let mapQ := MvPolynomial.map (σ := Fin d.n ⊕ Fin d.m) (algebraMap R B)
  let H := J.map mapQ
  have huX (p : MvPolynomial (Fin d.n) R) :
      u (mapQ (d.includeX p)) = MvPolynomial.C (mapB p) := by
    have heq : u.toRingHom.comp (mapQ.comp d.includeX.toRingHom) =
        MvPolynomial.C.comp mapB := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [u, mapQ, includeX, mapB]
      · intro i
        simp [u, mapQ, includeX, mapB]
    exact DFunLike.congr_fun heq p
  have huZ (l : Fin d.m) : u (mapQ (MvPolynomial.X (.inr l))) =
      MvPolynomial.X l := by simp [u, mapQ]
  have huC : u (mapQ (MvPolynomial.C π)) = 0 := by simp [u, mapQ, hπ]
  have huJ : D = H.map u.toRingHom := by
    have heq : (fun i : Fin d.m ⊕ Fin d.m ↦ u (mapQ
        (match i with
        | .inl j => d.equation (.inl j)
        | .inr l => d.equation (.inr (k, l))))) =
        Sum.elim (fun j ↦ MvPolynomial.C (mapB (d.f j))) linear := by
      funext i
      cases i with
      | inl j => simp only [equation, map_sub, map_mul, huX, huC, huZ,
          zero_mul, sub_zero, Sum.elim_inl]
      | inr l =>
        simp only [equation, map_sub, map_mul, map_sum, huX, huC, huZ,
          zero_mul, sub_zero, Sum.elim_inr, linear]
        congr 1
        exact (Finset.sum_coe_sort (d.E k) _).symm
    dsimp only [H]
    rw [Ideal.map_map]
    change D = (Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))).map (u.toRingHom.comp mapQ)
    rw [Ideal.map_span, ← Set.range_comp]
    change D = Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦ u (mapQ
      (match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))))
    rw [heq, Set.Sum.elim_range, Ideal.span_union]
    simp only [D, F, G, Ideal.map_span, ← Set.range_comp, Function.comp_def]
  let eu := Ideal.quotientEquivAlg H D u huJ
  let et₀ := (baseChangeQuotient R B (Fin d.n ⊕ Fin d.m) J).choose
  have het₀ := (baseChangeQuotient R B (Fin d.n ⊕ Fin d.m) J).choose_spec
  let euLift : B ⊗[R] (d.polynomial ⧸ J) ≃ₐ[B]
      B ⊗[R] ULift (d.polynomial ⧸ J) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (ULift.algEquiv (R := R)).symm
  let e := ((ec.trans ei).trans eu.symm).trans (et₀.symm.trans euLift)
  change ∃ e' : (MvPolynomial (Fin d.m) L ⧸ I) ≃ₐ[B]
      B ⊗[R] ULift (d.polynomial ⧸ J),
    ∀ p, e' (Ideal.Quotient.mk I (MvPolynomial.C (β p))) =
      Algebra.TensorProduct.includeRight (ULift.up (Ideal.Quotient.mk J (d.includeX p)))
  refine ⟨e, ?_⟩
  intro p
  have hec : ec (Ideal.Quotient.mk I (MvPolynomial.C (β p))) =
      Ideal.Quotient.mk (G.map q) (q (MvPolynomial.C (mapB p))) := by
    change Ideal.quotientEquivAlg I (G.map q) cp hI
      (Ideal.Quotient.mk I (MvPolynomial.C (β p))) = _
    rw [Ideal.quotientEquivAlg_mk]
    simp [cp, MvPolynomial.mapAlgEquiv_apply, q, hc]
  have heu : eu.symm (Ideal.Quotient.mk D (MvPolynomial.C (mapB p))) =
      Ideal.Quotient.mk H (mapQ (d.includeX p)) := by
    apply eu.injective
    rw [eu.apply_symm_apply]
    change _ = Ideal.quotientEquivAlg H D u huJ
      (Ideal.Quotient.mk H (mapQ (d.includeX p)))
    rw [Ideal.quotientEquivAlg_mk, huX]
  have het : et₀.symm (Ideal.Quotient.mk H (mapQ (d.includeX p))) =
      Algebra.TensorProduct.includeRight (Ideal.Quotient.mk J (d.includeX p)) := by
    apply et₀.injective
    rw [et₀.apply_symm_apply, het₀]
  dsimp only [e, AlgEquiv.trans_apply]
  rw [hec, hei, heu, het]
  simp [euLift, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.includeRight_apply]
  rfl

end Algebra.PopescuLiftPresentation
