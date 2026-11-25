/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.EtaleRetractionFiniteProductLocal
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# Henselianity of a module-finite local algebra

Source: Stacks Project, Algebra, Tag 04GH (lemma-finite-over-henselian), part (2).
(blueprint: lem-weil-pbc-finite-local-henselian)
-/

@[expose] public section

universe u v

namespace HenselianLocalRing

/-- The componentwise lifting argument of Stacks Tags 04GG (10) and 04GH (2).
The finite-product ideal order isomorphism makes the coordinate quotient maps jointly
injective. Their targets are nonzero local rings, so idempotents are zero-one vectors;
the identical vectors lift uniquely. The argument also covers the empty product. -/
private theorem product_idempotent_lifting
    {ι : Type*} [Finite ι] (D : ι → Type*) [∀ i, CommRing (D i)]
    [∀ i, IsLocalRing (D i)] (K : Ideal (∀ i, D i))
    (hK : ∀ i, K.map (Pi.evalRingHom D i) ≤ IsLocalRing.maximalIdeal (D i))
    (e₀ : (∀ i, D i) ⧸ K) (he₀ : IsIdempotentElem e₀) :
    ∃! e : ∀ i, D i, IsIdempotentElem e ∧ Ideal.Quotient.mk K e = e₀ := by
  classical
  let J : ∀ i, Ideal (D i) := fun i ↦ K.map (Pi.evalRingHom D i)
  have hn (i : ι) : J i ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (D i)).ne_top (hK i)
  have (i : ι) : Nontrivial (D i ⧸ J i) := Ideal.Quotient.nontrivial_iff.mpr (hn i)
  have (i : ι) : IsLocalRing (D i ⧸ J i) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (J i)) Ideal.Quotient.mk_surjective
  let q (i : ι) : (∀ i, D i) ⧸ K →+* D i ⧸ J i :=
    Ideal.Quotient.lift K ((Ideal.Quotient.mk (J i)).comp (Pi.evalRingHom D i))
      (by
        intro b hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hb))
  have hq (i : ι) : q i e₀ = 0 ∨ q i e₀ = 1 :=
    (he₀.map (q i)).eq_zero_or_one_of_isLocalRing
  let e : ∀ i, D i := fun i ↦ if q i e₀ = 0 then 0 else 1
  have he : IsIdempotentElem e := by
    funext i
    dsimp [e]
    split <;> simp
  have heq (i : ι) : Ideal.Quotient.mk (J i) (e i) = q i e₀ := by
    rcases hq i with hi | hi
    · simp [e, hi]
    · simp [e, hi]
  have hpi : Ideal.pi J = K := (Ideal.piOrderIso.symm_apply_apply K)
  have hinj : Function.Injective (RingHom.pi q) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    rw [← hpi]
    intro i
    exact Ideal.Quotient.eq.mp (congrFun hab i)
  have hequot : Ideal.Quotient.mk K e = e₀ := by
    apply hinj
    exact funext heq
  refine ⟨e, ⟨he, hequot⟩, ?_⟩
  intro f hf
  funext i
  have hfi : IsIdempotentElem (f i) := congrFun hf.1.eq i
  have hqi : Ideal.Quotient.mk (J i) (f i) =
      Ideal.Quotient.mk (J i) (e i) := by
    have h := congrArg (q i) (hf.2.trans hequot.symm)
    exact h
  rcases hfi.eq_zero_or_one_of_isLocalRing with hi | hi <;>
    rcases (show IsIdempotentElem (e i) from congrFun he.eq i).eq_zero_or_one_of_isLocalRing
      with hj | hj
  · exact hi.trans hj.symm
  · exfalso
    simp [hi, hj] at hqi
  · exfalso
    simp [hi, hj] at hqi
  · exact hi.trans hj.symm

/-- Combine the existing étale retraction and finite-product theorems, as in Stacks
Tag 04GG (1) => (8) => (10). Lift the base to the neighborhood's universe, transport the
residue-field map along the lift, and descend the resulting retraction. The universe
adapter follows the proved assembly in `FiniteOverHenselianLocalProduct`; importing that
module here would be circular, so only its retraction adapter is reproduced. -/
private theorem finite_product_local
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {B : Type v} [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (n : ℕ) (D : Fin n → Type v)
      (comm : ∀ i, CommRing (D i)) (alg : ∀ i, Algebra R (D i))
      (loc : ∀ i, IsLocalRing (D i)),
      letI := comm
      letI := alg
      letI := loc
      Nonempty (B ≃ₐ[R] ∀ i, D i) := by
  classical
  have hR :
    ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] (hEt : Algebra.Etale R S),
    ∀ (p : Ideal S) [p.IsPrime],
    ∀ (hp : p.comap (algebraMap R S) = IsLocalRing.maximalIdeal R),
    Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
        (Algebra.ofId R S) hp.symm) →
    ∃ τ : S →ₐ[R] R, p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom := by
    intro S _ _ hEt p _ hp hres
    have := hEt
    let T := ULift.{v} R
    let E : T ≃ₐ[R] R := ULift.algEquiv
    let : SMul R T := (inferInstance : Algebra R T).toSMul
    let : HenselianLocalRing T := HenselianLocalRing.of_ringEquiv E.symm.toRingEquiv
    let : Algebra T S := ((algebraMap R S).comp E.toRingHom).toAlgebra
    let : SMul T S := (inferInstance : Algebra T S).toSMul
    have : IsLocalHom E.toRingHom := IsLocalHom.of_surjective _ E.surjective
    have : IsLocalHom E.symm.toRingHom := IsLocalHom.of_surjective _ E.symm.surjective
    have : IsScalarTower R T S :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := T) (A := S) fun _ ↦ rfl
    have : Algebra.Etale R T := Algebra.Etale.of_equiv E.symm
    have : Algebra.Etale T S := Algebra.Etale.of_restrictScalars R T S
    have hpT : p.comap (algebraMap T S) = IsLocalRing.maximalIdeal T := by
      change (p.comap (algebraMap R S)).comap E.toRingHom = _
      rw [hp, IsLocalRing.maximalIdeal_comap]
    have : AlgebraicGeometry.Etale
        (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom (algebraMap T S)).op) :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
        (RingHom.etale_algebraMap.mpr inferInstance)
    have hresT : Function.Bijective
        (Ideal.ResidueField.map (IsLocalRing.maximalIdeal T) p (algebraMap T S) hpT.symm) := by
      let g := Ideal.ResidueField.map (IsLocalRing.maximalIdeal T)
        (IsLocalRing.maximalIdeal R) E.toRingHom
        (IsLocalRing.maximalIdeal_comap E.toRingHom).symm
      have hg : Function.Bijective g := by
        let g' := Ideal.ResidueField.map (IsLocalRing.maximalIdeal R)
          (IsLocalRing.maximalIdeal T) E.symm.toRingHom
          (IsLocalRing.maximalIdeal_comap E.symm.toRingHom).symm
        have h₁ : g'.comp g = RingHom.id _ := by
          apply Ideal.ResidueField.ringHom_ext
          ext x
          simp [g, g', Ideal.ResidueField.map_algebraMap]
        have h₂ : g.comp g' = RingHom.id _ := by
          apply Ideal.ResidueField.ringHom_ext
          ext x
          simp [g, g', Ideal.ResidueField.map_algebraMap]
        exact ⟨Function.LeftInverse.injective (congrArg DFunLike.coe h₁ |> congrFun),
          Function.RightInverse.surjective (congrArg DFunLike.coe h₂ |> congrFun)⟩
      have hcomp : Ideal.ResidueField.map (IsLocalRing.maximalIdeal T) p
          (algebraMap T S) hpT.symm =
          (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
            (Algebra.ofId R S) hp.symm).toRingHom.comp g := by
        apply Ideal.ResidueField.ringHom_ext
        ext x
        simp only [g, RingHom.coe_comp, Function.comp_apply,
          Ideal.ResidueField.map_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Ideal.ResidueField.mapₐ_apply, Algebra.toRingHom_ofId]
        change algebraMap S p.ResidueField (algebraMap R S (E x)) = _
        rw [← IsScalarTower.algebraMap_apply R S p.ResidueField]
        rfl
      rw [hcomp]
      exact hres.comp hg
    obtain ⟨τ, hτ, _⟩ :=
      existsUnique_algHom_of_henselianLocalRing_etale (algebraMap T S) p hpT hresT
    let σ : S →ₐ[R] R := E.toAlgHom.comp (τ.restrictScalars R)
    refine ⟨σ, ?_⟩
    rw [← hτ]
    ext x
    change τ x ∈ IsLocalRing.maximalIdeal T ↔ E (τ x) ∈ IsLocalRing.maximalIdeal R
    exact (SetLike.ext_iff.mp (IsLocalRing.maximalIdeal_comap E.toRingHom) (τ x)).symm
  exact finite_algebra_is_product_local_rings hR

/-- A module-finite local algebra over a henselian local ring is henselian.
Source: Stacks Project, Algebra, Tag 04GH (lemma-finite-over-henselian), part (2).
(blueprint: lem-weil-pbc-finite-local-henselian)

Proof: let A be the local algebra and let C be any finite A-algebra. It is finite
as an R-module by transitivity. The henselian etale retraction theorem and the
finite-algebra product-local theorem decompose C as a finite product of local
rings C_j. Transport the A-algebra structure to this product. Each projection is
surjective, so each C_j is finite over A. Its maximal ideal pulls back to the
maximal ideal n of A by integrality. Thus n C_j is contained in its maximal ideal,
and C_j / n C_j is a nonzero local ring. Quotienting the product by n C gives
the product of these quotients. An idempotent in a local ring is zero or one,
since e (1-e) = 0 and one of e and 1-e is a unit. Hence every idempotent of
C / n C is a zero-one vector and lifts to the identical vector in the product C.
The lift is unique, again componentwise. The empty product covers C = 0.
The idempotent-lifting/simple-root equivalence now gives HenselianLocalRing A. -/
theorem finite_local_henselian
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [HenselianLocalRing R] [IsLocalRing A] [Algebra R A] [Module.Finite R A] :
    HenselianLocalRing A := by
  classical
  apply ((HenselianLocalRing.TFAE A).out 2 1).mp
  apply (IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting.{v, u} A).mp
  intro C _ _ _ e₀ he₀
  let : Algebra R C := Algebra.compHom C (algebraMap R A)
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R C := Module.Finite.trans A C
  obtain ⟨n, D, comm, alg, loc, ⟨E⟩⟩ := finite_product_local (R := R) (B := C)
  let := comm
  let := alg
  let := loc
  let K := ((IsLocalRing.maximalIdeal A).map (algebraMap A C)).map E.toRingHom
  have hK : ∀ i, K.map (Pi.evalRingHom D i) ≤ IsLocalRing.maximalIdeal (D i) := by
    intro i
    let φ : C →+* D i := (Pi.evalRingHom D i).comp E.toRingHom
    let : Algebra A (D i) := (φ.comp (algebraMap A C)).toAlgebra
    let φₐ : C →ₐ[A] D i := { φ with commutes' := fun _ ↦ rfl }
    have hφ : Function.Surjective φₐ := (Function.surjective_eval i).comp E.surjective
    have : Module.Finite A (D i) := Module.Finite.of_surjective φₐ.toLinearMap hφ
    have hmax : ((IsLocalRing.maximalIdeal (D i)).comap
        (algebraMap A (D i))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal _
    have hcontract : (IsLocalRing.maximalIdeal (D i)).comap
        (algebraMap A (D i)) = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal hmax
    dsimp [K]
    rw [Ideal.map_map, Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    exact hcontract.ge
  let Q := Ideal.quotientEquiv
    ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) K E.toRingEquiv rfl
  obtain ⟨e, he, huniq⟩ := product_idempotent_lifting D K hK (Q e₀) (he₀.map Q)
  refine ⟨E.symm e, ⟨he.1.map E.symm, ?_⟩, ?_⟩
  · apply Q.injective
    simpa only [Q, Ideal.quotientEquiv_mk, AlgEquiv.coe_toRingEquiv,
      E.apply_symm_apply] using he.2
  · intro f hf
    apply E.injective
    rw [E.apply_symm_apply]
    apply huniq
    refine ⟨hf.1.map E, ?_⟩
    have h := congrArg Q hf.2
    simpa only [Q, Ideal.quotientEquiv_mk, AlgEquiv.coe_toRingEquiv] using h

end HenselianLocalRing
