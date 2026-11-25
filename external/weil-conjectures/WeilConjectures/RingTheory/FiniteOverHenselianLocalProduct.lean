/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.FiniteLocalHenselian
import WeilConjectures.RingTheory.EtaleRetractionFiniteProductLocal
import WeilConjectures.RingTheory.HenselianEtaleRetraction

/-!
# Finite algebras over henselian local rings

Source: Stacks Project, Algebra, Lemma 10.153.4, Tag 04GH, parts (1) and (2)
(blueprint: lem-weil-pbc-finite-over-henselian-local-product).
-/

@[expose] public section

universe u v

namespace HenselianLocalRing

set_option linter.style.haveILetI false in
/-- A module-finite algebra over a henselian local ring is a finite product of henselian
local algebras, with local structure maps and finite residue-field extensions.
Source: Stacks Project, Algebra, Lemma 10.153.4 (Tag 04GH), parts (1) and (2)
(blueprint: lem-weil-pbc-finite-over-henselian-local-product).

Proof:
1. The henselian étale retraction property (lem-weil-pbc-henselian-etale-retraction) and
   lem-weil-pbc-etale-retraction-finite-product-local decompose B into finitely many local
   factors. Each factor is finite over R because its projection is surjective.
2. By lem-weil-pbc-finite-algebra-local-radical, each factor's maximal ideal pulls back to
   the maximal ideal of R, so the structure map is local. Reducing finite module generators
   modulo the factor's maximal ideal gives generators over the residue field of R. This
   gives a finite field extension in the sense of def-pc-field-extension.
3. Any finite algebra C over a factor is finite over R, hence is again a product of local
   rings by the same two lemmas from Step 1. Each local component is finite over the factor,
   so lem-weil-pbc-finite-algebra-local-radical shows its structure map is local. Its quotient
   by the factor's maximal ideal is local too. Thus idempotents of this quotient product
   are precisely componentwise zero-one vectors, which lift uniquely to the same vectors
   in C. This is the henselian criterion of def-weil-pbc-henselian-terminology.
4. Combine these properties with the product isomorphism. For the zero algebra use r = 0;
   the product over Fin 0 is the zero ring and there are no factor conditions to check. -/
theorem finite_over_henselian_exists_algEquiv_pi
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    [HenselianLocalRing R] [Algebra R B] [Module.Finite R B] :
    ∃ (r : ℕ) (A : Fin r → Type v) (rings : ∀ i, CommRing (A i)),
      letI := rings
      ∃ (algebras : ∀ i, Algebra R (A i)),
        letI := algebras
        ∃ (henselian : ∀ i, HenselianLocalRing (A i)),
          letI := henselian
          ∃ (localMaps : ∀ i, IsLocalHom (algebraMap R (A i))),
            letI := localMaps
            Nonempty (B ≃ₐ[R] (∀ i, A i)) ∧
              (∀ i, Module.Finite R (A i)) ∧
              (∀ i, Module.Finite (IsLocalRing.ResidueField R)
                (IsLocalRing.ResidueField (A i))) := by
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
    haveI := hEt
    let T := ULift.{v} R
    let E : T ≃ₐ[R] R := ULift.algEquiv
    letI : SMul R T := (inferInstance : Algebra R T).toSMul
    letI : HenselianLocalRing T := HenselianLocalRing.of_ringEquiv E.symm.toRingEquiv
    letI : Algebra T S := ((algebraMap R S).comp E.toRingHom).toAlgebra
    letI : SMul T S := (inferInstance : Algebra T S).toSMul
    haveI : IsLocalHom E.toRingHom := IsLocalHom.of_surjective _ E.surjective
    haveI : IsLocalHom E.symm.toRingHom := IsLocalHom.of_surjective _ E.symm.surjective
    haveI : IsScalarTower R T S :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := T) (A := S) fun _ ↦ rfl
    haveI : Algebra.Etale R T := Algebra.Etale.of_equiv E.symm
    haveI : Algebra.Etale T S := Algebra.Etale.of_restrictScalars R T S
    have hpT : p.comap (algebraMap T S) = IsLocalRing.maximalIdeal T := by
      change (p.comap (algebraMap R S)).comap E.toRingHom = _
      rw [hp, IsLocalRing.maximalIdeal_comap]
    haveI : AlgebraicGeometry.Etale
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
  obtain ⟨r, A, rings, algebras, locals, ⟨e⟩⟩ :=
    finite_algebra_is_product_local_rings hR (B := B)
  letI := rings
  letI := algebras
  letI := locals
  haveI : Module.Finite R (∀ i, A i) := Module.Finite.equiv e.toLinearEquiv
  have hFinite (i : Fin r) : Module.Finite R (A i) := Module.Finite.of_pi A i
  have henselian (i : Fin r) : HenselianLocalRing (A i) := by
    haveI := hFinite i
    exact finite_local_henselian R (A i)
  have localMaps (i : Fin r) : IsLocalHom (algebraMap R (A i)) := by
    haveI := hFinite i
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R (A i))).out 5 1).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal (A i)))
  letI := henselian
  letI := localMaps
  refine ⟨r, A, rings, algebras, henselian, localMaps, ⟨e⟩, hFinite, ?_⟩
  intro i
  haveI := hFinite i
  infer_instance

end HenselianLocalRing
