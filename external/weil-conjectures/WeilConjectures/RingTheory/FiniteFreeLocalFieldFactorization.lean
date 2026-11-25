/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.MonicSpan
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Finite free local realization of a finite residue-field extension

Source: Stacks Project, Tag 07NE, specialized to a maximal ideal of a local ring.
-/

@[expose] public section

universe u

namespace IsLocalRing

private theorem exists_finite_free_local_monogenic_field_factor
    (A K : Type u) [CommRing A] [IsLocalRing A] [Field K]
    (psi : A →+* K) (hfinite : psi.Finite)
    (hker : RingHom.ker psi = maximalIdeal A) (x : K) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B)
      (phi : B →+* K),
      Module.Free A B ∧ Module.Finite A B ∧ IsLocalHom (algebraMap A B) ∧
        RingHom.ker phi = maximalIdeal B ∧ phi.comp (algebraMap A B) = psi ∧
          ∃ b, phi b = x := by
  classical
  let : Algebra A K := psi.toAlgebra
  have : Module.Finite A K := hfinite
  let q := Polynomial.eval₂RingHom psi x
  have hqcomp : q.comp Polynomial.C = psi := Polynomial.eval₂RingHom_comp_C psi x
  have hcomap : (RingHom.ker q).comap Polynomial.C = maximalIdeal A := by
    rw [RingHom.comap_ker, hqcomp, hker]
  have hne : RingHom.ker q ≠ ((RingHom.ker q).comap Polynomial.C).map Polynomial.C := by
    rw [hcomap]
    intro heq
    obtain ⟨g, hg, hgx⟩ := IsIntegral.of_finite (R := A) x
    have hmem : g ∈ RingHom.ker q := hgx
    rw [heq] at hmem
    have h1 := Ideal.mem_map_C_iff.mp hmem g.natDegree
    rw [hg.coeff_natDegree] at h1
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨f, hf, hspan⟩ := Polynomial.exists_monic_span_sup_map_eq A
    (RingHom.ker q) (by rw [hcomap]; infer_instance) hne
  rw [hcomap] at hspan
  have hfx : f.eval₂ psi x = 0 := by
    change q f = 0
    apply RingHom.mem_ker.mp
    rw [hspan]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f))
  let B := AdjoinRoot f
  let phi : B →+* K := AdjoinRoot.lift psi x hfx
  have hphimk : phi.comp (AdjoinRoot.mk f) = q := by
    apply RingHom.ext
    intro p
    exact AdjoinRoot.lift_mk hfx p
  have hphiker : RingHom.ker phi = (maximalIdeal A).map (algebraMap A B) := by
    apply Ideal.comap_injective_of_surjective (AdjoinRoot.mk f) AdjoinRoot.mk_surjective
    rw [RingHom.comap_ker, hphimk, hspan]
    have halg : algebraMap A B = (AdjoinRoot.mk f).comp Polynomial.C := rfl
    rw [halg, ← Ideal.map_map, Ideal.comap_map_of_surjective _ AdjoinRoot.mk_surjective]
    rw [AdjoinRoot.mk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hphicomp : phi.comp (algebraMap A B) = psi := AdjoinRoot.lift_comp_of hfx
  have : Module.Free A B := hf.free_adjoinRoot
  have : Module.Finite A B := hf.finite_adjoinRoot
  let : Algebra B K := phi.toAlgebra
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' hphicomp.symm
  have : Module.Finite B K := Module.Finite.of_restrictScalars_finite A B K
  have : (⊥ : Ideal K).IsMaximal := Ideal.bot_isMaximal
  have hmax : (RingHom.ker phi).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) (⊥ : Ideal K)
  have hlocal : IsLocalRing B := IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker phi, hmax, by
      intro n hn
      have : n.IsMaximal := hn
      have hnA : n.comap (algebraMap A B) = maximalIdeal A :=
        eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal n)
      have hle : RingHom.ker phi ≤ n := by
        rw [hphiker, Ideal.map_le_iff_le_comap, hnA]
      exact (hmax.eq_of_le hn.ne_top hle).symm⟩
  have hlocalMap : IsLocalHom (algebraMap A B) :=
    ((local_hom_TFAE (algebraMap A B)).out 5 1).mp
      (eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal B)))
  refine ⟨B, inferInstance, hlocal, inferInstance, phi, inferInstance, inferInstance,
    hlocalMap, eq_maximalIdeal hmax, hphicomp, ?_⟩
  exact ⟨AdjoinRoot.root f, AdjoinRoot.lift_root hfx⟩

/-- A finite field quotient-extension factors through a finite free local algebra.

Source: Stacks Project, Tag 07NE; the locality argument in Tag 0EYB.
(blueprint: lem-sbc-finite-free-local-field-factorization)

Proof: The kernel identifies the image of rho with A/m. Choose a finite set of
A-module generators of K. Induct on finite sets of elements to produce a local
finite free A-algebra mapping to K, with kernel its maximal ideal, whose image
contains that finite set. Start with A and rho. At an adjoining step, write the
preceding map as psi : S → K. K is still a finite S-module by restriction of
scalars, so the new element x is integral over S. The kernel of evaluation
S[T] → K therefore strictly contains m_S[T]: a monic polynomial vanishes at x,
whereas its leading coefficient 1 is not in m_S. Polynomial division over S/m_S
and lifting coefficients supply a monic f with evaluation kernel m_S[T] + (f).
Take B = S[T]/(f). Its power basis gives finite freeness, and evaluation descends
with kernel m_SB. This kernel is maximal because K is integral over B. Every
maximal ideal of B contracts to m_S by integrality, hence contains and equals
m_SB. Thus B is local, and contraction shows S → B is local. Compose the free
bases, finite generating sets, structural maps and evaluation maps along this
finite induction. At the final stage the image contains the chosen A-module
generators, hence all of K; the evaluation map is surjective. No separability or
Noetherianity is required; finitely many polynomial quotients remain in Type u.
This is solely a ring construction, with no scheme or smoothness hypothesis. -/
theorem exists_finite_free_local_field_factorization
    (A K : Type u) [CommRing A] [IsLocalRing A] [Field K]
    (rho : A →+* K) (hfinite : rho.Finite)
    (hker : RingHom.ker rho = maximalIdeal A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B),
      Module.Free A B ∧ Module.Finite A B ∧ IsLocalHom (algebraMap A B) ∧
        ∃ beta : B →+* K, Function.Surjective beta ∧
          beta.comp (algebraMap A B) = rho := by
  classical
  let : Algebra A K := rho.toAlgebra
  have : Module.Finite A K := hfinite
  have hstage : ∀ s : Finset K,
      ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B)
        (beta : B →+* K),
        Module.Free A B ∧ Module.Finite A B ∧ IsLocalHom (algebraMap A B) ∧
          RingHom.ker beta = maximalIdeal B ∧ beta.comp (algebraMap A B) = rho ∧
            ∀ x ∈ s, ∃ b, beta b = x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨A, inferInstance, inferInstance, inferInstance, rho, inferInstance,
          inferInstance, ?_, hker, ?_, ?_⟩
        · infer_instance
        · rfl
        · simp
    | @insert x s hx ih =>
        obtain ⟨B, hB, hlocal, hAlg, beta, hfree, hfin, hmap, hkerB, hcomp, hs⟩ := ih
        let := hB
        let := hlocal
        let := hAlg
        let := hfree
        let := hfin
        let := hmap
        let : Algebra B K := beta.toAlgebra
        have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' hcomp.symm
        have : Module.Finite B K := Module.Finite.of_restrictScalars_finite A B K
        obtain ⟨C, hC, hlocalC, hAlgC, phi, hfreeC, hfinC, hmapC,
          hkerC, hcompC, c, hc⟩ :=
          exists_finite_free_local_monogenic_field_factor B K beta
            (RingHom.finite_algebraMap.mpr inferInstance) hkerB x
        let := hC
        let := hlocalC
        let := hAlgC
        let := hfreeC
        let := hfinC
        let := hmapC
        let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
        have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
        have : Module.Free A C := Module.Free.trans (R := A) (S := B)
        have : Module.Finite A C := Module.Finite.trans B C
        refine ⟨C, inferInstance, inferInstance, inferInstance, phi, inferInstance,
          inferInstance, ?_, hkerC, ?_, ?_⟩
        · change IsLocalHom ((algebraMap B C).comp (algebraMap A B))
          infer_instance
        · change phi.comp ((algebraMap B C).comp (algebraMap A B)) = rho
          rw [← RingHom.comp_assoc, hcompC, hcomp]
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact ⟨c, hc⟩
          · obtain ⟨b, hb⟩ := hs z hz
            exact ⟨algebraMap B C b, (DFunLike.congr_fun hcompC b).trans hb⟩
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := A) (M := K))
  obtain ⟨B, hB, hlocal, hAlg, beta, hfree, hfin, hmap, _, hcomp, hcontains⟩ := hstage s
  let := hB
  let := hlocal
  let := hAlg
  let b : B →ₐ[A] K := { beta with commutes' := fun a ↦ DFunLike.congr_fun hcomp a }
  have hrange : Submodule.span A (s : Set K) ≤ LinearMap.range b.toLinearMap :=
    Submodule.span_le.mpr (fun x hx ↦ hcontains x hx)
  rw [hs] at hrange
  have hsurj : Function.Surjective beta :=
    LinearMap.range_eq_top.mp (top_le_iff.mp hrange)
  exact ⟨B, hB, hlocal, hAlg, hfree, hfin, hmap, beta, hsurj, hcomp⟩

end IsLocalRing
