/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Unramified.LocalStructure

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- The finite étale local residue capture data, before deriving Artinianness.
Source: Stacks Project, Smoothing Ring Maps, Tag 07FI, finite étale and henselian
factorization paragraphs.  The omitted Artinian conclusion is derived from finiteness.
(blueprint: lem-weil-pbc-artinian-separable-residue-lift-capture).

Proof: Construct the finite étale lift of the finite separable subextension of the
residue fields, then use henselian factorization and lift the chosen residue element.
This is the construction part of the core theorem; Artinianness of the lifted ring is
separate and follows from its finite module structure over the Artinian base. -/
theorem exists_finiteEtale_artinian_residue_lift_capture
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (b : IsLocalRing.ResidueField S)
    (hb : IsSeparable (IsLocalRing.ResidueField D) b) :
    ∃ (D' : Type (max u v z)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
      IsLocalRing D' ∧
      IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
      Etale D D' ∧ Module.Finite D D' ∧
      g'.comp (algebraMap D D') = algebraMap D S ∧
      ∃ d : D', IsLocalRing.residue S (g' d) = b := by
  classical
  let k := IsLocalRing.ResidueField D
  let K := IsLocalRing.ResidueField S
  -- Lift the separable minimal polynomial, keeping it monic.
  have hint : IsIntegral k b := hb.isIntegral
  obtain ⟨F, hFmap, -, hF⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr
      (Polynomial.map_surjective _ IsLocalRing.residue_surjective (minpoly k b)))
    (minpoly.monic hint)
  change Polynomial.map (algebraMap D k) F = minpoly k b at hFmap
  have hFb : Polynomial.aeval b F = 0 := by
    rw [← Polynomial.aeval_map_algebraMap k, hFmap]
    exact minpoly.aeval k b
  have hF'b : Polynomial.aeval b F.derivative ≠ 0 := by
    rw [← Polynomial.aeval_map_algebraMap k, ← Polynomial.derivative_map, hFmap]
    exact hb.aeval_derivative_ne_zero (minpoly.aeval k b)
  -- Inverting its derivative gives an étale algebra with the desired residue point.
  let P : StandardEtalePair D := ⟨F, hF, F.derivative, ⟨1, 0, 1, by simp⟩⟩
  have hP : P.HasMap b := ⟨hFb, hF'b.isUnit⟩
  let E := ULift.{max v z} P.Ring
  let e : E ≃ₐ[D] P.Ring := ULift.algEquiv
  let : Etale D E := Etale.of_equiv e.symm
  let : Module.Finite D E := Module.Finite.of_quasiFinite
  let : IsArtinianRing E := IsArtinianRing.of_finite D E
  let ψ : E →ₐ[D] K := (P.lift b hP).comp e.toAlgHom
  -- The residue point lifts across the nilpotent maximal ideal of S.
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal S) := by
    rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact IsArtinianRing.isNilpotent_nilradical
  let g : E →ₐ[D] S := FormallySmooth.lift (IsLocalRing.maximalIdeal S) hnil ψ
  have hg (x : E) : IsLocalRing.residue S (g x) = ψ x :=
    FormallySmooth.mk_lift (IsLocalRing.maximalIdeal S) hnil ψ x
  -- Select its local factor; localization of an Artinian ring is surjective.
  let q : Ideal E := RingHom.ker ψ
  let : q.IsPrime := RingHom.ker_isPrime ψ
  let D' := Localization.AtPrime q
  have hsurj : Function.Surjective (algebraMap E D') :=
    IsArtinianRing.localization_surjective q.primeCompl D'
  let : Module.Finite D D' := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom D E D').toLinearMap hsurj
  let : FinitePresentation D D' := FinitePresentation.of_finiteType.mp inferInstance
  let : Etale D D' := ⟨inferInstance, inferInstance⟩
  have hu (x : q.primeCompl) : IsUnit (g x) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [hg]
    exact x.property
  let g' : D' →ₐ[D] S := IsLocalization.liftAlgHom (f := g) hu
  have hg' (x : E) : g' (algebraMap E D' x) = g x := IsLocalization.lift_eq hu x
  have hlocal : IsLocalHom g'.toRingHom := by
    constructor
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    apply (IsLocalization.AtPrime.isUnit_to_map_iff D' q y).mpr
    change ψ y ≠ 0
    rw [← hg, ← hg']
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hx
  let : IsLocalHom g'.toRingHom := hlocal
  have hcomp : g'.toRingHom.comp (algebraMap D D') = algebraMap D S :=
    g'.comp_algebraMap
  have hbase : IsLocalHom (algebraMap D D') := by
    let : IsLocalHom (g'.toRingHom.comp (algebraMap D D')) := by
      rw [hcomp]
      infer_instance
    exact isLocalHom_of_comp (algebraMap D D') g'.toRingHom
  refine ⟨D', inferInstance, inferInstance, g'.toRingHom, inferInstance, hbase,
    hlocal, inferInstance, inferInstance, hcomp, ?_⟩
  refine ⟨algebraMap E D' (e.symm P.X), ?_⟩
  change IsLocalRing.residue S (g' (algebraMap E D' (e.symm P.X))) = b
  rw [hg', hg]
  change P.lift b hP (e (e.symm P.X)) = b
  rw [AlgEquiv.apply_symm_apply]
  exact P.lift_X b hP

end Algebra
