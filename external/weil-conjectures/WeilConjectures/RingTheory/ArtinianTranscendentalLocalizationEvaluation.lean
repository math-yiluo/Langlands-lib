/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.FlatAndFlatOfFlatFibreNoetherian
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# A component of the transcendental polynomial localization argument

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI.
-/

@[expose] public section
set_option autoImplicit false
universe u v z
namespace Algebra

/-- The flat local evaluation map from the transcendental polynomial localization.
Source: Stacks Project, Smoothing Ring Maps, Tag 07FI, lines 2642--2675.
(blueprint: lem-weil-pbc-artinian-transcendental-localization-core-evaluation)
Proof: Every polynomial outside P evaluates outside m_S, hence to a unit.
The localization universal property constructs g_0 : D[t]_P -> S. Its
contraction of m_S is the maximal ideal of D[t]_P, so g_0 is local.
The universal property gives the factorization over D, and t/1 maps to x.
As in the structural argument, transcendence identifies P with m_D[t];
thus the closed fibre of D -> D[t]_P is F(t), where F = D/m_D.
Apply the Noetherian fibre flatness criterion to D -> D[t]_P -> S with
module M = S, finite over itself: M is flat over D by hflat and its
closed fibre is flat over the field F(t). Hence g_0 is flat. Compose
with the canonical ULift down ring equivalence to obtain g'. This retains
locality, flatness, the factorization and the image of t/1. For D a field
this is precisely extension of evaluation from D[t] to its fraction field. -/
theorem localization_transcendental_evaluation
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    ∃ g' : T →+* S, IsLocalHom g' ∧ g'.Flat ∧
      g'.comp (algebraMap D T) = algebraMap D S ∧ x ∈ Set.range g' := by
  classical
  let θ := Polynomial.eval₂RingHom (algebraMap D S) x
  let P : Ideal (Polynomial D) := (IsLocalRing.maximalIdeal S).comap θ
  let T₀ := Localization.AtPrime P
  have hunits : ∀ y : P.primeCompl, IsUnit (θ y) := fun y ↦
    IsLocalRing.notMem_maximalIdeal.mp y.property
  let g₀ : T₀ →+* S := IsLocalization.lift hunits
  have hg₀ (p : Polynomial D) : g₀ (algebraMap (Polynomial D) T₀ p) = θ p :=
    IsLocalization.lift_eq hunits p
  have hlocal : IsLocalHom g₀ := by
    constructor
    intro a ha
    obtain ⟨p, q, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl a
    apply (IsLocalization.AtPrime.isUnit_mk'_iff T₀ P p q).mpr
    change θ p ∉ IsLocalRing.maximalIdeal S
    apply IsLocalRing.notMem_maximalIdeal.mpr
    have heq : θ p = θ q * g₀ (IsLocalization.mk' T₀ p q) :=
      (IsLocalization.lift_mk'_spec hunits p _ q).mp rfl
    rw [heq]
    exact (hunits q).mul ha
  have hfac : g₀.comp (algebraMap D T₀) = algebraMap D S := by
    ext d
    change g₀ (algebraMap (Polynomial D) T₀ (Polynomial.C d)) = _
    rw [hg₀]
    exact Polynomial.eval₂_C _ _
  have hP : P = (IsLocalRing.maximalIdeal D).map Polynomial.C := by
    have hres (p : Polynomial D) :
        Polynomial.aeval (IsLocalRing.residue S x) (p.map (IsLocalRing.residue D)) =
          IsLocalRing.residue S (θ p) := by
      change Polynomial.eval₂ _ _ _ =
        IsLocalRing.residue S (Polynomial.eval₂ (algebraMap D S) x p)
      rw [Polynomial.eval₂_map, Polynomial.hom_eval₂]
      rfl
    ext p
    rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
    constructor
    · intro hp
      have hzero : p.map (IsLocalRing.residue D) = 0 :=
        transcendental_iff.mp hx _ (by rw [hres, IsLocalRing.residue_eq_zero_iff]; exact hp)
      intro n
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      simpa using congrArg (fun q : Polynomial (IsLocalRing.ResidueField D) ↦ q.coeff n) hzero
    · intro hp
      have hzero : p.map (IsLocalRing.residue D) = 0 := by
        ext n
        simpa using (IsLocalRing.residue_eq_zero_iff _).mpr (hp n)
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [← hres, hzero, map_zero]
  have hflat₀ : g₀.Flat := by
    let : Algebra T₀ S := g₀.toAlgebra
    have : IsScalarTower D T₀ S := IsScalarTower.of_algebraMap_eq' hfac.symm
    have : IsLocalHom (algebraMap T₀ S) := hlocal
    have : IsLocalHom (algebraMap D T₀) := by
      have : IsLocalHom (g₀.comp (algebraMap D T₀)) := by
        rw [hfac]
        infer_instance
      exact isLocalHom_of_comp (algebraMap D T₀) g₀
    have : Module.Flat D S := RingHom.flat_algebraMap_iff.mp hflat
    have hm : (IsLocalRing.maximalIdeal D).map (algebraMap D T₀) =
        IsLocalRing.maximalIdeal T₀ := by
      calc
        _ = ((IsLocalRing.maximalIdeal D).map Polynomial.C).map
            (algebraMap (Polynomial D) T₀) := by rw [Ideal.map_map]; rfl
        _ = P.map (algebraMap (Polynomial D) T₀) :=
          congrArg (Ideal.map (algebraMap (Polynomial D) T₀)) hP.symm
        _ = _ := Localization.AtPrime.map_eq_maximalIdeal
    have : ((IsLocalRing.maximalIdeal D).map (algebraMap D T₀)).IsMaximal := by
      rw [hm]
      infer_instance
    let := Ideal.Quotient.field ((IsLocalRing.maximalIdeal D).map (algebraMap D T₀))
    have hfibre : Module.Flat
        (T₀ ⧸ (IsLocalRing.maximalIdeal D).map (algebraMap D T₀))
        (_root_.TensorProduct T₀
          (T₀ ⧸ (IsLocalRing.maximalIdeal D).map (algebraMap D T₀)) S) := by
      have := Module.Free.of_divisionRing
        (T₀ ⧸ (IsLocalRing.maximalIdeal D).map (algebraMap D T₀))
        (_root_.TensorProduct T₀
          (T₀ ⧸ (IsLocalRing.maximalIdeal D).map (algebraMap D T₀)) S)
      exact Module.Flat.of_free
    have hf := (Module.flat_and_flat_of_flat_fibre_noetherian D T₀ S S hfibre).2
    exact RingHom.flat_algebraMap_iff.mpr hf
  let e : ULift.{max u v z} T₀ ≃+* T₀ := ULift.ringEquiv
  refine ⟨g₀.comp e.toRingHom, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun a ha ↦ e.symm.toRingHom.isUnit_map (hlocal.map_nonunit _ ha)⟩
  · exact (RingHom.Flat.of_bijective e.bijective).comp hflat₀
  · ext d
    exact DFunLike.congr_fun hfac d
  · refine ⟨ULift.up (algebraMap (Polynomial D) T₀ Polynomial.X), ?_⟩
    change g₀ (algebraMap (Polynomial D) T₀ Polynomial.X) = x
    rw [hg₀]
    exact Polynomial.eval₂_X _ _


end Algebra
