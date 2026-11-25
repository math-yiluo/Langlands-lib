/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# A component of the transcendental polynomial localization argument

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI.
-/

@[expose] public section
set_option autoImplicit false
universe u v z
namespace Algebra

/-- The structural properties of the transcendental polynomial localization.
Source: Stacks Project, Smoothing Ring Maps, Tag 07FI, lines 2642--2675.
(blueprint: lem-weil-pbc-artinian-transcendental-localization-core-structural)
Proof: Write F = D/m_D and K = S/m_S. Reduction of evaluation factors through
F[t] -> K. Transcendence makes this map injective, so its kernel in D[t] is
exactly m_D[t], and therefore P = m_D[t]. Since D is Artinian it is Noetherian
and m_D is nilpotent. Consequently D[t]_P is Noetherian and local, and its
maximal ideal m_D D[t]_P is nilpotent. A Noetherian local ring with nilpotent
maximal ideal is Artinian. The contraction of this maximal ideal to D is m_D,
so D -> D[t]_P is local. The polynomial algebra is smooth and localization
makes its structure map essentially smooth. Transport all properties across
the canonical ULift ring equivalence. The flatness assumption is not needed
for this component. In the field case the localization is F(t), as expected. -/
theorem localization_artinian_transcendental_properties
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    IsLocalRing T ∧ IsArtinianRing T ∧ IsLocalHom (algebraMap D T) ∧
      EssentiallySmooth D T := by
  have _ := hflat
  dsimp
  let P : Ideal (Polynomial D) :=
    (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
  have hP : P = Ideal.map (Polynomial.C : D →+* Polynomial D)
      (IsLocalRing.maximalIdeal D) := by
    ext f
    rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
    have he : Polynomial.aeval (IsLocalRing.residue S x)
        (f.map (IsLocalRing.residue D)) =
        IsLocalRing.residue S (Polynomial.eval₂RingHom (algebraMap D S) x f) := by
      have heq : (Polynomial.aeval (IsLocalRing.residue S x)).toRingHom.comp
          (Polynomial.mapRingHom (IsLocalRing.residue D)) =
          (IsLocalRing.residue S).comp (Polynomial.eval₂RingHom (algebraMap D S) x) := by
        ext a <;> simp [IsLocalRing.ResidueField.algebraMap_residue]
      exact DFunLike.congr_fun heq f
    constructor
    · intro hf
      have hz : f.map (IsLocalRing.residue D) = 0 :=
        (transcendental_iff.mp hx) _ (he.trans ((IsLocalRing.residue_eq_zero_iff _).mpr hf))
      intro n
      have hn := congrArg (fun p => Polynomial.coeff p n) hz
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
        IsLocalRing.residue_eq_zero_iff] using hn
    · intro hf
      have hz : f.map (IsLocalRing.residue D) = 0 := by
        ext n
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
          IsLocalRing.residue_eq_zero_iff] using hf n
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [← he, hz, map_zero]
  let L := Localization.AtPrime P
  have : IsNoetherianRing D := inferInstance
  have : IsNoetherianRing (Polynomial D) := inferInstance
  have : IsArtinianRing L := by
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal L).mpr
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal D).mp
      (inferInstance : IsArtinianRing D)
    refine ⟨n, ?_⟩
    have hm := congrArg (Ideal.map (algebraMap (Polynomial D) L)) hP
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hm, Ideal.map_map,
      ← Ideal.map_pow, hn]
    exact Ideal.map_bot
  have : IsLocalHom (algebraMap D L) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap D L)).out 4 1).mp
    intro d hd
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply D (Polynomial D) L,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (S := L) P]
    change Polynomial.C d ∈ P
    rw [hP, Ideal.mem_map_C_iff]
    intro n
    by_cases hn : n = 0
    · simpa [hn] using hd
    · simp [Polynomial.coeff_C, hn]
  have : IsLocalRing (ULift.{max u v z} L) := ULift.ringEquiv.symm.isLocalRing
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact ULift.ringEquiv.symm.isArtinianRing
  · refine ⟨fun d hd => ?_⟩
    apply isUnit_of_map_unit (algebraMap D L) d
    exact hd.map (ULift.ringEquiv : ULift.{max u v z} L ≃+* L).toRingHom
  · let Q := ULift.{max u v z} (Polynomial D)
    let e : Polynomial D ≃ₐ[D] Q := ULift.algEquiv.symm
    have : Smooth D (Polynomial D) := ⟨inferInstance, inferInstance⟩
    have : Smooth D Q := Smooth.of_equiv e
    let M : Submonoid Q := Submonoid.map e P.primeCompl
    exact ⟨Q, inferInstance, inferInstance, inferInstance, M,
      ⟨(ULift.algEquiv (R := D)).trans
        (IsLocalization.algEquivOfAlgEquiv (M := P.primeCompl) (T := M)
          L (Localization M) e rfl)⟩⟩


end Algebra
