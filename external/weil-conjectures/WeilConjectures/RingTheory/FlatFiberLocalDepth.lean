/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.FlatLocalDepthFormula

/-!
# Depth formula at a prime of a fibre ring

Source: Stacks Project, Algebra, Tags 0339, 0337, 00ON and Remark 0H9M.
(blueprint: lem-weil-pbc-flat-fiber-local-depth).
-/

@[expose] public section

universe u v

namespace RingHom

private theorem maximal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (IsLocalRing.maximalIdeal A).map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top

private theorem depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  simp only [IsLocalRing.depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A = IsLocalRing.depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)


/-- Depth splits into a base term and a fibre term for a flat map.
Source: Stacks Project, Algebra, proof of Tag 0339, Tag 0337 and Remark 0H9M.
(blueprint: lem-weil-pbc-flat-fiber-local-depth).

Proof: Localize the flat map at p and q = Q.comap includeRight. This is a flat local
map of Noetherian local rings. Its closed fibre is S_q / p S_q: the image of
the maximal ideal of R_p equals the image of p, since denominators outside p
are units. Apply the flat local depth formula (Tag 0337). The fibre local-ring
isomorphism of Remark 0H9M identifies this quotient with (p.Fiber S)_Q.
A ring isomorphism carries maximal ideals and regular sequences bijectively,
preserves their lengths, and therefore preserves the supremum defining depth.
Substitution in the depth formula gives the assertion. -/
theorem depth_eq_add_of_flat_fiber {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] (hflat : (algebraMap R S).Flat)
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    IsLocalRing.depth (R := Localization.AtPrime
        (Q.comap Algebra.TensorProduct.includeRight.toRingHom))
      (Localization.AtPrime (Q.comap Algebra.TensorProduct.includeRight.toRingHom)) =
    IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) +
      IsLocalRing.depth (R := Localization.AtPrime Q) (Localization.AtPrime Q) := by
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let q : Ideal S := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  have : q.LiesOver p := Ideal.LiesOver.of_eq_comap p
    Algebra.TensorProduct.includeRight rfl
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have hf : (algebraMap Rp Sq).Flat := hflat.localRingHom q p (q.over_def p)
  let I : Ideal Sq := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sq)
  obtain ⟨_, hlocal, _, hd⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (algebraMap Rp Sq) hf
  have : IsLocalRing (Sq ⧸ I) := hlocal
  have hIeq : I = p.map (algebraMap R Sq) := by
    dsimp [I]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq R Rp Sq).symm
  let e := (Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv
  have hquot : (p.map (algebraMap R S)).map (algebraMap S Sq) =
      p.map (algebraMap R Sq) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S Sq]
  let e' : Localization.AtPrime Q ≃+* (Sq ⧸ I) :=
    e.trans ((Ideal.quotientEquivAlgOfEq R hquot).toRingEquiv.trans
      (Ideal.quotientEquivAlgOfEq R hIeq.symm).toRingEquiv)
  exact hd.trans (congrArg (IsLocalRing.depth (R := Rp) Rp + ·)
    (depth_eq_of_ringEquiv e').symm)

end RingHom
