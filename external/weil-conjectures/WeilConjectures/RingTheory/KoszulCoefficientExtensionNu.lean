/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Determinant

/-! # KoszulCoefficientExtensionNu

Source: Stacks Project, Tag 0BQZ, coefficient formulas in the finite free
Koszul calculation (blueprint: new-lem-sc-koszul-coefficient-extension-nu).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem pairing_conormal_det
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    (b : Module.Basis (Fin r) (A ⧸ I) I.Cotangent)
    (hb : ∀ i, b i = koszulConormalVector A I r f hf (Finsupp.single i 1))
    (w : ⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))
    (v : Fin r → (Fin r →₀ A)) :
    exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
        (exteriorPower.ιMulti (A ⧸ I) r
          (fun i ↦ koszulConormalVector A I r f hf (v i))) =
      exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
        (exteriorPower.ιMulti (A ⧸ I) r b) *
          Ideal.Quotient.mk I (Matrix.of fun i j ↦ v i j).det := by
  classical
  have hb' : ∀ i, I.toCotangent
      ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩ = b i := by
    intro i
    simpa [koszulConormalVector] using (hb i).symm
  let l := exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
  have h := (l.compAlternatingMap (exteriorPower.ιMulti (A ⧸ I) r)).eq_smul_basis_det b
  have hv := DFunLike.congr_fun h (fun i ↦ koszulConormalVector A I r f hf (v i))
  have hm : b.toMatrix (fun i ↦ koszulConormalVector A I r f hf (v i)) =
      (Matrix.of fun i j ↦ Ideal.Quotient.mk I (v i j)).transpose := by
    ext i j
    change b.coord i (koszulConormalVector A I r f hf (v j)) = _
    simp [koszulConormalVector, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
      hb', Module.Basis.coord_apply, Algebra.smul_def, Finsupp.single_apply]
  simp only [smul_apply, LinearMap.compAlternatingMap_apply,
    Module.Basis.det_apply, hm, Matrix.det_transpose, smul_eq_mul] at hv
  have hd := (RingHom.map_det (Ideal.Quotient.mk I) (Matrix.of fun i j ↦ v i j)).symm
  exact hv.trans (congrArg (fun a ↦ l (exteriorPower.ιMulti (A ⧸ I) r b) * a) hd)

/-- The coefficient extension normal determinant map with its evaluation formula.
Source: Stacks Project, Tag 0BQZ, finite free Koszul computation.
(blueprint: new-lem-sc-koszul-coefficient-extension-nu)

Proof: Put B = A/I and C = S/IS. Localization is flat, so Tag 062H gives
Koszul regularity of the image sequence. The conormal-basis theorem (Tag 062I)
gives bases b_i of I/I^2 and c_i of IS/(IS)^2 consisting of the generator classes.
Let b_i^* and c_i^* be their coordinate functionals. Their increasing top wedges
are bases of the normal determinants. Define nu by sending a times the top
wedge of b_i^* to q(a) times the top wedge of c_i^*. This is additive and
A-linear: hq identifies the A-action through B with the A-action through C.
The coordinates of koszulConormalVector(v) in b are the residues of the
coordinates of v, by its linearCombination definition. The coordinates of its
image in c are their q-images by hq. Pairing the top dual wedge with these
vectors is their coordinate determinant (pairingDual_ιMulti_ιMulti). Ring maps
preserve determinants, so multiplication by q(a) gives exactly the displayed
formula for every w and v. For r = 0 use the empty wedge and determinant 1.
If B or C is the zero ring, the same basis-coordinate construction and formulas
still apply, without a nontriviality hypothesis. No data are chosen from a mere
existence statement: the described coordinate maps are explicit once the
conormal bases, fixed by their generator values, are given. -/
theorem exists_koszul_coefficient_extension_nu
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S))
    (q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)))
    (hq : ∀ b : A, q (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) :
  ∃ (ν : koszulNormalDeterminant A I r →ₗ[A]
    (ModuleCat.restrictScalars (algebraMap A S)).obj
      (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
  ∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
    exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r (ν w)
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
        (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
          (algebraMap A S ∘ f) hs
          ((v i).mapRange (algebraMap A S) (map_zero _)))) =
    q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
      (exteriorPower.ιMulti (A ⧸ I) r
        (fun i ↦ koszulConormalVector A I r f hf (v i)))) := by
  classical
  have : Module.Flat A S := IsLocalization.flat S T
  have hregs := RingTheory.Sequence.isKoszulRegular_of_flat A S r f hreg
  obtain ⟨b, hb⟩ := exists_koszul_conormal_basis A I r f hreg hf
  obtain ⟨c, hc⟩ := exists_koszul_conormal_basis S (I.map (algebraMap A S)) r
    (algebraMap A S ∘ f) hregs hs
  let e := exteriorPower.ιMulti (A ⧸ I) r b
  let z := exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r c.coord
  let l : (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent)) →ₗ[A ⧸ I] (A ⧸ I) :=
    (LinearMap.applyₗ e).comp (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r)
  let ν : koszulNormalDeterminant A I r →ₗ[A]
      (ModuleCat.restrictScalars (algebraMap A S)).obj
        (koszulNormalDeterminant S (I.map (algebraMap A S)) r) :=
    { toFun := fun w ↦ q (l w) • z
      map_add' := by
        intro w w'
        simp only [map_add, add_smul]
      map_smul' := by
        intro a w
        change ⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent) at w
        change q (l (Ideal.Quotient.mk I a • w)) • z =
          Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S a) •
            (q (l w) • z)
        rw [map_smul, smul_eq_mul, map_mul, hq, smul_smul] }
  refine ⟨ν, ?_⟩
  intro w v
  have hp : exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r z
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
        (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
          (algebraMap A S ∘ f) hs
          ((v i).mapRange (algebraMap A S) (map_zero _)))) =
      q (Ideal.Quotient.mk I (Matrix.of fun i j ↦ v i j).det) := by
    have hc' : ∀ i, (I.map (algebraMap A S)).toCotangent
        ⟨(algebraMap A S ∘ f) i, hs ▸ Ideal.subset_span (Set.mem_range_self i)⟩ =
        c i := by
      intro i
      simpa [koszulConormalVector] using (hc i).symm
    simp only [z, exteriorPower.pairingDual_ιMulti_ιMulti]
    simp only [koszulConormalVector, Finsupp.linearCombination_apply,
      hc']
    simp only [Finsupp.sum, map_sum, LinearMap.map_smul_of_tower,
      Module.Basis.coord_apply]
    simp only [Finsupp.mapRange_apply, Module.Basis.repr_self, algebraMap_smul]
    simp only [Algebra.smul_def, Finsupp.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    refine Eq.trans ?_ ((congrArg q (RingHom.map_det (Ideal.Quotient.mk I)
      (Matrix.of fun i j ↦ v i j))).trans (RingHom.map_det q _)).symm
    congr 1
    ext i j
    dsimp
    split_ifs with h
    · change 0 = q (Ideal.Quotient.mk I (v i j))
      rw [hq, h, map_zero]
    · change Ideal.Quotient.mk (I.map (algebraMap A S))
          (algebraMap A S (v i j)) = q (Ideal.Quotient.mk I (v i j))
      exact (hq _).symm
  change exteriorPower.pairingDual _ _ r (q (l w) • z) _ = _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hp,
    pairing_conormal_det A I r f hf b hb, map_mul]
  rfl

end ExteriorAlgebra
