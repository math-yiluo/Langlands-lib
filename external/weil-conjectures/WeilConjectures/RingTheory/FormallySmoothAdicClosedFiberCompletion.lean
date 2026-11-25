/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import WeilConjectures.RingTheory.FormallySmoothAdicRingEquiv

/-! # The formally smooth closed fibre after completion

Source: Stacks Project, Tag 07NQ, opening completion reduction; Tags 07ED and 0325.
(blueprint: lem-weil-pbc-fs-closed-fibre-completion-transfer)
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom

private theorem formallySmoothAdic_of_algEquiv
    {R : Type u} {S T : Type v} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) (n : Ideal S)
    (h : Algebra.FormallySmoothAdic R S n) :
    Algebra.FormallySmoothAdic R T (n.map e.toRingHom) := by
  intro D _ _ J hJ g hg
  obtain ⟨k, hk, hgk⟩ := hg
  obtain ⟨l, hl⟩ := h J hJ (g.comp e.toAlgHom) ⟨k, hk, fun x hx ↦ by
    apply hgk
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem e.toRingHom hx⟩
  refine ⟨l.comp e.symm.toAlgHom, ?_⟩
  ext x
  have he := AlgHom.congr_fun hl (e.symm x)
  simpa using he

/-- Formal smoothness of the closed fibre passes to a map of maximal-ideal completions
commuting with the canonical maps. No flatness of the original map is needed here.
Source: Stacks Project, Tag 07NQ, opening reduction, and Tags 07ED and 0325.
(blueprint: lem-weil-pbc-fs-closed-fibre-completion-transfer)

Proof: Write mA and mB for the maximal ideals, C = B/mA B, and n = mB C.
Locality gives mA B contained in mB, so C is a nonzero Noetherian local ring and
n is its maximal ideal. Completion of the quotient map B -> C identifies
Bhat/(mA B)Bhat with the n-adic completion Chat (Tag 0325). The maximal ideal
of Ahat is mA Ahat; commuting with canonical maps shows its image in Bhat is
(mA B)Bhat. Thus the closed fibre of the completed map is Chat. The residue
field isomorphism A/mA -> Ahat/mAhat identifies its scalar structure with the
original one: both send the class of a to the class of f(a) in Chat. Formal
smoothness of C over A/mA passes to Chat by Tag 07ED. Its ideal of definition
is n Chat, which is the image of the maximal ideal of Bhat under the displayed
quotient isomorphism. Transport a lifting problem through the two ring
isomorphisms, apply formal smoothness of Chat, then transport the lift back.
The maps, ideal powers, square-zero condition, and reduction identity are all
preserved by these isomorphisms. This gives exactly the stated lifting property.
When A is a field the base completion is A itself. When mA B is zero the
quotient-completion identification is the identity, so these edge cases require
no additional hypotheses. -/
theorem formallySmoothAdic_closedFiber_completion
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (ψ : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    [IsLocalHom ψ]
    (hcomm : ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp f) :
    letI : Algebra A B := f.toAlgebra
    let I : Ideal B := Ideal.map f (maximalIdeal A)
    letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal A ≤ I.comap (algebraMap A B))
    Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)) →
      let Ahat := AdicCompletion (maximalIdeal A) A
      let Bhat := AdicCompletion (maximalIdeal B) B
      letI : Algebra Ahat Bhat := ψ.toAlgebra
      let Ihat : Ideal Bhat := Ideal.map ψ (maximalIdeal Ahat)
      letI : Algebra (Ahat ⧸ maximalIdeal Ahat) (Bhat ⧸ Ihat) :=
        Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
          maximalIdeal Ahat ≤ Ihat.comap (algebraMap Ahat Bhat))
      Algebra.FormallySmoothAdic (Ahat ⧸ maximalIdeal Ahat) (Bhat ⧸ Ihat)
        (Ideal.map (Ideal.Quotient.mk Ihat) (maximalIdeal Bhat)) := by
  dsimp only
  let : Algebra A B := f.toAlgebra
  let I : Ideal B := (maximalIdeal A).map f
  let : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
      maximalIdeal A ≤ I.comap (algebraMap A B))
  intro hfibre
  let C := B ⧸ I
  have : IsNoetherianRing C := isNoetherianRing_of_surjective B C
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let n : Ideal C := (maximalIdeal B).map (Ideal.Quotient.mk I)
  let Chat := AdicCompletion n C
  let Ahat := AdicCompletion (maximalIdeal A) A
  let Bhat := AdicCompletion (maximalIdeal B) B
  let cA : A →+* Ahat := algebraMap A Ahat
  let cB : B →+* Bhat := algebraMap B Bhat
  let cC : C →+* Chat := algebraMap C Chat
  let : Algebra Ahat Bhat := ψ.toAlgebra
  let Ihat : Ideal Bhat := (maximalIdeal Ahat).map ψ
  let : Algebra (Ahat ⧸ maximalIdeal Ahat) (Bhat ⧸ Ihat) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
      maximalIdeal Ahat ≤ Ihat.comap (algebraMap Ahat Bhat))
  have hIhat : Ihat = I.map cB := by
    dsimp [Ihat, I, cB]
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomm, Ideal.map_map]
  have H := AdicCompletion.exists_local_completion_quotient B C
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  dsimp only at H
  rw [Ideal.mk_ker, ← hIhat] at H
  obtain ⟨_, θ, _, hθ, _, _, e, he⟩ := H
  have hcomm' (a : A) : ψ (cA a) = cB (f a) := RingHom.congr_fun hcomm a
  have hec (b : B) : e (Ideal.Quotient.mk Ihat (cB b)) =
      cC (Ideal.Quotient.mk I b) := by
    rw [he]
    exact RingHom.congr_fun hθ b
  let eA : (A ⧸ maximalIdeal A) ≃+* (Ahat ⧸ maximalIdeal Ahat) :=
    RingEquiv.ofBijective (ResidueField.map cA) (AdicCompletion.residueField_map_bijective A)
  have heA (a : A) : eA (Ideal.Quotient.mk (maximalIdeal A) a) =
      Ideal.Quotient.mk (maximalIdeal Ahat) (cA a) := rfl
  have hChat := Algebra.FormallySmoothAdic.adicCompletion
    (A ⧸ maximalIdeal A) C n (IsNoetherian.noetherian n) hfibre
  have hbase := Algebra.FormallySmoothAdic.of_ringEquiv eA.symm
    (n.map cC) hChat
  let : Algebra (Ahat ⧸ maximalIdeal Ahat) Chat :=
    ((algebraMap (A ⧸ maximalIdeal A) Chat).comp eA.symm.toRingHom).toAlgebra
  let eF : (Bhat ⧸ Ihat) ≃ₐ[Ahat ⧸ maximalIdeal Ahat] Chat :=
    { e with
      commutes' := by
        intro r
        obtain ⟨r₀, rfl⟩ := eA.surjective r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r₀
        rw [heA]
        change e (Ideal.Quotient.mk Ihat (ψ (cA a))) =
          algebraMap (A ⧸ maximalIdeal A) Chat
            (eA.symm (Ideal.Quotient.mk (maximalIdeal Ahat) (cA a)))
        rw [← heA, RingEquiv.symm_apply_apply, hcomm', hec]
        rfl }
  let m : Ideal (Bhat ⧸ Ihat) := (maximalIdeal Bhat).map (Ideal.Quotient.mk Ihat)
  have hmaps : m.map eF.toRingHom = n.map cC := by
    have hcompeq : (eF.toRingHom.comp (Ideal.Quotient.mk Ihat)).comp cB =
        cC.comp (Ideal.Quotient.mk I) := by
      exact RingHom.ext hec
    dsimp only [m]
    rw [AdicCompletion.maximalIdeal_eq_map (R := B)]
    change (((maximalIdeal B).map cB).map (Ideal.Quotient.mk Ihat)).map eF.toRingHom =
      ((maximalIdeal B).map (Ideal.Quotient.mk I)).map cC
    simpa only [Ideal.map_map, RingHom.comp_assoc] using
      congrArg (fun h : B →+* Chat ↦ (maximalIdeal B).map h) hcompeq
  have htransport := formallySmoothAdic_of_algEquiv eF.symm (n.map cC) hbase
  rw [← hmaps, Ideal.map_map] at htransport
  have hid : eF.symm.toRingHom.comp eF.toRingHom = RingHom.id _ := by
    ext x
    exact eF.symm_apply_apply x
  rw [hid, Ideal.map_id] at htransport
  exact htransport

end RingHom
