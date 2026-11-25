/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorRestrictionCertificate
public import WeilConjectures.RingTheory.SelfTorConormalComparison
import WeilConjectures.RingTheory.KoszulRestrictionTestCycles

/-! # Normalized conormal wedges under resolution-induced Tor restriction

Source: Stacks Project, Tags 09PQ and 00LS.
(blueprint: new-t2-self-tor-restriction-conormal-wedge). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- A certified algebraic Tor restriction carries the normalized pure conormal wedge
to the wedge of the images of its ideal elements. No sheaf or derived-category
coordinate appears in this statement.
Source: Stacks Project, Tag 09PQ (resolution-independent products), Tag 00LS
(augmentation-preserving comparison and its homotopy uniqueness).
(blueprint: new-t2-self-tor-restriction-conormal-wedge).

Proof: Choose projective quotient resolutions P over A and Q over B, and lift
the Koszul augmentation of g to P. After quotient tensoring the standard top
wedge is a cycle. Normalize its image by selfTorConormalComparison_spec.
Apply the certificate to P,Q: its augmented comparison a and tensor comparison
k carry this class to Q-homology. Extend the Koszul complex along φ; on each
exterior power, generator-wise scalar extension gives the Koszul complex of g'.
The equation on g and g' makes this a chain map and identifies the standard
wedge tensors. The adjoint of a composed with the Koszul lift is an
augmentation-preserving Koszul lift into Q. Normalize that lift by
selfTorConormalComparison_spec over B. The certificate equation on cycles
identifies the two homology classes. Cancel Q.isoLeftDerivedObj to get the
asserted equality. This argument needs neither flatness of φ nor regularity
or finite generation of I,J. In degree zero the wedge is 1 and the quotient
ring map preserves 1; if either quotient is zero the corresponding classes
are zero. Characteristic two uses the alternating exterior wedge throughout. -/
theorem selfTor_restriction_conormal_wedge
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (φ : A →+* B) (n : ℕ)
    (q : (((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) →
      (((Tor' (ModuleCat.{u} B) n).obj (ModuleCat.of B (B ⧸ J))).obj
        (ModuleCat.of B (B ⧸ J))))
    (hq : IsSelfTorRestrictionMap A B I J φ n q)
    (g : Fin n → I) (g' : Fin n → J) (hg : ∀ j, φ (g j) = g' j) :
    q (selfTorConormalComparison A I n
      (exteriorPower.ιMulti (A ⧸ I) n (fun j ↦ I.toCotangent (g j)))) =
      selfTorConormalComparison B J n
        (exteriorPower.ιMulti (B ⧸ J) n (fun j ↦ J.toCotangent (g' j)))  := by
  classical
  let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
  let Q := projectiveResolution (ModuleCat.of B (B ⧸ J))
  let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
  obtain ⟨ψ, a, k, _, ha, hk, hcycles⟩ := hq P Q
  obtain ⟨aA, aB, haA, haB, zA, zB, hzA, hzB, hz⟩ :=
    exists_koszul_restriction_test_cycles A B I J φ n g g' hg P Q ψ a k ha hk
  have hA := selfTorConormalComparison_spec A I n n g P aA haA
    (fun j ↦ Finsupp.single j 1) zA hzA
  have hB := selfTorConormalComparison_spec B J n n g' Q aB haB
    (fun j ↦ Finsupp.single j 1) zB hzB
  simp only [Finsupp.linearCombination_single, one_smul] at hA hB
  have hp := congrArg (fun f ↦ f zA) (HomologicalComplex.homologyπ_naturality
    (TA.map aA) n)
  have hq' := congrArg (fun f ↦ f zB) (HomologicalComplex.homologyπ_naturality
    (TB.map aB) n)
  change (HomologicalComplex.homologyMap (TA.map aA) n)
    ((TA.obj _).homologyπ n zA) = _ at hp
  change (HomologicalComplex.homologyMap (TB.map aB) n)
    ((TB.obj _).homologyπ n zB) = _ at hq'
  simp only [ConcreteCategory.comp_apply] at hp hq'
  have hA' := hA.trans hp
  have hB' := hB.trans hq'
  have hm := hcycles (HomologicalComplex.cyclesMap (TA.map aA) n zA)
    (HomologicalComplex.cyclesMap (TB.map aB) n zB) hz
  rw [← hA', ← hB'] at hm
  have he : (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
      ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom
        (selfTorConormalComparison A I n
          (exteriorPower.ιMulti (A ⧸ I) n (fun j ↦ I.toCotangent (g j))))) =
      selfTorConormalComparison A I n
        (exteriorPower.ιMulti (A ⧸ I) n (fun j ↦ I.toCotangent (g j))) := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      congrArg (fun f ↦ f (selfTorConormalComparison A I n
        (exteriorPower.ιMulti (A ⧸ I) n (fun j ↦ I.toCotangent (g j)))))
        (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom_inv_id
  rw [he] at hm
  exact (ModuleCat.mono_iff_injective
    (Q.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).hom).mp
      inferInstance hm

end AlgebraicGeometry
