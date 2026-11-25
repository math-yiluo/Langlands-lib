/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.RingTheory.SymmetricConormalPresentationTransport
import WeilConjectures.RingTheory.SymmetricProjectivePresentationConormal

/-! # Free conormal presentation of the symmetric algebra of a projective conormal module

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CE, lines 357–414.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra.Presentation

/-- Identity on conormal representatives, with the quotient coefficient equivalence. -/
private noncomputable def conormalQuotientEquiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    let ρ := P.quotientEquiv.toRingEquiv
    let _ := RingHomInvPair.of_ringEquiv ρ
    let _ := RingHomInvPair.of_ringEquiv_symm ρ
    P.ker.Cotangent ≃ₛₗ[(↑ρ : P.Quotient →+* A)] P.toExtension.Cotangent := by
  have := RingHomInvPair.of_ringEquiv P.quotientEquiv.toRingEquiv
  have := RingHomInvPair.of_ringEquiv_symm P.quotientEquiv.toRingEquiv
  refine
    { __ := P.toExtension.cotangentEquivCotangentKer.symm.toAddEquiv
      map_smul' := ?_ }
  intro r x
  induction r using Quotient.inductionOn' with
  | h r =>
    apply Extension.Cotangent.ext
    change (Ideal.Quotient.mk P.ker r) • x =
      (algebraMap P.Ring A r • (Extension.Cotangent.of x)).val
    rw [algebraMap_smul, Extension.Cotangent.val_smul']
    rfl

/-- A finite polynomial presentation with projective conormal module produces a symmetric
algebra whose canonical finite polynomial map has free conormal module. The linear
equivalence permits a universe change of the conormal module.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CE, lines 357–414, at `a = 1`.
(blueprint: lem-weil-pbc-symmetric-conormal-free-presentation)

Proof. Write `P = R[x]/I`, and let the `m` relations generate `I`. Their classes give a
surjection `q : A^m → P.toExtension.Cotangent`. Projectivity splits this map; if `K` is its
kernel, the splitting identifies `P.toExtension.Cotangent × K` with `A^m`. Present the
symmetric algebra by `R[x,y]`, sending each `y` to the class of the corresponding relation.
The symmetric-projective-presentation-conormal lemma gives the conormal module of this
surjection as `Sym_A(I/I²) ⊗_A ((I/I²) × K)`, hence as the free module `Sym_A(I/I²)^m`.
Use `P.quotientEquiv` to identify `R[x]/I` with `A`, and the given equivalence to identify
its conormal module with `M`. The universal property transports the symmetric algebra and
its polynomial surjection along these equivalences. Reindex the two finite sets of
variables by `Fin (n + m)`. The induced isomorphisms of ideals, their squares and their
quotients transport the free conormal module to the kernel of the resulting map. These
operations also apply when either finite index is empty or `A` is the zero ring. -/
theorem symmetric_conormal_free_presentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m))
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Projective A M]
    (e : P.toExtension.Cotangent ≃ₗ[A] M)
    [Algebra R (SymmetricAlgebra A M)] [IsScalarTower R A (SymmetricAlgebra A M)] :
    let x : Fin m → M := fun j ↦ e (Extension.Cotangent.mk
      ⟨P.relation j, P.relation_mem_ker j⟩)
    let f : MvPolynomial (Fin (n + m)) R →ₐ[R] SymmetricAlgebra A M :=
      MvPolynomial.aeval (fun i ↦ Sum.elim
        (fun j ↦ algebraMap A (SymmetricAlgebra A M) (P.val j))
        (fun j ↦ SymmetricAlgebra.ι A M (x j)) (finSumFinEquiv.symm i))
    Module.Free (MvPolynomial (Fin (n + m)) R ⧸ RingHom.ker f.toRingHom)
      (RingHom.ker f.toRingHom).Cotangent := by
  classical
  let I : Ideal (MvPolynomial (Fin n) R) := P.ker
  let B := MvPolynomial (Fin n) R ⧸ I
  let C := SymmetricAlgebra B I.Cotangent
  let z : Fin m → I := fun j ↦ ⟨P.relation j, P.relation_mem_ker j⟩
  let q : (Fin m → B) →ₗ[B] I.Cotangent :=
    (Pi.basisFun B (Fin m)).constr B (fun j ↦ I.toCotangent (z j))
  have hq (j : Fin m) : q (Pi.single j 1) = I.toCotangent (z j) := by
    rw [← Pi.basisFun_apply B]
    exact (Pi.basisFun B (Fin m)).constr_basis B _ j
  have := RingHomInvPair.of_ringEquiv P.quotientEquiv.toRingEquiv
  have := RingHomInvPair.of_ringEquiv_symm P.quotientEquiv.toRingEquiv
  have : Module.Projective B I.Cotangent :=
    Module.Projective.of_equiv (P.conormalQuotientEquiv.trans e).symm
  let φ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* C :=
    MvPolynomial.eval₂Hom ((algebraMap B C).comp (Ideal.Quotient.mk I))
      (fun j ↦ SymmetricAlgebra.ι B I.Cotangent (I.toCotangent (z j)))
  let α : MvPolynomial (Fin m) B →ₐ[B] C :=
    MvPolynomial.aeval (fun j ↦ SymmetricAlgebra.ι B I.Cotangent (I.toCotangent (z j)))
  obtain ⟨hφ, _, _, _, _, _, _, _, _, _, _, _, ⟨d⟩, ⟨d'⟩⟩ :=
    Algebra.symmetric_projective_presentation_conormal R n m I z
      P.span_range_relation_eq_ker q hq φ
      (by intro r; exact MvPolynomial.eval₂Hom_C _ _ _)
      (by intro j; rw [hq]; exact MvPolynomial.eval₂Hom_X' _ _ _)
      α (by intro j; rw [hq]; exact MvPolynomial.aeval_X _ _)
  have : Module.Free C (TensorProduct B C (I.Cotangent × LinearMap.ker q)) :=
    Module.Free.of_equiv d'.symm
  have : Module.Free C (Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent :=
    Module.Free.of_equiv d.symm
  obtain ⟨ρ, ⟨c⟩⟩ := P.symmetric_conormal_presentation_transport M e hφ
  have := RingHomInvPair.of_ringEquiv ρ
  have := RingHomInvPair.of_ringEquiv_symm ρ
  exact Module.Free.of_equiv c.symm

end Algebra.Presentation
