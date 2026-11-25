/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Transport of the symmetric presentation conormal module

Source: Stacks Project, Lemma 07CE, equation (16.3.1.1), at `a = 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Lift a coefficient and semilinear module equivalence to the symmetric algebras. -/
private theorem exists_symmetricEquiv
    {B : Type*} {A : Type*} [CommRing B] [CommRing A]
    {N : Type*} {M : Type*} [AddCommGroup N] [AddCommGroup M]
    [Module B N] [Module A M] (ρ : B ≃+* A)
    (c : N ≃ₛₗ[(↑ρ : B →+* A)] M) :
    ∃ E : SymmetricAlgebra B N ≃+* SymmetricAlgebra A M,
      (∀ b, E (algebraMap B _ b) = algebraMap A _ (ρ b)) ∧
      (∀ x, E (SymmetricAlgebra.ι B N x) = SymmetricAlgebra.ι A M (c x)) := by
  let : Algebra B (SymmetricAlgebra A M) :=
    ((algebraMap A _).comp ρ.toRingHom).toAlgebra
  let : Algebra A (SymmetricAlgebra B N) :=
    ((algebraMap B _).comp ρ.symm.toRingHom).toAlgebra
  let l : N →ₗ[B] SymmetricAlgebra A M :=
    { toFun := fun x ↦ SymmetricAlgebra.ι A M (c x)
      map_add' := by intros; simp
      map_smul' := by
        intro b x
        rw [c.map_smulₛₗ, map_smul]
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        rfl }
  let k : M →ₗ[A] SymmetricAlgebra B N :=
    { toFun := fun x ↦ SymmetricAlgebra.ι B N (c.symm x)
      map_add' := by intros; simp
      map_smul' := by
        intro a x
        rw [c.symm.map_smulₛₗ, map_smul]
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        rfl }
  let F := (SymmetricAlgebra.lift l).toRingHom
  let G := (SymmetricAlgebra.lift k).toRingHom
  have hF (b : B) : F (algebraMap B _ b) = algebraMap A _ (ρ b) :=
    (SymmetricAlgebra.lift l).commutes b
  have hG (a : A) : G (algebraMap A _ a) = algebraMap B _ (ρ.symm a) :=
    (SymmetricAlgebra.lift k).commutes a
  have hFι (x : N) : F (SymmetricAlgebra.ι B N x) =
      SymmetricAlgebra.ι A M (c x) := SymmetricAlgebra.lift_ι_apply l x
  have hGι (x : M) : G (SymmetricAlgebra.ι A M x) =
      SymmetricAlgebra.ι B N (c.symm x) := SymmetricAlgebra.lift_ι_apply k x
  have hGF : Function.LeftInverse G F := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap b => rw [hF, hG, ρ.symm_apply_apply]
    | ι x => rw [hFι, hGι, c.symm_apply_apply]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hFG : Function.RightInverse G F := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap a => rw [hG, hF, ρ.apply_symm_apply]
    | ι x => rw [hGι, hFι, c.apply_symm_apply]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact ⟨{ F with invFun := G, left_inv := hGF, right_inv := hFG }, hF, hFι⟩

/-- A commuting square of ring equivalences transports the kernel conormal module. -/
private theorem conormal_of_square
    {S : Type*} {T : Type*} {C : Type*} {D : Type*}
    [CommRing S] [CommRing T] [CommRing C] [CommRing D]
    (t : S ≃+* T) (E : C ≃+* D) (φ : T →+* C) (f : S →+* D)
    (h : ∀ x, E (φ (t x)) = f x) (hφ : Function.Surjective φ) :
    ∃ ρ : (S ⧸ RingHom.ker f) ≃+* C,
      Nonempty ((RingHom.ker f).Cotangent ≃ₛₗ[(↑ρ : (S ⧸ RingHom.ker f) →+* C)]
        (Algebra.Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent) := by
  let I := RingHom.ker f
  let J := RingHom.ker φ
  let Q := Algebra.Extension.ofSurjective φ.toIntAlgHom hφ
  have ht (x : S) : x ∈ I ↔ t x ∈ J := by
    change f x = 0 ↔ φ (t x) = 0
    rw [← h x, ← E.map_zero, E.injective.eq_iff]
  have h₁ : I ≤ J.comap t.toIntAlgEquiv.toAlgHom := fun x hx ↦ (ht x).mp hx
  have h₂ : J ≤ I.comap t.symm.toIntAlgEquiv.toAlgHom := by
    intro x hx
    apply (ht (t.symm x)).mpr
    simpa using hx
  let F := Ideal.mapCotangent (R := ℤ) I J t.toIntAlgEquiv.toAlgHom h₁
  let G := Ideal.mapCotangent (R := ℤ) J I t.symm.toIntAlgEquiv.toAlgHom h₂
  have hF (x : I) : F (I.toCotangent x) = J.toCotangent ⟨t x, h₁ x.2⟩ := rfl
  have hG (x : J) : G (J.toCotangent x) = I.toCotangent ⟨t.symm x, h₂ x.2⟩ := rfl
  let d : I.Cotangent ≃+ J.Cotangent :=
    { toFun := F
      invFun := G
      map_add' := F.map_add
      left_inv := by
        intro x
        obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
        rw [hF, hG]
        congr 1
        exact Subtype.ext (t.symm_apply_apply x)
      right_inv := by
        intro x
        obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
        rw [hG, hF]
        congr 1
        exact Subtype.ext (t.apply_symm_apply x) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := hφ (E.symm y)
    refine ⟨t.symm z, ?_⟩
    rw [← h, t.apply_symm_apply, hz, E.apply_symm_apply]
  let ρ := (f.quotientKerEquivOfSurjective hf).trans E.symm
  have hρ (r : S) : ρ (Ideal.Quotient.mk I r) = φ (t r) := by
    change E.symm (f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk I r)) = _
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk, ← h, E.symm_apply_apply]
  let c : I.Cotangent ≃+ Q.Cotangent :=
    d.trans Q.cotangentEquivCotangentKer.symm.toAddEquiv
  refine ⟨ρ, ⟨{ c with map_smul' := ?_ }⟩⟩
  intro r x
  induction r using Quotient.inductionOn' with
  | h r =>
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    apply Algebra.Extension.Cotangent.ext
    change F ((Ideal.Quotient.mk I r) • I.toCotangent x) =
      (ρ (Ideal.Quotient.mk I r) • Algebra.Extension.Cotangent.of (P := Q)
        (F (I.toCotangent x))).val
    rw [hρ]
    change F ((Ideal.Quotient.mk I r) • I.toCotangent x) =
      (algebraMap Q.Ring C (t r) • Algebra.Extension.Cotangent.of (P := Q)
        (F (I.toCotangent x))).val
    rw [algebraMap_smul, Algebra.Extension.Cotangent.val_smul']
    change F (r • I.toCotangent x) = t r • F (I.toCotangent x)
    rw [← I.toCotangent.map_smul, hF, hF, ← J.toCotangent.map_smul]
    congr 1
    exact Subtype.ext (t.map_mul r x)

namespace Algebra.Presentation

/-- Identity on conormal representatives with the quotient coefficient equivalence. -/
private noncomputable def conormalQuotientEquiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    P.ker.Cotangent ≃ₛₗ[(↑P.quotientEquiv.toRingEquiv : P.Quotient →+* A)]
      P.toExtension.Cotangent := by
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

/-- Changing the quotient coefficient ring, its conormal module, and the indexing of
polynomial variables preserves the conormal of the canonical symmetric presentation.
This transport statement does not assume projectivity or assert freeness.

Source: Stacks Project, Lemma 07CE, the polynomial presentation preceding
(16.3.1.1), https://stacks.math.columbia.edu/tag/07CE.
(blueprint: lem-weil-pbc-symmetric-conormal-presentation-transport)

Proof. Identify `P.Quotient` with `A` by `P.quotientEquiv`. On conormal representatives,
the identity identifies `P.ker.Cotangent` with `P.toExtension.Cotangent`, semilinearly
for this coefficient equivalence. Compose with `e`. The symmetric algebra universal
property gives a ring equivalence from the symmetric algebra over `P.Quotient` to
`SymmetricAlgebra A M`: on coefficients it is the quotient equivalence followed by
the coefficient embedding, and on degree-one generators it is the conormal equivalence
followed by `ι`. Applying the universal property to the inverse coefficient and module
equivalences supplies its inverse. Their compositions fix coefficients and all
degree-one generators, hence are identities.
Flatten the iterated polynomial ring with the polynomial sum equivalence, and reindex
`Fin n ⊕ Fin m` by `finSumFinEquiv`. On constants, old variables, and new variables,
the resulting commuting square compares exactly the displayed maps `φ` and `f`.
The domain ring equivalence maps `ker f` onto `ker φ` and maps their squares onto
one another, because the codomain ring map is injective. Restrict it to the ideals
and descend it and its inverse to the quotients by their squares. The resulting
additive equivalence is semilinear for the quotient-ring equivalence. Compose that
scalar equivalence with the first-isomorphism equivalence induced by the surjective
map `φ`. Reinterpret its ideal cotangent as the extension cotangent: both are the
same quotient, and the scalar actions agree on every polynomial representative.
This gives `ρ` and the asserted equivalence. Neither this argument nor the universal
properties require projectivity, a nonzero ring, or nonempty variable sets. -/
theorem symmetric_conormal_presentation_transport
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m))
    (M : Type w) [AddCommGroup M] [Module A M]
    (e : P.toExtension.Cotangent ≃ₗ[A] M)
    [Algebra R (SymmetricAlgebra A M)] [IsScalarTower R A (SymmetricAlgebra A M)] :
    let I : Ideal (MvPolynomial (Fin n) R) := P.ker
    let C := SymmetricAlgebra (MvPolynomial (Fin n) R ⧸ I) I.Cotangent
    let φ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* C :=
      MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (Fin n) R ⧸ I) C).comp
        (Ideal.Quotient.mk I))
        (fun j ↦ SymmetricAlgebra.ι (MvPolynomial (Fin n) R ⧸ I) I.Cotangent
          (I.toCotangent ⟨P.relation j, P.relation_mem_ker j⟩))
    let f : MvPolynomial (Fin (n + m)) R →ₐ[R] SymmetricAlgebra A M :=
      MvPolynomial.aeval (fun i ↦ Sum.elim
        (fun j ↦ algebraMap A (SymmetricAlgebra A M) (P.val j))
        (fun j ↦ SymmetricAlgebra.ι A M
          (e (Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)))
        (finSumFinEquiv.symm i))
    ∀ hφ : Function.Surjective φ,
      ∃ ρ : (MvPolynomial (Fin (n + m)) R ⧸ RingHom.ker f.toRingHom) ≃+* C,
        Nonempty ((RingHom.ker f.toRingHom).Cotangent
          ≃ₛₗ[(↑ρ : (MvPolynomial (Fin (n + m)) R ⧸ RingHom.ker f.toRingHom) →+* C)]
          (Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent) := by
  classical
  dsimp only
  intro hφ
  let I := P.ker
  let B := P.Quotient
  let C := SymmetricAlgebra B I.Cotangent
  let φ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* C :=
    MvPolynomial.eval₂Hom ((algebraMap B C).comp (Ideal.Quotient.mk I))
      (fun j ↦ SymmetricAlgebra.ι B I.Cotangent
        (I.toCotangent ⟨P.relation j, P.relation_mem_ker j⟩))
  let f : MvPolynomial (Fin (n + m)) R →ₐ[R] SymmetricAlgebra A M :=
    MvPolynomial.aeval (fun i ↦ Sum.elim
      (fun j ↦ algebraMap A (SymmetricAlgebra A M) (P.val j))
      (fun j ↦ SymmetricAlgebra.ι A M
        (e (Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)))
      (finSumFinEquiv.symm i))
  let c := P.conormalQuotientEquiv.trans e
  obtain ⟨E, hE, hEι⟩ := exists_symmetricEquiv P.quotientEquiv.toRingEquiv c
  let T : MvPolynomial (Fin (n + m)) R ≃+*
      MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    ((MvPolynomial.renameEquiv R
      (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin m)))).trans
      (MvPolynomial.sumAlgEquiv R (Fin m) (Fin n))).toRingEquiv
  have hTC (r : R) : T (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
    change MvPolynomial.sumAlgEquiv R (Fin m) (Fin n)
      (MvPolynomial.renameEquiv R
        (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin m)))
        (MvPolynomial.C r)) = _
    simp
  have hTX (i : Fin n ⊕ Fin m) : T (MvPolynomial.X (finSumFinEquiv i)) =
      Sum.elim (fun j ↦ MvPolynomial.C (MvPolynomial.X j)) MvPolynomial.X i := by
    change MvPolynomial.sumAlgEquiv R (Fin m) (Fin n)
      (MvPolynomial.renameEquiv R
        (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin m)))
        (MvPolynomial.X (finSumFinEquiv i))) = _
    cases i <;> simp
  have h : E.toRingHom.comp (φ.comp T.toRingHom) = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change E (φ (T (MvPolynomial.C r))) = f (MvPolynomial.C r)
      rw [hTC]
      simp only [φ, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      rw [hE]
      change algebraMap A (SymmetricAlgebra A M)
        (P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.C r))) = _
      rw [P.quotientEquiv_mk]
      simp [f, Generators.algebraMap_apply, ← IsScalarTower.algebraMap_apply R A]
    · intro i
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      change E (φ (T (MvPolynomial.X (finSumFinEquiv i)))) = _
      rw [hTX]
      cases i with
      | inl j =>
        simp only [Sum.elim_inl, φ, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
        rw [hE]
        change algebraMap A (SymmetricAlgebra A M)
          (P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.X j))) = _
        rw [P.quotientEquiv_mk]
        simp [f, Generators.algebraMap_apply]
      | inr j =>
        simp only [Sum.elim_inr, φ, MvPolynomial.eval₂Hom_X']
        rw [hEι]
        change SymmetricAlgebra.ι A M
          (e (Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)) = _
        simp [f]
  exact conormal_of_square T E φ f.toRingHom (fun x ↦ DFunLike.congr_fun h x) hφ

end Algebra.Presentation
