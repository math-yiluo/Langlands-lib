/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndEtale

/-!
# Directed unions of étale subalgebras are ind-étale

If an `R`-algebra `S` is the directed union of a family `𝒜` of subalgebras each of which is étale
over `R`, then `S` is ind-étale over `R` (`Algebra.IndEtale.of_directedOn`): it is the filtered
colimit of the members of `𝒜`.

This is the form in which the strict henselization at a boundary point `z` of a curve, the
inertia invariants of `B_Q`, is ind-étale: it is the union of the localizations of the integral
closures in the finite subextensions fixed by inertia, which are étale at the point over `z`
(blueprint `lemma-boundary-stalk--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Subalgebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒜 : Set (Subalgebra R S))

/-- The diagram of the members of a family of subalgebras, ordered by inclusion. -/
@[simps]
def setDiag : 𝒜 ⥤ CommAlgCat.{u} R where
  obj A := .of R A.1
  map h := CommAlgCat.ofHom (Subalgebra.inclusion (Subtype.coe_le_coe.mpr h.le))
  map_id _ := CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl)
  map_comp _ _ := CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl)

variable {𝒜} (hdir : DirectedOn (· ≤ ·) 𝒜) (hcov : ∀ x, ∃ A ∈ 𝒜, x ∈ A)

include hdir in
/-- The images of an element in a cocone under the members containing it agree. -/
lemma cocone_setDiag_eq (c : Cocone (setDiag 𝒜)) {A B : 𝒜} {x : S} (hA : x ∈ A.1)
    (hB : x ∈ B.1) : (c.ι.app A).hom ⟨x, hA⟩ = (c.ι.app B).hom ⟨x, hB⟩ := by
  obtain ⟨C, hC, hAC, hBC⟩ := hdir A.1 A.2 B.1 B.2
  have h₁ := congrArg (fun f ↦ f.hom ⟨x, hA⟩) (c.w (homOfLE (show A ≤ ⟨C, hC⟩ from hAC)))
  have h₂ := congrArg (fun f ↦ f.hom ⟨x, hB⟩) (c.w (homOfLE (show B ≤ ⟨C, hC⟩ from hBC)))
  exact h₁.symm.trans h₂

/-- The value of the descended map at `x`, computed in a member containing `x`. -/
noncomputable def setDescFun (c : Cocone (setDiag 𝒜)) (x : S) : c.pt :=
  (c.ι.app ⟨(hcov x).choose, (hcov x).choose_spec.1⟩).hom ⟨x, (hcov x).choose_spec.2⟩

include hdir in
lemma setDescFun_eq (c : Cocone (setDiag 𝒜)) (A : 𝒜) {x : S} (hx : x ∈ A.1) :
    setDescFun hcov c x = (c.ι.app A).hom ⟨x, hx⟩ :=
  cocone_setDiag_eq hdir c _ hx

include hdir hcov in
lemma exists_mem_of_mem₂ (x y : S) : ∃ A : 𝒜, x ∈ A.1 ∧ y ∈ A.1 := by
  obtain ⟨A, hA, hxA⟩ := hcov x
  obtain ⟨B, hB, hyB⟩ := hcov y
  obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA B hB
  exact ⟨⟨C, hC⟩, hAC hxA, hBC hyB⟩

include hdir in
/-- The descended algebra map. -/
noncomputable def setDescAlgHom (c : Cocone (setDiag 𝒜)) : S →ₐ[R] c.pt where
  toFun := setDescFun hcov c
  map_one' := by
    obtain ⟨A, hA, -⟩ := hcov 1
    rw [setDescFun_eq hdir hcov c ⟨A, hA⟩ (one_mem _)]
    exact map_one _
  map_zero' := by
    obtain ⟨A, hA, -⟩ := hcov 0
    rw [setDescFun_eq hdir hcov c ⟨A, hA⟩ (zero_mem _)]
    exact map_zero _
  map_mul' x y := by
    obtain ⟨A, hx, hy⟩ := exists_mem_of_mem₂ hdir hcov x y
    change setDescFun hcov c (x * y) = setDescFun hcov c x * setDescFun hcov c y
    rw [setDescFun_eq hdir hcov c A (mul_mem hx hy), setDescFun_eq hdir hcov c A hx,
      setDescFun_eq hdir hcov c A hy]
    exact map_mul (c.ι.app A).hom ⟨x, hx⟩ ⟨y, hy⟩
  map_add' x y := by
    obtain ⟨A, hx, hy⟩ := exists_mem_of_mem₂ hdir hcov x y
    change setDescFun hcov c (x + y) = setDescFun hcov c x + setDescFun hcov c y
    rw [setDescFun_eq hdir hcov c A (add_mem hx hy), setDescFun_eq hdir hcov c A hx,
      setDescFun_eq hdir hcov c A hy]
    exact map_add (c.ι.app A).hom ⟨x, hx⟩ ⟨y, hy⟩
  commutes' r := by
    obtain ⟨A, hA, -⟩ := hcov 0
    change setDescFun hcov c (algebraMap R S r) = algebraMap R c.pt r
    rw [setDescFun_eq hdir hcov c ⟨A, hA⟩ (Subalgebra.algebraMap_mem _ r)]
    exact (c.ι.app _).hom.commutes r

include hdir in
/-- A directed family of subalgebras covering `S` is a colimit presentation of `S`. -/
noncomputable def setColimitPresentation : ColimitPresentation 𝒜 (CommAlgCat.of R S) where
  diag := setDiag 𝒜
  ι :=
    { app A := CommAlgCat.ofHom A.1.val
      naturality _ _ _ := CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl) }
  isColimit :=
    { desc c := CommAlgCat.ofHom (setDescAlgHom hdir hcov c)
      fac c A := CommAlgCat.hom_ext (AlgHom.ext fun x ↦ setDescFun_eq hdir hcov c A x.2)
      uniq c m hm := by
        refine CommAlgCat.hom_ext (AlgHom.ext fun x ↦ ?_)
        obtain ⟨A, hA, hxA⟩ := hcov x
        have key := congrArg (fun f ↦ f.hom ⟨x, hxA⟩) (hm ⟨A, hA⟩)
        exact key.trans (setDescFun_eq hdir hcov c ⟨A, hA⟩ hxA).symm }

end Subalgebra

/-- **A directed union of étale subalgebras is ind-étale.** -/
theorem Algebra.IndEtale.of_directedOn {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (𝒜 : Set (Subalgebra R S)) (hdir : DirectedOn (· ≤ ·) 𝒜) (hcov : ∀ x, ∃ A ∈ 𝒜, x ∈ A)
    (het : ∀ A ∈ 𝒜, Algebra.Etale R A) : Algebra.IndEtale R S := by
  obtain ⟨A₀, hA₀, -⟩ := hcov 0
  have : Nonempty 𝒜 := ⟨⟨A₀, hA₀⟩⟩
  have : IsDirected 𝒜 (· ≤ ·) := ⟨fun A B ↦ by
    obtain ⟨C, hC, hAC, hBC⟩ := hdir A.1 A.2 B.1 B.2
    exact ⟨⟨C, hC⟩, hAC, hBC⟩⟩
  exact ⟨𝒜, inferInstance, inferInstance, Subalgebra.setColimitPresentation hdir hcov,
    fun A ↦ het A.1 A.2⟩
