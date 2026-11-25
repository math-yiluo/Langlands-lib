/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Tensor base changes over a directed union of subalgebras

Source: Stacks Project, Algebra, Tags 00DD, 00D6 and 00D7; Tag 033C,
third paragraph. (blueprint: lem-weil-pbc-directed-subalgebra-tensor-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Subalgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Base change over a directed union of subalgebras gives a filtered ring colimit.
There is no smoothness, finite-type or normality assumption.

Source: Stacks Project, Algebra, Tags 00DD, 00D6 and 00D7; Tag 033C,
third paragraph. (blueprint: lem-weil-pbc-directed-subalgebra-tensor-colimit).

Proof: index by the subalgebras A in P, ordered by inclusion. Nonemptiness and
directedness make this a small filtered category. The assumption A0 ≤ A gives
A its canonical A0-algebra structure. Form the tensor-product ring diagram
A tensor B with maps induced by inclusions, and the cocone with vertex R tensor B.
The inclusions of A into R are colimiting by
`CommRingCat.isColimitSubalgebraCocone`: the covering hypothesis gives supremum top.
For any ring cocone c on the tensor diagram, restriction to A tensor 1 gives
a compatible family of ring maps out of A, hence a ring map r from R into c's
vertex. Restriction to 1 tensor B gives a ring map b from B into c's vertex
independent of the chosen stage: any two stages have a common upper bound.
The maps r and b agree on A0 by the tensor balancing relation at any stage.
Give c's vertex the A0-algebra structure induced by b. The universal property
of the algebra tensor product then gives a ring map from R tensor B to c's
vertex. Its composites with the coprojections agree with c on both tensor
factors and hence on the entire tensor product. For uniqueness, restriction
to the R factor is determined by the covering of R by the A, and restriction
to B is determined at any single stage. Tensor-product extensionality then
determines the whole ring map. This proves the cocone is colimiting; compare
it with the chosen categorical colimit to obtain the ring equivalence.
Each stage is A tensor B, and every type lives in universe u. The existential
algebra structure in the conclusion is the canonical one induced by A0 ≤ A.
-/
theorem exists_tensorProduct_colimit_of_directed_cover
    {R : Type u} [CommRing R] (A0 : Subalgebra ℤ R)
    (B : Type u) [CommRing B] [Algebra A0 B]
    (P : Set (Subalgebra ℤ R)) (hne : P.Nonempty)
    (hdir : DirectedOn (· ≤ ·) P) (hcover : ∀ x : R, ∃ A ∈ P, x ∈ A)
    (hle : ∀ A ∈ P, A0 ≤ A) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ CommRingCat.{u}) (_ : HasColimit F),
      Nonempty ((colimit F : CommRingCat.{u}) ≃+* (R ⊗[A0] B)) ∧
      ∀ i : I, ∃ (A : Subalgebra ℤ R) (_ : A ∈ P) (_ : Algebra A0 A),
        Nonempty ((A ⊗[A0] B) ≃+* F.obj i) := by
  classical
  let I := {A : Subalgebra ℤ R // A ∈ P}
  have : Nonempty I := hne.to_subtype
  have : IsDirectedOrder I := ⟨fun i j ↦ by
    obtain ⟨A, hA, hi, hj⟩ := hdir i.1 i.2 j.1 j.2
    exact ⟨⟨A, hA⟩, hi, hj⟩⟩
  let aI (i : I) : Algebra A0 i.1 :=
    (Subalgebra.inclusion (hle i.1 i.2)).toRingHom.toAlgebra
  let inc {i j : I} (h : i ≤ j) : i.1 →ₐ[A0] j.1 :=
    { (Subalgebra.inclusion h).toRingHom with commutes' := fun _ ↦ Subtype.ext rfl }
  let val (i : I) : i.1 →ₐ[A0] R :=
    { i.1.val.toRingHom with commutes' := fun _ ↦ rfl }
  let F : I ⥤ CommRingCat.{u} :=
    { obj i := CommRingCat.of (i.1 ⊗[A0] B)
      map {i j} f := CommRingCat.ofHom
        (Algebra.TensorProduct.map (inc (leOfHom f)) (AlgHom.id A0 B)).toRingHom
      map_id i := by ext <;> rfl
      map_comp f g := by ext <;> rfl }
  let U : Cocone F :=
    { pt := CommRingCat.of (R ⊗[A0] B)
      ι :=
        { app i := CommRingCat.ofHom
            (Algebra.TensorProduct.map (val i) (AlgHom.id A0 B)).toRingHom
          naturality {i j} f := by ext <;> rfl } }
  have hsup : ⨆ i : I, i.1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨A, hA, hx⟩ := hcover x
    exact Algebra.mem_iSup_of_mem ⟨A, hA⟩ hx
  let V := CommRingCat.subalgebraCocone R (· ∈ P)
  have hV : IsColimit V := CommRingCat.isColimitSubalgebraCocone R (· ∈ P) hsup
  have hU : IsColimit U := by
    apply IsColimit.ofExistsUnique
    intro c
    let left (i : I) : i.1 →+* c.pt :=
      (c.ι.app i).hom.comp Algebra.TensorProduct.includeLeftRingHom
    let right (i : I) : B →+* c.pt :=
      (c.ι.app i).hom.comp Algebra.TensorProduct.includeRight.toRingHom
    have hleft {i j : I} (h : i ≤ j) (x : i.1) :
        left j (inc h x) = left i x := by
      have hh := ConcreteCategory.congr_hom (c.w (homOfLE h)) (x ⊗ₜ[A0] 1)
      simpa [F, left] using hh
    have hright {i j : I} (h : i ≤ j) : right i = right j := by
      ext b
      have hh := ConcreteCategory.congr_hom (c.w (homOfLE h)) (1 ⊗ₜ[A0] b)
      simpa [F, right] using hh.symm
    have hright_all (i j : I) : right i = right j := by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      exact (hright hik).trans (hright hjk).symm
    let cR : Cocone (CommRingCat.subalgebraDiagram R (· ∈ P)) :=
      { pt := c.pt
        ι :=
          { app i := CommRingCat.ofHom (left i)
            naturality {i j} f := by
              ext x
              exact hleft (leOfHom f) x } }
    let r : R →+* c.pt := (hV.desc cR).hom
    have hr (i : I) (x : i.1) : r (x : R) = left i x := by
      have hh := ConcreteCategory.congr_hom (hV.fac cR i) x
      exact hh
    let i0 : I := Classical.arbitrary I
    let b : B →+* c.pt := right i0
    have hb (i : I) : b = right i := hright_all i0 i
    let : Algebra A0 c.pt := (b.comp (algebraMap A0 B)).toAlgebra
    let bAlg : B →ₐ[A0] c.pt := { b with commutes' := fun _ ↦ rfl }
    let rAlg : R →ₐ[A0] c.pt :=
      { toRingHom := r, commutes' := by
          intro a
          change r (a : R) = b (algebraMap A0 B a)
          calc
            r (a : R) = left i0 (algebraMap A0 i0.1 a) := hr i0 (algebraMap A0 i0.1 a)
            _ = right i0 (algebraMap A0 B a) := by
              exact congrArg (c.ι.app i0).hom
                (RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap a)
            _ = b (algebraMap A0 B a) := rfl }
    let m : U.pt ⟶ c.pt := CommRingCat.ofHom
      (Algebra.TensorProduct.lift rAlg bAlg (fun _ _ ↦ Commute.all _ _)).toRingHom
    have hm (i : I) : U.ι.app i ≫ m = c.ι.app i := by
      apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext
      · ext x
        change r (val i x) * b 1 = (c.ι.app i).hom (x ⊗ₜ[A0] 1)
        rw [map_one, mul_one]
        exact hr i x
      · ext x
        change r 1 * b x = (c.ι.app i).hom (1 ⊗ₜ[A0] x)
        rw [map_one, one_mul, hb i]
        rfl
    refine ⟨m, hm, ?_⟩
    intro n hn
    apply CommRingCat.hom_ext
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      obtain ⟨A, hA, hx⟩ := hcover x
      let i : I := ⟨A, hA⟩
      have hh := ConcreteCategory.congr_hom ((hn i).trans (hm i).symm)
        ((⟨x, hx⟩ : i.1) ⊗ₜ[A0] (1 : B))
      exact hh
    · ext x
      have hh := ConcreteCategory.congr_hom ((hn i0).trans (hm i0).symm)
        ((1 : i0.1) ⊗ₜ[A0] x)
      exact hh
  let : HasColimit F := ⟨⟨U, hU⟩⟩
  refine ⟨I, inferInstance, inferInstance, F, inferInstance,
    ⟨CategoryTheory.Iso.commRingCatIsoToRingEquiv (colimit.isoColimitCocone ⟨U, hU⟩)⟩, ?_⟩
  intro i
  exact ⟨i.1, i.2, aI i, ⟨RingEquiv.refl _⟩⟩

end Subalgebra
