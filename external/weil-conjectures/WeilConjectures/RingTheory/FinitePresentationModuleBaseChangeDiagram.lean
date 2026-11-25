/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink
import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # The presentation-matrix diagram before its colimit verification
Source: Stacks Project, Algebra, Tags 00QX and 00R1.
(blueprint: lem-weil-pbc-finite-presentation-base-change-diagram).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

private def coordinates {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (n : ℕ) : (Fin n → R) →ₛₗ[φ] (Fin n → T) where
  toFun x := fun a ↦ φ (x a)
  map_add' x y := by ext a; exact φ.map_add _ _
  map_smul' r x := by ext a; exact φ.map_mul _ _

private theorem coordinates_matrix {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (C : Matrix (Fin n) (Fin m) T) (h : ∀ a b, φ (A a b) = C a b)
    (x : Fin m → R) :
    coordinates φ n (A.toLin' x) = C.toLin' (coordinates φ m x) := by
  ext a
  simp only [coordinates, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]
  simp only [map_sum, map_mul, h]

private def presentationLift {R T P : Type*} [CommRing R] [CommRing T]
    [AddCommGroup P] [Module T P] (φ : R →+* T) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R)
    (f : (Fin n → T) →ₗ[T] P) (g : (Fin m → T) →ₗ[T] (Fin n → T))
    (hex : Function.Exact g f) (hA : ∀ a b, φ (A a b) = LinearMap.toMatrix' g a b) :
    ((Fin n → R) ⧸ A.toLin'.range) →ₛₗ[φ] P :=
  A.toLin'.range.liftQ (f.comp (coordinates φ n)) (by
    rintro _ ⟨x, rfl⟩
    change f (coordinates φ n (A.toLin' x)) = 0
    rw [coordinates_matrix φ A (LinearMap.toMatrix' g) hA, Matrix.toLin'_toMatrix']
    exact (hex _).2 ⟨_, rfl⟩)

private theorem quotient_exact {R : Type*} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) :
    Function.Exact A.toLin' A.toLin'.range.mkQ := by
  intro x
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range, Set.mem_range]

private theorem presentation_baseChange {R T P : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [AddCommGroup P] [Module T P] [Module R P] [IsScalarTower R T P]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (f : (Fin n → T) →ₗ[T] P) (g : (Fin m → T) →ₗ[T] (Fin n → T))
    (hf : Function.Surjective f) (hex : Function.Exact g f)
    (hA : ∀ a b, algebraMap R T (A a b) = LinearMap.toMatrix' g a b)
    (q : ((Fin n → R) ⧸ A.toLin'.range) →ₗ[R] P)
    (hq : ∀ x, q (A.toLin'.range.mkQ x) = f (coordinates (algebraMap R T) n x)) :
    IsBaseChange T q := by
  let c (k : ℕ) : (Fin k → R) →ₗ[R] (Fin k → T) :=
    (Algebra.linearMap R T).compLeft (Fin k)
  apply IsBaseChange.of_right_exact T (c m) (c n) q
    (f := A.toLin') (g := A.toLin'.range.mkQ) (f' := g) (g' := f)
  · apply LinearMap.ext
    intro x
    simpa [c, coordinates, LinearMap.compLeft, Matrix.toLin'_toMatrix',
      Algebra.linearMap_apply, Function.comp_def] using
      coordinates_matrix (algebraMap R T) A (LinearMap.toMatrix' g) hA x
  · apply LinearMap.ext
    intro x
    exact hq x
  · exact (IsBaseChange.linearMap R T).finitePow (Fin m)
  · exact (IsBaseChange.linearMap R T).finitePow (Fin n)
  · exact quotient_exact A
  · exact Submodule.mkQ_surjective _
  · exact hex
  · exact hf

/-- Construct the diagram from a lifted finite presentation matrix and its tensor comparison maps.
Source: Stacks Project, Algebra, Tag 00QX, presentation-matrix paragraph,
non-local construction used in Tag 00R1.
(blueprint: lem-weil-pbc-finite-presentation-base-change-diagram)

Proof: The finite presentation f, g and its lifted matrix A₀ are given explicitly.
Restrict to the upper tail of i₀. It is nonempty and directed. Every original stage
maps to a tail stage, so its full inclusion is final.
At each tail stage take the quotient of its finite free module by the image of the
lifted matrix. The ring transition maps preserve these images and descend to additive
maps of quotients. Identities, compositions, and scalar compatibility follow on
representatives, producing D and ν. The images of the coordinate vectors generate
these modules. Each stage ring is countable: a finite-type integer algebra is a
quotient of a polynomial algebra in finitely many variables over ℤ. The finite powers
and their quotients are therefore countable and small in universe v. Transport the
explicit quotients, their actions and maps through `Shrink` equivalences to Type v.
Tensor right exactness identifies each base-changed quotient with the quotient by the
transported matrix, using the finite-product tensor equivalence for the free terms.
At a later stage this is precisely its defining quotient; over S it is the original
presentation of M. On pure tensors the resulting equivalences send y tensor x to y
times the image of x. No additive colimit property is asserted here.
-/
theorem exists_finitePresentation_baseChange_diagram
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hfinite : ∀ i, Algebra.FiniteType ℤ (B.obj i))
    (M : Type v) [AddCommGroup M] [Module S M]
    (n m : ℕ) (f : (Fin n → S) →ₗ[S] M)
    (g : (Fin m → S) →ₗ[S] (Fin n → S))
    (hf : Function.Surjective f) (hexact : Function.Exact g f)
    (i₀ : I) (A₀ : Matrix (Fin n) (Fin m) (B.obj i₀))
    (hA : ∀ a b, (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i₀)) (A₀ a b) =
      LinearMap.toMatrix' g a b) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (F : J ⥤ I) (_ : F.Final)
      (D : J ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
      (_ : ∀ j, Module (B.obj (F.obj j)) (D.obj j)),
      (∀ (i j : J) (h : i ≤ j) (y : B.obj (F.obj i)) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (F.map (homOfLE h))).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ j (y : B.obj (F.obj j)) (x : D.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app (F.obj j))) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) ∧
      (∀ j, Module.Finite (B.obj (F.obj j)) (D.obj j)) ∧
      (∀ (i j : J) (h : i ≤ j),
        letI := (B.map (F.map (homOfLE h))).hom.toAlgebra
        ∃ e : B.obj (F.obj j) ⊗[B.obj (F.obj i)] D.obj i ≃ₗ[B.obj (F.obj j)] D.obj j,
          ∀ (y : B.obj (F.obj j)) (x : D.obj i),
            e (y ⊗ₜ[B.obj (F.obj i)] x) = y • (D.map (homOfLE h)).hom x) ∧
      (∀ j,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app (F.obj j))).toAlgebra
        ∃ e : S ⊗[B.obj (F.obj j)] D.obj j ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj j),
            e (y ⊗ₜ[B.obj (F.obj j)] x) =
              y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) := by
  classical
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨by
    intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let F : J ⥤ I :=
    { obj := fun j ↦ j.val
      map := fun h ↦ homOfLE (leOfHom h) }
  have hF : F.Final := by
    apply Functor.final_of_exists_of_isFiltered
    · intro i
      obtain ⟨j, hij, h₀j⟩ := exists_ge_ge i i₀
      exact ⟨⟨j, h₀j⟩, ⟨homOfLE hij⟩⟩
    · intro i j s t
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  let A (j : J) : Matrix (Fin n) (Fin m) (B.obj j.val) :=
    fun a b ↦ (B.map (homOfLE j.property)).hom (A₀ a b)
  let Q (j : J) := (Fin n → B.obj j.val) ⧸ (A j).toLin'.range
  let (j : J) : Algebra.FiniteType ℤ (B.obj j.val) := hfinite j.val
  let (j : J) : Small.{v} (B.obj j.val) := Algebra.FiniteType.small.{v} (R := ℤ)
  let (j : J) : Small.{v} (Q j) := Module.Finite.small (B.obj j.val) (Q j)
  let E (j : J) : Shrink.{v} (Q j) ≃ₗ[B.obj j.val] Q j := Shrink.linearEquiv _ _
  let p (j : J) : (Fin n → B.obj j.val) →ₗ[B.obj j.val] Shrink.{v} (Q j) :=
    (E j).symm.toLinearMap.comp (A j).toLin'.range.mkQ
  have hp (j : J) : Function.Surjective (p j) :=
    (E j).symm.surjective.comp (Submodule.mkQ_surjective _)
  have htrans {i j : J} (h : i ⟶ j) (a : Fin n) (b : Fin m) :
      (B.map (F.map h)).hom (A i a b) = A j a b := by
    exact (ConcreteCategory.congr_hom
      (B.map_comp (homOfLE i.property) (F.map h)) (A₀ a b)).symm
  let t {i j : J} (h : i ⟶ j) : Q i →ₛₗ[(B.map (F.map h)).hom] Q j :=
    presentationLift (B.map (F.map h)).hom (A i) (A j).toLin'.range.mkQ
      (A j).toLin' (quotient_exact (A j)) (by
        intro a b
        exact (htrans h a b).trans
          (congrArg (fun C ↦ C a b) (LinearMap.toMatrix'_toLin' (A j))).symm)
  let d {i j : J} (h : i ⟶ j) : Shrink.{v} (Q i) →+ Shrink.{v} (Q j) :=
    (E j).symm.toAddMonoidHom.comp ((t h).toAddMonoidHom.comp (E i).toAddMonoidHom)
  have hd {i j : J} (h : i ⟶ j) (x : Fin n → B.obj i.val) :
      d h (p i x) = p j (coordinates (B.map (F.map h)).hom n x) := by
    change (E j).symm (t h (E i ((E i).symm ((A i).toLin'.range.mkQ x)))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hds {i j : J} (h : i ⟶ j) (r : B.obj i.val) (x : Shrink.{v} (Q i)) :
      d h (r • x) = (B.map (F.map h)).hom r • d h x := by
    dsimp [d]
    rw [(E i).map_smul, (t h).map_smulₛₗ, (E j).symm.map_smul]
  let D : J ⥤ AddCommGrpCat.{v} :=
    { obj := fun j ↦ AddCommGrpCat.of (Shrink.{v} (Q j))
      map := fun h ↦ AddCommGrpCat.ofHom (d h)
      map_id := by
        intro j
        apply AddCommGrpCat.ext
        intro x
        obtain ⟨x, rfl⟩ := hp j x
        change d (𝟙 j) (p j x) = p j x
        rw [hd]
        congr 1
        ext a
        simp [coordinates, F]
      map_comp := by
        intro i j k h l
        apply AddCommGrpCat.ext
        intro x
        obtain ⟨x, rfl⟩ := hp i x
        change d (h ≫ l) (p i x) = d l (d h (p i x))
        rw [hd, hd, hd]
        congr 1
        ext a
        exact ConcreteCategory.congr_hom (B.map_comp (F.map h) (F.map l)) (x a) }
  let κh (j : J) : B.obj j.val →+* S :=
    @CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app j.val)
  have hκA (j : J) (a : Fin n) (b : Fin m) :
      (κh j) (A j a b) = LinearMap.toMatrix' g a b := by
    exact (ConcreteCategory.congr_hom (κ.naturality (homOfLE j.property))
      (A₀ a b)).trans (hA a b)
  let q (j : J) : Q j →ₛₗ[κh j] M :=
    presentationLift (κh j) (A j) f g hexact (hκA j)
  let leg (j : J) : Shrink.{v} (Q j) →+ M :=
    (q j).toAddMonoidHom.comp (E j).toAddMonoidHom
  have hleg (j : J) (x : Fin n → B.obj j.val) :
      leg j (p j x) = f (coordinates (κh j) n x) := by
    change q j (E j ((E j).symm ((A j).toLin'.range.mkQ x))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  let ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M) :=
    { app := fun j ↦ AddCommGrpCat.ofHom (leg j)
      naturality := by
        intro i j h
        apply AddCommGrpCat.ext
        intro x
        obtain ⟨x, rfl⟩ := hp i x
        change leg j (d h (p i x)) = leg i (p i x)
        rw [hd, hleg, hleg]
        congr 1
        ext a
        exact ConcreteCategory.congr_hom (κ.naturality (F.map h)) (x a) }
  refine ⟨J, inferInstance, inferInstance, inferInstance, F, hF, D, ν,
    (fun j ↦ inferInstanceAs (Module (B.obj j.val) (Shrink.{v} (Q j)))),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h r x
    exact hds (homOfLE h) r x
  · intro j r x
    change leg j (r • x) = (κh j) r • leg j x
    dsimp [leg]
    rw [(E j).map_smul, (q j).map_smulₛₗ]
  · intro j
    exact inferInstanceAs (Module.Finite (B.obj j.val) (Shrink.{v} (Q j)))
  · intro i j h
    let φ : B.obj i.val →+* B.obj j.val := (B.map (F.map (homOfLE h))).hom
    let : Algebra (B.obj i.val) (B.obj j.val) := φ.toAlgebra
    let : Module (B.obj i.val) (D.obj j) := Module.compHom (D.obj j) φ
    let : IsScalarTower (B.obj i.val) (B.obj j.val) (D.obj j) :=
      IsScalarTower.of_algebraMap_smul fun r x ↦ rfl
    let dl : Q i →ₗ[B.obj i.val] D.obj j :=
      { toAddHom := ((E j).symm.toAddMonoidHom.comp (t (homOfLE h)).toAddMonoidHom)
        map_smul' := by
          intro r x
          change (E j).symm (t (homOfLE h) (r • x)) = _
          rw [(t (homOfLE h)).map_smulₛₗ, (E j).symm.map_smul]
          rfl }
    have hb := presentation_baseChange (A i) (p j) (A j).toLin' (hp j)
      (by
        intro x
        change p j x = 0 ↔ _
        rw [show p j x = (E j).symm ((A j).toLin'.range.mkQ x) from rfl,
          LinearEquiv.map_eq_zero_iff]
        exact quotient_exact (A j) x)
      (by
        intro a b
        rw [LinearMap.toMatrix'_toLin']
        change φ (A i a b) = A j a b
        exact htrans (homOfLE h) a b) dl (by intro x; rfl)
    let e := IsBaseChange.comp_equiv (E i) dl hb
    exact ⟨e.equiv, fun y x ↦ e.equiv_tmul y x⟩
  · intro j
    let φ : B.obj j.val →+* S := κh j
    let : Algebra (B.obj j.val) S := φ.toAlgebra
    let : Module (B.obj j.val) M := Module.compHom M φ
    let : IsScalarTower (B.obj j.val) S M :=
      IsScalarTower.of_algebraMap_smul fun r x ↦ rfl
    let ql : Q j →ₗ[B.obj j.val] M :=
      { toAddHom := (q j).toAddMonoidHom
        map_smul' := by intro r x; exact (q j).map_smulₛₗ r x }
    have hb := presentation_baseChange (A j) f g hf hexact (hκA j) ql (by intro x; rfl)
    have he := IsBaseChange.comp_equiv (E j) ql hb
    exact ⟨he.equiv, fun y x ↦ he.equiv_tmul y x⟩

end Module
