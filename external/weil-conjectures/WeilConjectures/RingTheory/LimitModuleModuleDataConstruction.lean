/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.LimitModuleRingData
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.RingTheory.BaseChangeDiagramElementwise
/-!
# Cokernels of a descended matrix on a later tail
Source: Stacks Project, Algebra, Tag 00QX (the choice of λ₂), and Tag 00R1.
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data)
-/

@[expose] public section
universe u v p
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom

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

private theorem matrix_lifts_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hκ : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)))
    (n m : ℕ) (A : Matrix (Fin n) (Fin m) S) :
    ∃ (i : I) (A₀ : Matrix (Fin n) (Fin m) (B.obj i)),
      ∀ a b, (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) (A₀ a b) =
        A a b := by
  classical
  let : IsFiltered I := inferInstance
  let : PreservesColimit B (forget CommRingCat) := inferInstance
  have reps (p : Fin n × Fin m) :
      ∃ (i : I) (a : B.obj i), (κ.app i).hom a = A p.1 p.2 :=
    Concrete.isColimit_exists_rep B hκ.some (A p.1 p.2)
  choose stage entry hentry using reps
  have bound (t : Finset (Fin n × Fin m)) : ∃ i, ∀ p ∈ t, stage p ≤ i := by
    induction t using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary I, by simp⟩
    | @insert p t _ ht =>
      obtain ⟨i, hi⟩ := ht
      obtain ⟨j, hpj, hij⟩ := exists_ge_ge (stage p) i
      refine ⟨j, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hpj
      · exact (hi q hq).trans hij
  obtain ⟨i, hi⟩ := bound Finset.univ
  refine ⟨i, fun a b ↦ (B.map (homOfLE (hi (a, b) (Finset.mem_univ _)))).hom
    (entry (a, b)), ?_⟩
  intro a b
  exact (ConcreteCategory.congr_hom
    (κ.naturality (homOfLE (hi (a, b) (Finset.mem_univ _)))) (entry (a, b))).trans
      (hentry (a, b))

private theorem additive_diagram_isColimit
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : J ⥤ AddCommGrpCat.{v}) (M : Type v) [AddCommGroup M]
    (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
    (hrep : ∀ x : M, ∃ (i : J) (y : D.obj i), (ν.app i).hom y = x)
    (hzero : ∀ (i : J) (x : D.obj i), (ν.app i).hom x = 0 →
      ∃ (j : J) (h : i ≤ j), (D.map (homOfLE h)).hom x = 0) :
    Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) := by
  classical
  have compat (i j : J) (h : i ≤ j) (x : D.obj i) :
      (ν.app j).hom ((D.map (homOfLE h)).hom x) = (ν.app i).hom x := by
    exact ConcreteCategory.congr_hom (ν.naturality (homOfLE h)) x
  have eventual (i j : J) (x : D.obj i) (y : D.obj j)
      (hxy : (ν.app i).hom x = (ν.app j).hom y) :
      ∃ (k : J) (hik : i ≤ k) (hjk : j ≤ k),
        (D.map (homOfLE hik)).hom x = (D.map (homOfLE hjk)).hom y := by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hz : (ν.app k).hom
        ((D.map (homOfLE hik)).hom x - (D.map (homOfLE hjk)).hom y) = 0 := by
      rw [map_sub, compat, compat, hxy, sub_self]
    obtain ⟨l, hkl, hl⟩ := hzero k _ hz
    refine ⟨l, hik.trans hkl, hjk.trans hkl, ?_⟩
    rw [map_sub, sub_eq_zero] at hl
    have c₁ := ConcreteCategory.congr_hom (D.map_comp
      (homOfLE hik) (homOfLE hkl)) x
    have c₂ := ConcreteCategory.congr_hom (D.map_comp
      (homOfLE hjk) (homOfLE hkl)) y
    exact c₁.trans (hl.trans c₂.symm)
  let idx (x : M) : J := (hrep x).choose
  let rep (x : M) : D.obj (idx x) := (hrep x).choose_spec.choose
  have rep_eq (x : M) : (ν.app (idx x)).hom (rep x) = x :=
    (hrep x).choose_spec.choose_spec
  let value (s : Cocone D) (x : M) : s.pt := (s.ι.app (idx x)).hom (rep x)
  have value_rep (s : Cocone D) (i : J) (x : D.obj i) :
      value s ((ν.app i).hom x) = (s.ι.app i).hom x := by
    obtain ⟨k, h₁, h₂, he⟩ := eventual _ i (rep ((ν.app i).hom x)) x (rep_eq _)
    have c₁ := ConcreteCategory.congr_hom (s.w (homOfLE h₁))
      (rep ((ν.app i).hom x))
    have c₂ := ConcreteCategory.congr_hom (s.w (homOfLE h₂)) x
    exact c₁.symm.trans ((congrArg (s.ι.app k).hom he).trans c₂)
  let desc (s : Cocone D) : AddCommGrpCat.of M ⟶ s.pt :=
    AddCommGrpCat.ofHom
      { toFun := value s
        map_zero' := by
          let i : J := Classical.arbitrary J
          have hz := value_rep s i 0
          simpa only [map_zero] using hz
        map_add' := by
          intro x y
          obtain ⟨k, hxk, hyk⟩ := exists_ge_ge (idx x) (idx y)
          let a := (D.map (homOfLE hxk)).hom (rep x)
          let b := (D.map (homOfLE hyk)).hom (rep y)
          have ha : (ν.app k).hom a = x := (compat (idx x) k hxk (rep x)).trans (rep_eq x)
          have hb : (ν.app k).hom b = y := (compat (idx y) k hyk (rep y)).trans (rep_eq y)
          have hab : (ν.app k).hom (a + b) = x + y := by rw [map_add, ha, hb]
          rw [← hab, value_rep, map_add, ← value_rep s k a, ← value_rep s k b, ha, hb] }
  refine ⟨{ desc := desc, fac := ?_, uniq := ?_ }⟩
  · intro s i
    apply AddCommGrpCat.ext
    intro x
    exact value_rep s i x
  · intro s m hm
    apply AddCommGrpCat.ext
    intro x
    have h := ConcreteCategory.congr_hom (hm (idx x)) (rep x)
    change m.hom ((ν.app (idx x)).hom (rep x)) = value s x at h
    change m.hom x = value s x
    simpa only [rep_eq] using h

-- The quotient construction from FinitePresentationModuleBaseChangeDiagram, with
-- the stage universe enlarged to max u v. No finite-type-over-ℤ assumption is needed.
private theorem presentation_diagram
    {J : Type u} [Preorder J]
    (B : J ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const J).obj (CommRingCat.of S))
    (M : Type (max u v)) [AddCommGroup M] [Module S M]
    (n m : ℕ) (f : (Fin n → S) →ₗ[S] M)
    (g : (Fin m → S) →ₗ[S] (Fin n → S))
    (hf : Function.Surjective f) (hexact : Function.Exact g f)
    (i₀ : J) (h₀ : ∀ j : J, i₀ ≤ j)
    (A₀ : Matrix (Fin n) (Fin m) (B.obj i₀))
    (hA : ∀ a b, (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i₀)) (A₀ a b) =
      LinearMap.toMatrix' g a b) :
    ∃ (D : J ⥤ AddCommGrpCat.{max u v})
      (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
      (_ : ∀ j, Module (B.obj j) (D.obj j)),
      (∀ (i j : J) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ j (y : B.obj j) (x : D.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app j)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) ∧
      (∀ j, Module.Finite (B.obj j) (D.obj j)) ∧
      (∀ j, ∃ H₀ : (Fin m → B.obj j) →ₗ[B.obj j] (Fin n → B.obj j),
        Nonempty (((Fin n → B.obj j) ⧸ LinearMap.range H₀) ≃ₗ[B.obj j] D.obj j)) ∧
      (∀ (i j : J) (h : i ≤ j),
        letI := (B.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
          ∀ (y : B.obj j) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      (∀ j,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app j)).toAlgebra
        ∃ e : S ⊗[B.obj j] D.obj j ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj j), e (y ⊗ₜ[B.obj j] x) =
            y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) := by
  classical
  let A (j : J) : Matrix (Fin n) (Fin m) (B.obj j) :=
    fun a b ↦ (B.map (homOfLE (h₀ j))).hom (A₀ a b)
  let Q (j : J) := (Fin n → B.obj j) ⧸ (A j).toLin'.range
  let E (j : J) : Shrink.{max u v} (Q j) ≃ₗ[B.obj j] Q j := Shrink.linearEquiv _ _
  let p (j : J) : (Fin n → B.obj j) →ₗ[B.obj j] Shrink.{max u v} (Q j) :=
    (E j).symm.toLinearMap.comp (A j).toLin'.range.mkQ
  have hp (j : J) : Function.Surjective (p j) :=
    (E j).symm.surjective.comp (Submodule.mkQ_surjective _)
  have htrans {i j : J} (h : i ⟶ j) (a : Fin n) (b : Fin m) :
      (B.map h).hom (A i a b) = A j a b := by
    exact (ConcreteCategory.congr_hom
      (B.map_comp (homOfLE (h₀ i)) h) (A₀ a b)).symm
  let t {i j : J} (h : i ⟶ j) : Q i →ₛₗ[(B.map h).hom] Q j :=
    presentationLift (B.map h).hom (A i) (A j).toLin'.range.mkQ
      (A j).toLin' (quotient_exact (A j)) (by
        intro a b
        exact (htrans h a b).trans
          (congrArg (fun C ↦ C a b) (LinearMap.toMatrix'_toLin' (A j))).symm)
  let d {i j : J} (h : i ⟶ j) : Shrink.{max u v} (Q i) →+ Shrink.{max u v} (Q j) :=
    (E j).symm.toAddMonoidHom.comp ((t h).toAddMonoidHom.comp (E i).toAddMonoidHom)
  have hd {i j : J} (h : i ⟶ j) (x : Fin n → B.obj i) :
      d h (p i x) = p j (coordinates (B.map h).hom n x) := by
    change (E j).symm (t h (E i ((E i).symm ((A i).toLin'.range.mkQ x)))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hds {i j : J} (h : i ⟶ j) (r : B.obj i) (x : Shrink.{max u v} (Q i)) :
      d h (r • x) = (B.map h).hom r • d h x := by
    dsimp [d]
    rw [(E i).map_smul, (t h).map_smulₛₗ, (E j).symm.map_smul]
  let D : J ⥤ AddCommGrpCat.{max u v} :=
    { obj := fun j ↦ AddCommGrpCat.of (Shrink.{max u v} (Q j))
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
        simp [coordinates]
      map_comp := by
        intro i j k h l
        apply AddCommGrpCat.ext
        intro x
        obtain ⟨x, rfl⟩ := hp i x
        change d (h ≫ l) (p i x) = d l (d h (p i x))
        rw [hd, hd, hd]
        congr 1
        ext a
        exact ConcreteCategory.congr_hom (B.map_comp h l) (x a) }
  let κh (j : J) : B.obj j →+* S :=
    @CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app j)
  have hκA (j : J) (a : Fin n) (b : Fin m) :
      (κh j) (A j a b) = LinearMap.toMatrix' g a b := by
    exact (ConcreteCategory.congr_hom (κ.naturality (homOfLE (h₀ j)))
      (A₀ a b)).trans (hA a b)
  let q (j : J) : Q j →ₛₗ[κh j] M :=
    presentationLift (κh j) (A j) f g hexact (hκA j)
  let leg (j : J) : Shrink.{max u v} (Q j) →+ M :=
    (q j).toAddMonoidHom.comp (E j).toAddMonoidHom
  have hleg (j : J) (x : Fin n → B.obj j) :
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
        exact ConcreteCategory.congr_hom (κ.naturality h) (x a) }
  refine ⟨D, ν,
    (fun j ↦ inferInstanceAs (Module (B.obj j) (Shrink.{max u v} (Q j)))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h r x
    exact hds (homOfLE h) r x
  · intro j r x
    change leg j (r • x) = (κh j) r • leg j x
    dsimp [leg]
    rw [(E j).map_smul, (q j).map_smulₛₗ]
  · intro j
    exact inferInstanceAs (Module.Finite (B.obj j) (Shrink.{max u v} (Q j)))
  · intro j
    exact ⟨(A j).toLin', ⟨(E j).symm⟩⟩
  · intro i j h
    let φ : B.obj i →+* B.obj j := (B.map (homOfLE h)).hom
    let : Algebra (B.obj i) (B.obj j) := φ.toAlgebra
    let : Module (B.obj i) (D.obj j) := Module.compHom (D.obj j) φ
    let : IsScalarTower (B.obj i) (B.obj j) (D.obj j) :=
      IsScalarTower.of_algebraMap_smul fun r x ↦ rfl
    let dl : Q i →ₗ[B.obj i] D.obj j :=
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
    let φ : B.obj j →+* S := κh j
    let : Algebra (B.obj j) S := φ.toAlgebra
    let : Module (B.obj j) M := Module.compHom M φ
    let : IsScalarTower (B.obj j) S M :=
      IsScalarTower.of_algebraMap_smul fun r x ↦ rfl
    let ql : Q j →ₗ[B.obj j] M :=
      { toAddHom := (q j).toAddMonoidHom
        map_smul' := by intro r x; exact (q j).map_smulₛₗ r x }
    have hb := presentation_baseChange (A j) f g hf hexact (hκA j) ql (by intro x; rfl)
    have he := IsBaseChange.comp_equiv (E j) ql hb
    exact ⟨he.equiv, fun y x ↦ he.equiv_tmul y x⟩

/-- Presentation-cokernel module data after restricting a descended ring diagram.
Source: Stacks Project, Algebra, Tag 00QX, presentation-matrix paragraph; Tag 00R1.
Proof:
1. Express H using the standard bases as its finite t-by-s matrix. The ring colimit
   represents each entry at some stage of B. Directedness supplies a common stage
   i₁ ≥ i₀ for all entries. For an empty matrix take i₁ = i₀. Restrict B, β, κ and
   τ₀ to the tail above i₁. That tail is cofinal: every old index has a common upper
   bound with i₁. Hence its ring colimit is still T, and both ring-localization
   hypotheses restrict to it. They are hypotheses, not consequences of colimitness.
2. Map the lifted matrix at i₁ into each later ring B₁(i), obtaining Hᵢ. Define
   D(i) as the additive group of the actual quotient B₁(i)^t / range Hᵢ (lifted
   to universe max u v). Ring transitions send matrix columns to matrix columns,
   so entrywise maps descend to semilinear quotient maps. Composition and identity
   follow on representatives. The presentation equivalence at T identifies the
   limit quotient with N and induces δ and ν. Their naturality and scalar formulas
   also follow on representatives. The t standard basis classes generate D(i).
3. Tensoring a cokernel is right exact. Base change carries the finite free modules
   and the lifted matrix to the later free modules and matrices. Thus it identifies
   B₁(j) ⊗[B₁(i)] D(i) with D(j) and T ⊗[B₁(i)] D(i) with N. On pure tensors the
   maps are precisely multiplication by the scalar followed by the quotient map.
4. A vector representing an element of N has finitely many coordinates, so it
   lifts to a common stage. If a stage vector maps to zero in N, it is H applied
   to a finite vector over T. Lift that vector's coordinates to a later stage;
   the finitely many equalities with the original vector hold at a still later
   stage by the eventual-equality criterion for the ring colimit. Consequently
   the quotient class is zero there. For any additive cocone define its map from
   N by a representative. Two choices become equal at a common later stage by
   applying the zero criterion to their difference. This gives a well-defined
   additive map, factoring each leg, and representatives prove uniqueness.
   Therefore the displayed additive cocone has colimit N on the chosen later tail.
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data) -/
theorem exists_limit_module_presentation_cokernel_data
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (N : AddCommGrpCat.{max u v}) [Module T N]
    (s t : ℕ) (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N))
    (i₀ : I) (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
    (β : B ⟶ (Functor.const _).obj T)
    (hβcol : Nonempty (IsColimit (Cocone.mk T β)))
    (hBlocal : ∀ i : {i : I // i₀ ≤ i}, IsLocalRing (B.obj i))
    (hβlocal : ∀ i : {i : I // i₀ ≤ i}, IsLocalHom (β.app i).hom)
    (hBmaplocal : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      IsLocalHom (B.map (homOfLE h)).hom)
    (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T)
    (hκ : ∀ i x, κ i x = (β.app i).hom x)
    (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i)
    (hτlocal : ∀ i, IsLocalHom (τ₀ i))
    (hτfinite : ∀ i, (τ₀ i).EssFiniteType)
    (hτcomp : ∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom)
    (hτnat : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      (B.map (homOfLE h)).hom.comp (τ₀ i) =
        (τ₀ j).comp (F.map (homOfLE h)).hom)
    (hRingTrans : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      letI := (τ₀ i).toAlgebra
      letI := (F.map (homOfLE h)).hom.toAlgebra
      (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
        (∀ (x : B.obj i) (y : F.obj j.1),
          φ (x ⊗ₜ[F.obj i.1] y) =
            (B.map (homOfLE h)).hom x * τ₀ j y) ∧
        (letI := φ.toAlgebra
         ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
           IsLocalization U (B.obj j))))
    (hRingLimit : ∀ i : {i : I // i₀ ≤ i},
      letI := (τ₀ i).toAlgebra
      letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
      (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
        (∀ (x : B.obj i) (y : c.pt),
          φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
        (letI := φ.toAlgebra
         ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T))) :
  ∃ (i₁ : I) (hi : i₀ ≤ i₁),
  let ρ : {i : I // i₁ ≤ i} ⥤ {i : I // i₀ ≤ i} :=
    { obj := fun i ↦ ⟨i.1, hi.trans i.2⟩
      map := fun h ↦ homOfLE (leOfHom h) }
  let B₁ := ρ ⋙ B
  let κ₁ : ∀ i : {i : I // i₁ ≤ i}, B₁.obj i →+* T := fun i ↦ κ (ρ.obj i)
  ∃ (D : {i : I // i₁ ≤ i} ⥤ AddCommGrpCat.{max u v}) (δ : D ⟶ (Functor.const _).obj N),
  Nonempty (IsColimit (Cocone.mk N δ)) ∧
  ∃ (ν : ∀ i : {i : I // i₁ ≤ i}, D.obj i →+ N)
    (_ : ∀ i : {i : I // i₁ ≤ i}, Module (B₁.obj i) (D.obj i)),
    (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
    (∀ i, ∀ (y : B₁.obj i) (x : D.obj i), ν i (y • x) = κ₁ i y • ν i x) ∧
    (∀ (i j : {i : I // i₁ ≤ i}) (h : i ≤ j)
      (y : B₁.obj i) (x : D.obj i),
      (D.map (homOfLE h)).hom (y • x) =
        (B₁.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
    (∀ i, Module.Finite (B₁.obj i) (D.obj i)) ∧
    (∀ i, ∃ H₀ : (Fin s → B₁.obj i) →ₗ[B₁.obj i] (Fin t → B₁.obj i),
      Nonempty (((Fin t → B₁.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B₁.obj i] D.obj i)) ∧
    (∀ (i j : {i : I // i₁ ≤ i}) (h : i ≤ j),
      (letI := (B₁.map (homOfLE h)).hom.toAlgebra
       ∃ e : B₁.obj j ⊗[B₁.obj i] D.obj i ≃ₗ[B₁.obj j] D.obj j,
         ∀ (y : B₁.obj j) (x : D.obj i),
           e (y ⊗ₜ[B₁.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
    (∀ i : {i : I // i₁ ≤ i},
      (letI := (κ₁ i).toAlgebra
       ∃ e : T ⊗[B₁.obj i] D.obj i ≃ₗ[T] N,
         ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B₁.obj i] x) = y • ν i x)) := by
  have _ := hc
  have _ := hF
  have _ := hcLocal
  have _ := hBlocal
  have _ := hβlocal
  have _ := hBmaplocal
  have _ := hτlocal
  have _ := hτfinite
  have _ := hτcomp
  have _ := hτnat
  have _ := hRingTrans
  have _ := hRingLimit
  classical
  let K := {i : I // i₀ ≤ i}
  let : Nonempty K := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected K (· ≤ ·) := ⟨by
    intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  obtain ⟨k, A₀, hA⟩ := matrix_lifts_to_stage B T β hβcol t s (LinearMap.toMatrix' H)
  let J := {i : I // k.val ≤ i}
  let : Nonempty J := ⟨⟨k.val, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨by
    intro i j
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨l, i.property.trans hil⟩, hil, hjl⟩⟩
  let ρ : J ⥤ K :=
    { obj := fun i ↦ ⟨i.1, k.property.trans i.2⟩
      map := fun h ↦ homOfLE (leOfHom h) }
  have hρ : ρ.Final := by
    apply Functor.final_of_exists_of_isFiltered
    · intro i
      obtain ⟨j, hij, hkj⟩ := exists_ge_ge i.val k.val
      exact ⟨⟨j, hkj⟩, ⟨homOfLE hij⟩⟩
    · intro i j a b
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  let B₁ := ρ ⋙ B
  let β₁ : B₁ ⟶ (Functor.const J).obj T := (Cocone.mk T β).whisker ρ |>.ι
  have hβ₁ : Nonempty (IsColimit (Cocone.mk T β₁)) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv ρ _).symm hβcol.some⟩
  let eN := hN.some
  let f : (Fin t → T) →ₗ[T] N := eN.toLinearMap.comp (LinearMap.range H).mkQ
  have hf : Function.Surjective f :=
    eN.surjective.comp (Submodule.mkQ_surjective _)
  have hex : Function.Exact H f := by
    intro x
    change eN ((LinearMap.range H).mkQ x) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      LinearMap.mem_range, Set.mem_range]
  obtain ⟨D, δ, hmod, ht, hδ, hfinite, hpres, hbase, hlimit⟩ :=
    presentation_diagram B₁ T β₁ N t s f H hf hex ⟨k.val, le_rfl⟩
      (fun j ↦ j.property) A₀ hA
  let := hmod
  obtain ⟨hrep, hzero⟩ := Module.baseChange_diagram_elementwise B₁ T β₁ hβ₁ N D δ
    hδ hbase hlimit
  have hcol := additive_diagram_isColimit D N δ hrep hzero
  have hκ₁ (i : J) : κ (ρ.obj i) = (β₁.app i).hom := by
    ext x
    exact hκ (ρ.obj i) x
  refine ⟨k.val, k.property, D, δ, hcol, (fun i ↦ (δ.app i).hom), hmod,
    (by intro i x; rfl), ?_, ht, hfinite, hpres, hbase, ?_⟩
  · intro i y x
    change (@AddCommGrpCat.Hom.hom _ N (δ.app i)) (y • x) =
      κ (ρ.obj i) y • (@AddCommGrpCat.Hom.hom _ N (δ.app i)) x
    rw [hκ₁]
    exact hδ i y x
  · intro i
    change (letI : Algebra (B₁.obj i) T := (κ (ρ.obj i)).toAlgebra
      ∃ e : T ⊗[B₁.obj i] D.obj i ≃ₗ[T] N,
        ∀ (y : T) (x : D.obj i),
          e (y ⊗ₜ[B₁.obj i] x) = y • (@AddCommGrpCat.Hom.hom _ N (δ.app i)) x)
    rw [hκ₁ i]
    exact hlimit i
end RingHom
