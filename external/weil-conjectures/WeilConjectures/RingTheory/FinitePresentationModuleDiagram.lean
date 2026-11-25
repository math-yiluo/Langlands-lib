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
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.RingTheory.FinitePresentationModuleBaseChangeDiagram
import WeilConjectures.RingTheory.BaseChangeDiagramElementwise

/-! # Descent of a finite presentation along a directed ring diagram
Source: Stacks Project, Algebra, Tags 00QX and 00R1, the presentation-matrix construction.
(blueprint: lem-weil-pbc-finite-presentation-module-diagram).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

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

/-- Descend a finite presentation to a cofinal directed restriction of a given ring diagram.
The finite-type assumption permits the stage modules to live in any universe `v`.

Source: Stacks Project, Algebra, Tag 00QX, presentation-matrix paragraph, in its
non-local form used in Tag 00R1.
(blueprint: lem-weil-pbc-finite-presentation-module-diagram)

Proof:
1. Choose a finite free presentation of M. Represent each matrix entry in a stage
   of B using the elementwise ring-colimit theorem, and take a common upper bound i₀.
   Empty matrices cause no problem: choose any index, using nonemptiness.
2. Let J be the upper tail above i₀, and F its inclusion. This tail is nonempty and
   directed. Every original index admits a map to an index in J, so the fully faithful
   inclusion F is final. Restriction therefore preserves the ring colimit.
3. For j in J form the quotient of the finite free B(Fj)-module by the image of the
   lifted presentation matrix. Entrywise ring maps descend to additive quotient maps;
   they respect scalar actions. Functoriality and cocone naturality hold on quotient
   representatives. The classes of the standard basis finitely generate each quotient.
   A finite-type integer algebra is countable; so are its finite powers and quotients.
   Transport each quotient to a small model in Type v, and transport all maps and actions.
4. Tensor right exactness and the finite-product tensor equivalence identify base
   change of these quotients with the corresponding later quotient and with M.
   The equivalences send y tensor x to y times the induced image of x.
5. Apply directedColimitBaseChangeElementwise at i₀ and transport its representative
   and eventual-zero criteria along the equivalences in step 4 and the ring-colimit
   comparison with S. Thus every element of M comes from a stage; two representatives
   with equal images become equal at a common later stage, by applying eventual zero
   to their difference after moving to a common stage. For any additive cocone to X,
   define M → X by the value of a representative. Eventual equality makes this
   independent of the representative. Move two representatives to a common stage to
   prove additivity. It factors every cocone leg, and representatives prove uniqueness.
   This constructs IsColimit directly, even when the index universe u exceeds v;
   it does not require a small-index filtered-colimit instance for AddCommGrpCat.{v}.
   All transports use actual quotient constructions, not arbitrary witnesses of an
   unproved existence theorem.
-/
theorem exists_finitePresentation_module_diagram
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hκ : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)))
    (hfinite : ∀ i, Algebra.FiniteType ℤ (B.obj i))
    (M : Type v) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (F : J ⥤ I) (_ : F.Final)
      (D : J ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
      (_ : ∀ j, Module (B.obj (F.obj j)) (D.obj j)),
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
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
  obtain ⟨n, m, f, g, hsurj, hexact⟩ := FinitePresentation.exists_fin' S M
  obtain ⟨i₀, A₀, hA⟩ := matrix_lifts_to_stage B S κ hκ n m (LinearMap.toMatrix' g)
  obtain ⟨J, hJ, hne, hdir, F, hF, D, ν, hmod, ht, hν, hf, hb, hS⟩ :=
    exists_finitePresentation_baseChange_diagram B S κ hfinite M n m f g
      hsurj hexact i₀ A₀ hA
  let := hJ
  let := hne
  let := hdir
  let := hF
  let := hmod
  let κ' : F ⋙ B ⟶ (Functor.const J).obj (CommRingCat.of S) :=
    (Cocone.mk (CommRingCat.of S) κ).whisker F |>.ι
  have hκ' : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ')) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm hκ.some⟩
  let : ∀ j, Module ((F ⋙ B).obj j) (D.obj j) := hmod
  obtain ⟨hrep, hzero⟩ := baseChange_diagram_elementwise (F ⋙ B) S κ' hκ' M D ν
    hν hb hS
  exact ⟨J, hJ, hne, hdir, F, hF, D, ν, hmod,
    additive_diagram_isColimit D M ν hrep hzero, ht, hν, hf, hb, hS⟩

end Module
