/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Data.Finset.Order
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Finite relation factorization for an elementwise ring colimit

Source: Stacks Project, Tags 00HK and 00R6, equational flatness and finite-data descent.
(blueprint: lem-weil-pbc-colimit-flat-relation-descent-elementwise)
-/

@[expose] public section

universe u v w z t
open CategoryTheory CategoryTheory.Limits
namespace RingTheory

private theorem additive_colimit_eventual_eq
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit N]
    (i : Λ) (x y : N.obj i)
    (h : (colimit.ι N i).hom x = (colimit.ι N i).hom y) :
    ∃ (j : Λ) (f : i ⟶ j), (N.map f).hom x = (N.map f).hom y := by
  let U := AddCommGrpCat.uliftFunctor.{u, z}
  let : IsFiltered Λ := inferInstance
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max u z}) := preservesFilteredColimitsOfSize_shrink _
  have hc := isColimitOfPreserves U (colimit.isColimit N)
  have he : (U.mapCocone (colimit.cocone N)).ι.app i (ULift.up x) =
      (U.mapCocone (colimit.cocone N)).ι.app i (ULift.up y) := congrArg ULift.up h
  obtain ⟨j, f, g, hj⟩ :=
    Concrete.isColimit_exists_of_rep_eq (N ⋙ U) hc (ULift.up x) (ULift.up y) he
  have hfg : f = g := Subsingleton.elim _ _
  subst g
  exact ⟨j, f, congrArg ULift.down hj⟩


/-- A relation becomes trivial at a later stage when the ring colimit is elementwise.
The explicit preservation assumption ensures that ring colimit representatives and
zero relations descend even when the indexing and ring universes are independent.
Source: Stacks Project, Tags 00HK and 00R6.
(blueprint: lem-weil-pbc-colimit-flat-relation-descent-elementwise)

Proof: Map the given relation to N_infty. The compatibility of psi with phi
and of the module coprojections with the scalar actions gives a relation
with coefficients a_i(a_p) in A_infty. Flatness and the equational criterion
00HK give finitely many coefficients c_pq in A_infty and elements y_q in
N_infty, with n_i(x_p)=sum_q c_pq*y_q and sum_p a_i(a_p)*c_pq=0.
Represent the finitely many coefficients and module elements at stages of the
ring and additive-group colimits, and move all representatives to one stage
above i by directedness. Scalar compatibility identifies the images of the
stage expressions with these expressions in N_infty. Eventual zero in the
ring colimit makes all column relations zero at a common later stage, and
eventual equality in the additive-group colimit makes all row expressions
equal there. Move both sets of equations to a further common stage; ring
maps, additive maps and scalar compatibility preserve them. These descended
coefficients and vectors give the stated factorization. Empty row or column
sets are allowed, with empty sums equal to zero. No tensor-colimit or finite
presentation theorem, nor Noetherian or local hypothesis, is needed.
(blueprint: lem-weil-pbc-colimit-flat-relation-descent)
-/
theorem exists_stage_flat_relation_factorization_of_preserves
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z}))
    (i : Λ) {ι : Type t} [Fintype ι] (a : ι → A.obj i) (x : ι → N.obj i)
    (hx : ∑ p, (φ i) (a p) • x p = 0) :
    ∃ (j : Λ) (f : i ⟶ j) (m : ℕ)
      (c : ι → Fin m → A.obj j) (y : Fin m → N.obj j),
      (∀ p, (N.map f).hom (x p) = ∑ q, (φ j) (c p q) • y q) ∧
      (∀ q, ∑ p, (A.map f).hom (a p) * c p q = 0) := by
  let := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
  have hxa : ∑ p, (colimit.ι A i).hom (a p) • (colimit.ι N i).hom (x p) = 0 := by
    have he (p : ι) : ψ ((colimit.ι A i).hom (a p)) =
        (colimit.ι B i).hom ((φ i) (a p)) :=
      DFunLike.congr_fun (hψ i) (a p)
    have hz := congrArg (colimit.ι N i).hom hx
    rw [map_sum, map_zero] at hz
    change ∑ p, ψ ((colimit.ι A i).hom (a p)) •
      (colimit.ι N i).hom (x p) = 0
    simpa only [hlimitScalar, he] using hz
  let : Module.Flat (colimit A : CommRingCat.{v})
      (colimit N : AddCommGrpCat.{z}) := hflat
  obtain ⟨m, c, y, hc, hcy⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hxa
  classical
  choose kc cc hcc using fun pq : ι × Fin m ↦ Concrete.colimit_exists_rep A (c pq.1 pq.2)
  have group_rep (y : (colimit N : AddCommGrpCat.{z})) :
      ∃ (j : Λ) (x : N.obj j), (colimit.ι N j).hom x = y := by
    let U := AddCommGrpCat.uliftFunctor.{u, z}
    let : IsFiltered Λ := inferInstance
    let : PreservesFilteredColimitsOfSize.{u, u}
        (forget AddCommGrpCat.{max u z}) := preservesFilteredColimitsOfSize_shrink _
    have hc := isColimitOfPreserves U (colimit.isColimit N)
    obtain ⟨j, x, hx⟩ := Concrete.isColimit_exists_rep (N ⋙ U) hc (ULift.up y)
    exact ⟨j, x.down, congrArg ULift.down hx⟩
  choose ky yy hyy using fun q : Fin m ↦ group_rep (y q)
  obtain ⟨j, hj⟩ :=
    (insert i ((Finset.univ.image kc) ∪ (Finset.univ.image ky))).exists_le
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have hkc (pq : ι × Fin m) : kc pq ≤ j := hj (kc pq)
    (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ pq))))
  have hky (q : Fin m) : ky q ≤ j := hj (ky q)
    (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ q))))
  let f : i ⟶ j := homOfLE hij
  let c₀ (p : ι) (q : Fin m) : A.obj j := (A.map (homOfLE (hkc (p, q)))).hom (cc (p, q))
  let y₀ (q : Fin m) : N.obj j := (N.map (homOfLE (hky q))).hom (yy q)
  have hc₀ (p : ι) (q : Fin m) : (colimit.ι A j).hom (c₀ p q) = c p q :=
    (ConcreteCategory.congr_hom (colimit.w A (homOfLE (hkc (p, q)))) _).trans (hcc (p, q))
  have hy₀ (q : Fin m) : (colimit.ι N j).hom (y₀ q) = y q :=
    (ConcreteCategory.congr_hom (colimit.w N (homOfLE (hky q))) _).trans (hyy q)
  have hxj (p : ι) : (colimit.ι N i).hom (x p) =
      (colimit.ι N j).hom (∑ q, (φ j) (c₀ p q) • y₀ q) := by
    rw [map_sum]
    have hψj (r : A.obj j) : (colimit.ι B j).hom ((φ j) r) =
        ψ ((colimit.ι A j).hom r) := (DFunLike.congr_fun (hψ j) r).symm
    simp only [hlimitScalar, hψj, hc₀, hy₀]
    exact hc p
  have hcol (q : Fin m) : (colimit.ι A j).hom
      (∑ p, (A.map f).hom (a p) * c₀ p q) = 0 := by
    rw [map_sum]
    simp only [map_mul, hc₀]
    have ha (p : ι) : (colimit.ι A j).hom ((A.map f).hom (a p)) =
        (colimit.ι A i).hom (a p) := ConcreteCategory.congr_hom (colimit.w A f) _
    simpa only [ha] using hcy q
  have col_zero (q : Fin m) : ∃ (k : Λ) (g : j ⟶ k),
      (A.map g).hom (∑ p, (A.map f).hom (a p) * c₀ p q) = 0 := by
    have hz : (colimit.ι A j).hom (∑ p, (A.map f).hom (a p) * c₀ p q) =
        (colimit.ι A j).hom 0 := (hcol q).trans (map_zero _).symm
    obtain ⟨k, g, h, he⟩ := Concrete.colimit_exists_of_rep_eq A _ _ hz
    exact ⟨k, g, he.trans (map_zero _)⟩
  choose kr gr hgr using col_zero
  have he (p : ι) : ∃ (k : Λ) (g : j ⟶ k),
      (N.map g).hom ((N.map f).hom (x p)) =
        (N.map g).hom (∑ q, (φ j) (c₀ p q) • y₀ q) := by
    apply additive_colimit_eventual_eq N j
    exact (ConcreteCategory.congr_hom (colimit.w N f) (x p)).trans (hxj p)
  choose k g hg using he
  obtain ⟨l, hl⟩ := (insert j ((Finset.univ.image k) ∪ (Finset.univ.image kr))).exists_le
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  have hkl (p : ι) : k p ≤ l := hl (k p)
    (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ p))))
  have hkrl (q : Fin m) : kr q ≤ l := hl (kr q)
    (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ q))))
  let e : j ⟶ l := homOfLE hjl
  refine ⟨l, f ≫ e, m, fun p q ↦ (A.map e).hom (c₀ p q),
    fun q ↦ (N.map e).hom (y₀ q), ?_, ?_⟩
  · intro p
    have hmap : (N.map e).hom ((N.map f).hom (x p)) =
        (N.map e).hom (∑ q, (φ j) (c₀ p q) • y₀ q) := by
      have h := congrArg (N.map (homOfLE (hkl p))).hom (hg p)
      have heq : (f ≫ g p) ≫ homOfLE (hkl p) = f ≫ e := Subsingleton.elim _ _
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, heq,
        Subsingleton.elim (g p ≫ homOfLE (hkl p)) e] using h
    rw [Functor.map_comp]
    change (N.map e).hom ((N.map f).hom (x p)) = _
    rw [hmap, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hscalar]
    exact congrArg (fun b ↦ b • (N.map e).hom (y₀ q))
      (DFunLike.congr_fun (hcomm j l e) (c₀ p q))
  · intro q
    have h : (A.map e).hom (∑ p, (A.map f).hom (a p) * c₀ p q) = 0 := by
      have hh := congrArg (A.map (homOfLE (hkrl q))).hom (hgr q)
      have heq : gr q ≫ homOfLE (hkrl q) = e := Subsingleton.elim _ _
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, heq,
        map_zero] using hh
    rw [map_sum] at h
    simpa only [map_mul, Functor.map_comp, CommRingCat.hom_comp,
      RingHom.comp_apply] using h

end RingTheory
