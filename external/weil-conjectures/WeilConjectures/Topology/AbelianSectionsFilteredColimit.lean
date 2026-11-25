/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Abelian sections and directed colimits on compact opens

Source: Stacks Project, Cohomology, Lemma 01FF, degree-zero argument;
Sheaves, Lemma 009F(4).
(blueprint: lem-sc-topological-abelian-sections-filtered-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

-- Equality of colimit sections becomes equality at one stage on a neighborhood.
private theorem abelian_colimit_sections_locally_eventually_equal
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [HasColimit D]
    (U : Opens X) (i i' : I) (s : (D.obj i).obj.obj (op U))
    (s' : (D.obj i').obj.obj (op U))
    (h : (colimit.ι D i).1.app (op U) s = (colimit.ι D i').1.app (op U) s')
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (k : I) (hi : i ≤ k) (hi' : i' ≤ k),
      (D.obj k).obj.map (homOfLE hVU).op ((D.map (homOfLE hi)).1.app (op U) s) =
        (D.obj k).obj.map (homOfLE hVU).op ((D.map (homOfLE hi')).1.app (op U) s') := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have he : (S.map (colimit.ι D i)) ((Presheaf.germ (D.obj i).obj) U x hx s) =
      (S.map (colimit.ι D i')) ((Presheaf.germ (D.obj i').obj) U x hx s') := by
    change (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (colimit.ι D i).1
        ((Presheaf.germ (D.obj i).obj) U x hx s) =
      (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (colimit.ι D i').1
        ((Presheaf.germ (D.obj i').obj) U x hx s')
    rw [Presheaf.stalkFunctor_map_germ_apply, Presheaf.stalkFunctor_map_germ_apply]
    exact congrArg ((Presheaf.germ (colimit D).obj) U x hx) h
  obtain ⟨k, f, g, hk⟩ :=
    (Concrete.isColimit_rep_eq_iff_exists (D ⋙ S)
      (isColimitOfPreserves S (colimit.isColimit D)) _ _).mp he
  have hk' : (Presheaf.germ (D.obj k).obj) U x hx ((D.map f).1.app (op U) s) =
      (Presheaf.germ (D.obj k).obj) U x hx ((D.map g).1.app (op U) s') := by
    change (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (D.map f).1
        ((Presheaf.germ (D.obj i).obj) U x hx s) =
      (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (D.map g).1
        ((Presheaf.germ (D.obj i').obj) U x hx s') at hk
    rw [Presheaf.stalkFunctor_map_germ_apply, Presheaf.stalkFunctor_map_germ_apply] at hk
    exact hk
  obtain ⟨V, hxV, a, b, hab⟩ := Presheaf.germ_eq (D.obj k).obj x hx hx _ _ hk'
  exact ⟨V, hxV, a.le, k, f.le, g.le, hab⟩

-- A finite subcover lets us choose one upper bound for the local stages.
private theorem abelian_colimit_sections_eventually_equal
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [HasColimit D]
    (U : Opens X) (hU : IsCompact (U : Set X))
    (i i' : I) (s : (D.obj i).obj.obj (op U))
    (s' : (D.obj i').obj.obj (op U))
    (h : (colimit.ι D i).1.app (op U) s = (colimit.ι D i').1.app (op U) s') :
    ∃ (k : I) (hi : i ≤ k) (hi' : i' ≤ k),
      (D.map (homOfLE hi)).1.app (op U) s =
        (D.map (homOfLE hi')).1.app (op U) s' := by
  classical
  have hlocal := fun x : U ↦
    abelian_colimit_sections_locally_eventually_equal X I D U i i' s s' h x x.property
  choose V hxV hVU k hi hi' he using hlocal
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  obtain ⟨l, hl⟩ := (((t.finite_toSet.image k).insert i).insert i').bddAbove
  have hil : i ≤ l := hl (by simp)
  have hi'l : i' ≤ l := hl (by simp)
  have hkl (x : t) : k x ≤ l := hl (by
    apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    exact ⟨x, x.property, rfl⟩)
  refine ⟨l, hil, hi'l, ?_⟩
  apply (D.obj l).eq_of_locally_eq' (fun x : t ↦ V x) U
    (fun x ↦ homOfLE (hVU x))
  · intro x hx
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨y, hyt⟩, hy⟩
  · intro x
    have e := congrArg ((D.map (homOfLE (hkl x))).1.app (op (V x))) (he x)
    simpa only [← ConcreteCategory.comp_apply, Category.assoc,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality,
      ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      ← Functor.map_comp, homOfLE_comp] using e

/-- Compact-open injectivity, from Stacks 009F(2), using 009E(5).
Equality of images gives equality of germs. Stalks preserve sheaf colimits,
so filtered-colimit equality gives a common stage at each point. Equality
of germs gives a neighborhood of agreement. A finite subcover and a common
upper bound give global equality by sheaf separation. Finally represent
arbitrary colimit elements by sections to prove injectivity of the map.
(blueprint: lem-sc-topological-abelian-sections-filtered-colimit) -/
private theorem abelian_colimit_sections_injective
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [HasColimit D]
    (Ψ : ∀ (U : Opens X),
      colimit (D ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) ⟶
        (colimit D).obj.obj (op U))
    (hΨ : ∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
      Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) i s) =
        (colimit.ι D i).1.app (op U) s) :
    ∀ (U : Opens X), IsCompact (U : Set X) →
      Function.Injective (Ψ U) ∧
      (∀ (i i' : I) (s : (D.obj i).obj.obj (op U))
          (s' : (D.obj i').obj.obj (op U)),
        (colimit.ι D i).1.app (op U) s =
            (colimit.ι D i').1.app (op U) s' →
          ∃ (i'' : I) (hi : i ≤ i'') (hi' : i' ≤ i''),
            (D.map (homOfLE hi)).1.app (op U) s =
              (D.map (homOfLE hi')).1.app (op U) s') := by
  intro U hU
  have he := abelian_colimit_sections_eventually_equal X I D U hU
  refine ⟨?_, he⟩
  intro a b hab
  let E := D ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  obtain ⟨i, s, rfl⟩ := Concrete.colimit_exists_rep E a
  obtain ⟨i', s', rfl⟩ := Concrete.colimit_exists_rep E b
  have hab' : (colimit.ι D i).1.app (op U) s =
      (colimit.ι D i').1.app (op U) s' :=
    (hΨ U i s).symm.trans (hab.trans (hΨ U i' s'))
  obtain ⟨k, hi, hi', hk⟩ := he i i' s s' hab'
  exact (Concrete.colimit_rep_eq_iff_exists E s s').mpr
    ⟨k, homOfLE hi, homOfLE hi', hk⟩

-- Stalks preserve the sheaf colimit, so sections lift at one stage locally.
private theorem abelian_colimit_sections_locally_lift
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [HasColimit D]
    (U : Opens X) (t : (colimit D).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (i : I) (s : (D.obj i).obj.obj (op V)),
      (colimit.ι D i).1.app (op V) s =
        (colimit D).obj.map (homOfLE hVU).op t := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x
  obtain ⟨i, a, ha⟩ := Concrete.isColimit_exists_rep (D ⋙ S)
    (isColimitOfPreserves S (colimit.isColimit D))
    ((Presheaf.germ (colimit D).obj) U x hx t)
  obtain ⟨V, hxV, s, hs⟩ := Presheaf.exists_germ_eq (D.obj i).obj a
  have he : (Presheaf.germ (colimit D).obj) V x hxV
      ((colimit.ι D i).1.app (op V) s) =
      (Presheaf.germ (colimit D).obj) U x hx t := by
    rw [← Presheaf.stalkFunctor_map_germ_apply, hs]
    exact ha
  obtain ⟨W, hxW, f, g, he⟩ :=
    Presheaf.germ_eq (colimit D).obj x hxV hx _ _ he
  refine ⟨W, hxW, g.le, i, (D.obj i).obj.map f.op s, ?_⟩
  rw [NatTrans.naturality_apply]
  exact he

/-- Finite-cover bijectivity, from Stacks 009F(4), using 009E(5).
The finite-refinement hypothesis implies compactness, hence injectivity.
Stalk-colimit representability and equality of germs give local section lifts.
Refine their cover to the finite cover with compact overlaps. On each overlap,
compact-open eventual equality supplies a stage of agreement. Choose an upper
bound for all local stages and overlap stages, then glue in that sheaf. The
image of the glued section equals the original section by sheaf separation.
(blueprint: lem-sc-topological-abelian-sections-filtered-colimit) -/
private theorem abelian_colimit_sections_surjective
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [HasColimit D]
    (Ψ : ∀ (U : Opens X),
      colimit (D ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) ⟶
        (colimit D).obj.obj (op U))
    (hΨ : ∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
      Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) i s) =
        (colimit.ι D i).1.app (op U) s) :
    ∀ (U : Opens X),
      (∀ (K : Type u) (V : K → Opens X),
        (∀ x : X, x ∈ U → ∃ k, x ∈ V k) →
        ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X),
          (∀ x : X, x ∈ U → ∃ j, x ∈ W j) ∧
          (∀ j, ∃ k, W j ≤ V k) ∧
          (∀ j j', IsCompact (((W j ⊓ W j') : Opens X) : Set X))) →
      Function.Bijective (Ψ U) ∧
        (∀ t, ∃ (i : I) (s : (D.obj i).obj.obj (op U)),
          Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) i s) = t) := by
  classical
  intro U hU
  have hcompact : IsCompact (U : Set X) := by
    apply isCompact_of_finite_subcover
    intro K V hV hcover
    obtain ⟨J, hJ, W, hWcover, hWV, _⟩ :=
      hU K (fun k ↦ ⟨V k, hV k⟩) (fun x hx ↦ Set.mem_iUnion.mp (hcover hx))
    choose q hq using hWV
    refine ⟨Finset.univ.image q, ?_⟩
    intro x hx
    obtain ⟨j, hj⟩ := hWcover x hx
    exact Set.mem_iUnion₂.mpr ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩,
      hq j hj⟩
  have hinj := (abelian_colimit_sections_injective X I D Ψ hΨ U hcompact).1
  have hrep : ∀ t : (colimit D).obj.obj (op U),
      ∃ (i : I) (s : (D.obj i).obj.obj (op U)), (colimit.ι D i).1.app (op U) s = t := by
    intro t
    have hlocal := fun x : U ↦ abelian_colimit_sections_locally_lift X I D U t x x.property
    choose V hxV hVU i s hs using hlocal
    obtain ⟨J, hJ, W, hWcover, hWV, hWcompact⟩ :=
      hU U V (fun x hx ↦ ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
    choose q hq using hWV
    let ij : J → I := fun j ↦ i (q j)
    have hWU (j : J) : W j ≤ U := (hq j).trans (hVU (q j))
    let sj (j : J) : (D.obj (ij j)).obj.obj (op (W j)) :=
      (D.obj (ij j)).obj.map (homOfLE (hq j)).op (s (q j))
    have hc (j : J) : (colimit.ι D (ij j)).1.app (op (W j)) (sj j) =
        (colimit D).obj.map (homOfLE (hWU j)).op t := by
      dsimp [sj, ij]
      rw [NatTrans.naturality_apply, hs]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    have hoverlap (j j' : J) :
        (colimit.ι D (ij j)).1.app (op (W j ⊓ W j'))
            ((D.obj (ij j)).obj.map (Opens.infLELeft (W j) (W j')).op (sj j)) =
          (colimit.ι D (ij j')).1.app (op (W j ⊓ W j'))
            ((D.obj (ij j')).obj.map (Opens.infLERight (W j) (W j')).op (sj j')) := by
      rw [NatTrans.naturality_apply (colimit.ι D (ij j)).1
        (Opens.infLELeft (W j) (W j')).op (sj j), hc j,
        NatTrans.naturality_apply (colimit.ι D (ij j')).1
        (Opens.infLERight (W j) (W j')).op (sj j'), hc j']
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    have hevent (j j' : J) := abelian_colimit_sections_eventually_equal X I D
      (W j ⊓ W j') (hWcompact j j') (ij j) (ij j') _ _ (hoverlap j j')
    choose k hik hi'k he using hevent
    obtain ⟨l, hl⟩ := ((Set.finite_range ij).union
      (Set.finite_range (fun p : J × J ↦ k p.1 p.2))).bddAbove
    have hil (j : J) : ij j ≤ l := hl (Or.inl ⟨j, rfl⟩)
    have hkl (j j' : J) : k j j' ≤ l := hl (Or.inr ⟨(j, j'), rfl⟩)
    let sl (j : J) : (D.obj l).obj.obj (op (W j)) :=
      (D.map (homOfLE (hil j))).1.app (op (W j)) (sj j)
    have hcompat : Presheaf.IsCompatible (D.obj l).obj W sl := by
      intro j j'
      have e := congrArg ((D.map (homOfLE (hkl j j'))).1.app (op (W j ⊓ W j')))
        (he j j')
      simpa only [sl, ← ConcreteCategory.comp_apply, Category.assoc,
        ← NatTrans.naturality_assoc, ← NatTrans.naturality,
        ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
        ← Functor.map_comp, homOfLE_comp] using e
    obtain ⟨a, ha, _⟩ := (D.obj l).existsUnique_gluing' W U
      (fun j ↦ homOfLE (hWU j)) (by
        intro x hx
        obtain ⟨j, hj⟩ := hWcover x hx
        exact Opens.mem_iSup.mpr ⟨j, hj⟩) sl hcompat
    refine ⟨l, a, ?_⟩
    apply (colimit D).eq_of_locally_eq' W U (fun j ↦ homOfLE (hWU j)) (by
      intro x hx
      obtain ⟨j, hj⟩ := hWcover x hx
      exact Opens.mem_iSup.mpr ⟨j, hj⟩)
    intro j
    rw [← NatTrans.naturality_apply, ha]
    dsimp [sl]
    have hw := congrArg (fun f ↦ f.1.app (op (W j)) (sj j))
      (colimit.w D (homOfLE (hil j)))
    exact hw.trans (hc j)
  refine ⟨⟨hinj, ?_⟩, ?_⟩
  · intro t
    obtain ⟨i, s, hs⟩ := hrep t
    exact ⟨colimit.ι (D ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) i s, (hΨ U i s).trans hs⟩
  · intro t
    obtain ⟨i, s, hs⟩ := hrep t
    exact ⟨i, s, (hΨ U i s).trans hs⟩


/-- Sections on compact opens preserve directed colimits under the compact-basis and
compact-intersection hypotheses.
Source: Stacks Project, Cohomology, Lemma 01FF, degree-zero argument;
Sheaves, Lemma 009F(4), with Modules, Lemma 01AH.
(blueprint: lem-sc-topological-abelian-sections-filtered-colimit).

Proof: every open covering of a compact open admits a finite refinement by compact
opens: refine pointwise using the basis and then take a finite subcover. Pairwise
intersections are compact by hypothesis. Stalk functors on abelian sheaves preserve
colimits, and the forgetful functor on abelian groups preserves filtered colimits.
Representability and eventual equality in those stalk colimits give local lifts and
local eventual equality of sections. Compactness gives eventual equality on a whole
compact open. On the finite refinement, choose local lifts and one common upper stage
for all lifts and their agreements on compact overlaps, and glue in that sheaf.
The image of the glued section is the original section by separation. Thus the
canonical section comparison is bijective, hence an isomorphism of abelian groups.
This proves preservation of the diagram's colimit; quantify over all diagrams.
Empty opens give the zero group and the empty finite covering; no separation or
compactness of the whole space is required. The private helpers adapt the proof of
`SheavesDirectedColimitSections` to abelian groups using Mathlib's concrete-colimit API. -/
theorem abelianSections_preservesDirectedColimits
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (V : Set X), IsOpen V → ∀ x ∈ V, ∃ W : Set X, IsOpen W ∧
      IsCompact W ∧ x ∈ W ∧ W ⊆ V)
    (hint : ∀ (V W : Set X), IsOpen V → IsOpen W → IsCompact V → IsCompact W →
      IsCompact (V ∩ W))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) := by
  classical
  let X' := TopCat.of X
  let E (V : Opens X) := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  refine ⟨fun {D} ↦ ?_⟩
  suffices IsIso (colimit.post D (E U)) from
    preservesColimit_of_isIso_post (E U) D
  let Ψ (V : Opens X) := colimit.post D (E V)
  have hΨ (V : Opens X) (i : I) (s : (D.obj i).obj.obj (op V)) :
      Ψ V (colimit.ι (D ⋙ E V) i s) = (colimit.ι D i).1.app (op V) s := by
    exact ConcreteCategory.congr_hom (colimit.ι_post D (E V) i) s
  have hfinite (K : Type u) (V : K → Opens X)
      (hcover : ∀ x : X, x ∈ U → ∃ k, x ∈ V k) :
      ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X),
        (∀ x : X, x ∈ U → ∃ j, x ∈ W j) ∧
        (∀ j, ∃ k, W j ≤ V k) ∧
        (∀ j j', IsCompact (((W j ⊓ W j') : Opens X) : Set X)) := by
    choose k hk using hcover
    have href (x : U) := hbas (V (k x x.property)) (V (k x x.property)).isOpen
      x (hk x x.property)
    choose W hWopen hWcompact hxW hWV using href
    obtain ⟨t, ht⟩ := hU.elim_finite_subcover W hWopen (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
    refine ⟨t, inferInstance, fun x ↦ ⟨W x, hWopen x⟩, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact ⟨⟨y, hy⟩, hxy⟩
    · intro x
      exact ⟨k x x.val.property, hWV x⟩
    · intro x y
      exact hint (W x) (W y) (hWopen x) (hWopen y) (hWcompact x) (hWcompact y)
  exact (ConcreteCategory.isIso_iff_bijective (Ψ U)).mpr
    (abelian_colimit_sections_surjective X' I D Ψ hΨ U hfinite).1

end TopCat
