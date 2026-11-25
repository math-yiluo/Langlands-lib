/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Transport of stagewise unitors in a stage system

Let `S` be a stage system with a family of bifunctors `T i` and scalar comparisons `c h`
satisfying the tower equation, together with stagewise units `Un i`, unitors and scalar unit
comparisons `e h : T_h (Un i) ≅ Un j` obeying both unit squares. Then the scalar unit
comparisons satisfy the cocycle equation, and the stagewise unitor representatives of a
common-stage tensor with the unit are compatible with transport. This is the categorical part
of the construction of the common-stage unitors.

Source: Stacks Project, Tag 0FFK (coherence for unit constraints); blueprint coefficient
conventions (blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public section

namespace WeilConjectures

open CategoryTheory

section
variable {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
  (S : StageSystem C) (T : ∀ i, C i × C i ⥤ C i)
  (c : ∀ {i j : I} (h : i ≤ j), T i ⋙ S.T h ≅ (S.T h).prod (S.T h) ⋙ T j)
  (Un : ∀ i, C i) (e : ∀ {i j : I} (h : i ≤ j), (S.T h).obj (Un i) ≅ Un j)

/-- The tower equation of a family of stagewise bifunctor comparisons. -/
def StageTensorTower : Prop :=
  ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X Y : C i),
    (S.T h').map ((c h).hom.app (X, Y)) ≫ (c h').hom.app ((S.T h).obj X, (S.T h).obj Y) ≫
      (T k).map (Prod.mkHom ((S.assoc h h').hom.app X) ((S.assoc h h').hom.app Y)) =
    (S.assoc h h').hom.app ((T i).obj (X, Y)) ≫ (c (h.trans h')).hom.app (X, Y)

private theorem map_mkHom_comp {D : Type*} [Category D] (F : D × D ⥤ D) {A B C' X Y Z : D}
    (f : A ⟶ B) (g : X ⟶ Y) (f' : B ⟶ C') (g' : Y ⟶ Z) :
    F.map (Prod.mkHom f g) ≫ F.map (Prod.mkHom f' g') = F.map (Prod.mkHom (f ≫ f') (g ≫ g')) := by
  rw [← F.map_comp]
  rfl


private theorem map_mkHom_comp_assoc' {D : Type*} [Category D] (F : D × D ⥤ D)
    {A B C' X Y Z W : D}
    (f : A ⟶ B) (g : X ⟶ Y) (f' : B ⟶ C') (g' : Y ⟶ Z) (q : F.obj (C', Z) ⟶ W) :
    F.map (Prod.mkHom f g) ≫ F.map (Prod.mkHom f' g') ≫ q =
      F.map (Prod.mkHom (f ≫ f') (g ≫ g')) ≫ q := by
  rw [← Category.assoc, map_mkHom_comp]

/-- The scalar unit comparisons satisfy the cocycle equation, as a consequence of the right
unit squares, the tower equation and naturality of the unitors. -/
theorem stageUnit_cocycle (tower : StageTensorTower S T c)
    (lu : ∀ i (X : C i), (T i).obj (Un i, X) ≅ X) (ru : ∀ i (X : C i), (T i).obj (X, Un i) ≅ X)
    (hlu : ∀ i {X Y : C i} (f : X ⟶ Y),
      (T i).map (Prod.mkHom (𝟙 (Un i)) f) ≫ (lu i Y).hom = (lu i X).hom ≫ f)
    (hru : ∀ i {X Y : C i} (f : X ⟶ Y),
      (T i).map (Prod.mkHom f (𝟙 (Un i))) ≫ (ru i Y).hom = (ru i X).hom ≫ f)
    (hR : ∀ {i j : I} (h : i ≤ j) (X : C i),
      (c h).hom.app (X, Un i) ≫ (T j).map (Prod.mkHom (𝟙 _) (e h).hom) ≫
        (ru j ((S.T h).obj X)).hom = (S.T h).map (ru i X).hom)
    {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    (S.T h').map (e h).hom ≫ (e h').hom =
      (S.assoc h h').hom.app (Un i) ≫ (e (h.trans h')).hom := by
  let F := S.T h
  let G := S.T h'
  let H := S.T (h.trans h')
  let a := S.assoc h h'
  let φ : H.obj (Un i) ≅ Un k := (a.app (Un i)).symm ≪≫ G.mapIso (e h) ≪≫ e h'
  have key : ∀ X : C i, (c (h.trans h')).hom.app (X, Un i) ≫
      (T k).map (Prod.mkHom (𝟙 _) φ.hom) ≫ (ru k (H.obj X)).hom = H.map (ru i X).hom := by
    intro X
    have n1 : H.map (ru i X).hom =
        a.inv.app _ ≫ G.map (F.map (ru i X).hom) ≫ a.hom.app X := by
      have := a.hom.naturality (ru i X).hom
      dsimp only [Functor.comp_map] at this
      rw [this, Iso.inv_hom_id_app_assoc]
    rw [n1, ← hR h X, G.map_comp, G.map_comp, ← hR h' (F.obj X)]
    rw [← cancel_epi (a.hom.app ((T i).obj (X, Un i))), Iso.hom_inv_id_app_assoc]
    have ht := tower h h' X (Un i)
    have hn : G.map ((T j).map (Prod.mkHom (𝟙 (F.obj X)) (e h).hom)) ≫
        (c h').hom.app (F.obj X, Un j) =
        (c h').hom.app (F.obj X, F.obj (Un i)) ≫
          (T k).map (Prod.mkHom (G.map (𝟙 (F.obj X))) (G.map (e h).hom)) :=
      (c h').hom.naturality (Prod.mkHom (𝟙 (F.obj X)) (e h).hom)
    have hr : (T k).map (Prod.mkHom (a.hom.app X) (𝟙 (Un k))) ≫ (ru k (H.obj X)).hom =
        (ru k (G.obj (F.obj X))).hom ≫ a.hom.app X := hru k (a.hom.app X)
    rw [← reassoc_of% ht]
    simp only [Category.assoc]
    rw [reassoc_of% hn, ← hr]
    simp only [map_mkHom_comp_assoc', Functor.map_id, φ, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, Functor.mapIso_hom, Category.comp_id]
    simp only [a, F, G, H, Category.id_comp, Iso.hom_inv_id_app_assoc]
  have h1 := key (Un i)
  have h2 := hR (h.trans h') (Un i)
  have ht : (T k).map (Prod.mkHom (𝟙 (H.obj (Un i))) φ.hom) =
      (T k).map (Prod.mkHom (𝟙 (H.obj (Un i))) (e (h.trans h')).hom) := by
    rw [← h2] at h1
    exact (cancel_mono (ru k (H.obj (Un i))).hom).mp
      ((cancel_epi ((c (h.trans h')).hom.app (Un i, Un i))).mp h1)
  -- Tensoring on the left by the extended unit is faithful.
  have hφ : φ = e (h.trans h') := by
    have hc := congrArg (fun z ↦ (T k).map (Prod.mkHom φ.inv (𝟙 _)) ≫ z ≫
      (T k).map (Prod.mkHom φ.hom (𝟙 (Un k)))) ht
    simp only [map_mkHom_comp, Category.id_comp, Category.comp_id,
      Iso.inv_hom_id] at hc
    have he := congrArg (fun z ↦ z ≫ (lu k (Un k)).hom) hc
    beta_reduce at he
    rw [hlu, hlu] at he
    exact Iso.ext ((cancel_epi (lu k (H.obj (Un i))).hom).mp he)
  have := congrArg Iso.hom hφ
  simp only [φ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom] at this
  rw [← this, Iso.hom_inv_id_app_assoc]

/-- The stagewise representative of the common-stage left unitor of `(m, y)`, for the unit
represented at the stage `b`, at a stage `L` above the common stage `s`. -/
def stageLeftUnitorRep (lu : ∀ i (X : C i), (T i).obj (Un i, X) ≅ X)
    {b m s : I} (hb : b ≤ s) (hm : m ≤ s) (y : C m) {L : I} (h : s ≤ L) :
    (S.T h).obj ((T s).obj ((S.T hb).obj (Un b), (S.T hm).obj y)) ≅
      (S.T (hm.trans h)).obj y :=
  (c h).app _ ≪≫ (T L).mapIso (Iso.prod ((S.assoc hb h).app (Un b) ≪≫ e (hb.trans h))
    ((S.assoc hm h).app y)) ≪≫ lu L _

/-- The stagewise representative of the common-stage right unitor of `(m, y)`. -/
def stageRightUnitorRep (ru : ∀ i (X : C i), (T i).obj (X, Un i) ≅ X)
    {b m s : I} (hb : b ≤ s) (hm : m ≤ s) (y : C m) {L : I} (h : s ≤ L) :
    (S.T h).obj ((T s).obj ((S.T hm).obj y, (S.T hb).obj (Un b))) ≅
      (S.T (hm.trans h)).obj y :=
  (c h).app _ ≪≫ (T L).mapIso (Iso.prod ((S.assoc hm h).app y)
    ((S.assoc hb h).app (Un b) ≪≫ e (hb.trans h))) ≪≫ ru L _

/-- Transport of the stagewise left unitor representatives. -/
theorem stageLeftUnitorRep_tr (tower : StageTensorTower S T c)
    (lu : ∀ i (X : C i), (T i).obj (Un i, X) ≅ X)
    (hlu : ∀ i {X Y : C i} (f : X ⟶ Y),
      (T i).map (Prod.mkHom (𝟙 (Un i)) f) ≫ (lu i Y).hom = (lu i X).hom ≫ f)
    (hL : ∀ {i j : I} (h : i ≤ j) (X : C i),
      (c h).hom.app (Un i, X) ≫ (T j).map (Prod.mkHom (e h).hom (𝟙 _)) ≫
        (lu j ((S.T h).obj X)).hom = (S.T h).map (lu i X).hom)
    (cocycle : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (S.T h').map (e h).hom ≫ (e h').hom =
        (S.assoc h h').hom.app (Un i) ≫ (e (h.trans h')).hom)
    {b m s : I} (hb : b ≤ s) (hm : m ≤ s) (y : C m) {L L' : I} (h : s ≤ L) (k : L ≤ L') :
    S.tr k (stageLeftUnitorRep S T c Un e lu hb hm y h).hom =
      (stageLeftUnitorRep S T c Un e lu hb hm y (h.trans k)).hom := by
  let G := S.T k
  have h1 : G.map ((S.assoc hb h).hom.app (Un b) ≫ (e (hb.trans h)).hom) ≫ (e k).hom =
      (S.assoc h k).hom.app ((S.T hb).obj (Un b)) ≫
        ((S.assoc hb (h.trans k)).hom.app (Un b) ≫ (e (hb.trans (h.trans k))).hom) := by
    rw [G.map_comp, Category.assoc, cocycle, ← Category.assoc, S.cocycle hb h k (Un b),
      Category.assoc]
  have h2 : G.map ((S.assoc hm h).hom.app y) ≫ (S.assoc (hm.trans h) k).hom.app y =
      (S.assoc h k).hom.app ((S.T hm).obj y) ≫ (S.assoc hm (h.trans k)).hom.app y :=
    S.cocycle hm h k y
  have hn : G.map ((T L).map (Prod.mkHom
      ((S.assoc hb h).hom.app (Un b) ≫ (e (hb.trans h)).hom) ((S.assoc hm h).hom.app y))) ≫
      (c k).hom.app (Un L, (S.T (hm.trans h)).obj y) =
      (c k).hom.app ((S.T h).obj ((S.T hb).obj (Un b)), (S.T h).obj ((S.T hm).obj y)) ≫
        (T L').map (Prod.mkHom
          (G.map ((S.assoc hb h).hom.app (Un b) ≫ (e (hb.trans h)).hom))
          (G.map ((S.assoc hm h).hom.app y))) :=
    (c k).hom.naturality _
  have hl : (lu L' (G.obj ((S.T (hm.trans h)).obj y))).hom ≫
      (S.assoc (hm.trans h) k).hom.app y =
      (T L').map (Prod.mkHom (𝟙 (Un L')) ((S.assoc (hm.trans h) k).hom.app y)) ≫
        (lu L' _).hom := (hlu L' _).symm
  simp only [StageSystem.tr, stageLeftUnitorRep, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.app_hom]
  rw [← cancel_epi ((S.assoc h k).hom.app _), Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% (tower h k ((S.T hb).obj (Un b)) ((S.T hm).obj y))]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← hL k ((S.T (hm.trans h)).obj y)]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  congr 1
  rw [hl]
  simp only [map_mkHom_comp_assoc', Category.id_comp, Category.comp_id]
  rw [h1, h2]

/-- Transport of the stagewise right unitor representatives. -/
theorem stageRightUnitorRep_tr (tower : StageTensorTower S T c)
    (ru : ∀ i (X : C i), (T i).obj (X, Un i) ≅ X)
    (hru : ∀ i {X Y : C i} (f : X ⟶ Y),
      (T i).map (Prod.mkHom f (𝟙 (Un i))) ≫ (ru i Y).hom = (ru i X).hom ≫ f)
    (hR : ∀ {i j : I} (h : i ≤ j) (X : C i),
      (c h).hom.app (X, Un i) ≫ (T j).map (Prod.mkHom (𝟙 _) (e h).hom) ≫
        (ru j ((S.T h).obj X)).hom = (S.T h).map (ru i X).hom)
    (cocycle : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (S.T h').map (e h).hom ≫ (e h').hom =
        (S.assoc h h').hom.app (Un i) ≫ (e (h.trans h')).hom)
    {b m s : I} (hb : b ≤ s) (hm : m ≤ s) (y : C m) {L L' : I} (h : s ≤ L) (k : L ≤ L') :
    S.tr k (stageRightUnitorRep S T c Un e ru hb hm y h).hom =
      (stageRightUnitorRep S T c Un e ru hb hm y (h.trans k)).hom := by
  let G := S.T k
  have h1 : G.map ((S.assoc hb h).hom.app (Un b) ≫ (e (hb.trans h)).hom) ≫ (e k).hom =
      (S.assoc h k).hom.app ((S.T hb).obj (Un b)) ≫
        ((S.assoc hb (h.trans k)).hom.app (Un b) ≫ (e (hb.trans (h.trans k))).hom) := by
    rw [G.map_comp, Category.assoc, cocycle, ← Category.assoc, S.cocycle hb h k (Un b),
      Category.assoc]
  have h2 : G.map ((S.assoc hm h).hom.app y) ≫ (S.assoc (hm.trans h) k).hom.app y =
      (S.assoc h k).hom.app ((S.T hm).obj y) ≫ (S.assoc hm (h.trans k)).hom.app y :=
    S.cocycle hm h k y
  have hn : G.map ((T L).map (Prod.mkHom ((S.assoc hm h).hom.app y)
      ((S.assoc hb h).hom.app (Un b) ≫ (e (hb.trans h)).hom))) ≫
      (c k).hom.app ((S.T (hm.trans h)).obj y, Un L) =
      (c k).hom.app ((S.T h).obj ((S.T hm).obj y), (S.T h).obj ((S.T hb).obj (Un b))) ≫
        (T L').map (Prod.mkHom (G.map ((S.assoc hm h).hom.app y))
          (G.map ((S.assoc hb h).hom.app (Un b) ≫ (e (hb.trans h)).hom))) :=
    (c k).hom.naturality _
  have hl : (ru L' (G.obj ((S.T (hm.trans h)).obj y))).hom ≫
      (S.assoc (hm.trans h) k).hom.app y =
      (T L').map (Prod.mkHom ((S.assoc (hm.trans h) k).hom.app y) (𝟙 (Un L'))) ≫
        (ru L' _).hom := (hru L' _).symm
  simp only [StageSystem.tr, stageRightUnitorRep, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.app_hom]
  rw [← cancel_epi ((S.assoc h k).hom.app _), Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% (tower h k ((S.T hm).obj y) ((S.T hb).obj (Un b)))]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← hR k ((S.T (hm.trans h)).obj y)]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  congr 1
  rw [hl]
  simp only [map_mkHom_comp_assoc', Category.id_comp, Category.comp_id]
  rw [h1, h2]

theorem stageLeftUnitorRep_hom_eq (lu : ∀ i (X : C i), (T i).obj (Un i, X) ≅ X)
    {b m s : I} (hb : b ≤ s) (hm : m ≤ s) (y : C m) {L : I} (h : s ≤ L) :
    (stageLeftUnitorRep S T c Un e lu hb hm y h).hom =
      ((c h).hom.app ((S.T hb).obj (Un b), (S.T hm).obj y) ≫
        (T L).map (Prod.mkHom ((S.assoc hb h).hom.app (Un b)) ((S.assoc hm h).hom.app y))) ≫
      (T L).map (Prod.mkHom (e (hb.trans h)).hom (𝟙 _)) ≫ (lu L _).hom := by
  simp only [stageLeftUnitorRep, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Category.assoc, map_mkHom_comp_assoc', Category.comp_id]

theorem stageRightUnitorRep_hom_eq (ru : ∀ i (X : C i), (T i).obj (X, Un i) ≅ X)
    {b m s : I} (hb : b ≤ s) (hm : m ≤ s) (y : C m) {L : I} (h : s ≤ L) :
    (stageRightUnitorRep S T c Un e ru hb hm y h).hom =
      ((c h).hom.app ((S.T hm).obj y, (S.T hb).obj (Un b)) ≫
        (T L).map (Prod.mkHom ((S.assoc hm h).hom.app y) ((S.assoc hb h).hom.app (Un b)))) ≫
      (T L).map (Prod.mkHom (𝟙 _) (e (hb.trans h)).hom) ≫ (ru L _).hom := by
  simp only [stageRightUnitorRep, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Category.assoc, map_mkHom_comp_assoc', Category.comp_id]

/-- A transport-compatible family of stagewise isomorphisms defines an isomorphism of the pair
category, represented at every stage by the given family. -/
theorem pairCategory_exists_iso_of_tr [IsDirectedOrder I] {A M : S.PairCategory}
    (hm : M.stage ≤ A.stage)
    (rep : ∀ {L : I} (h : A.stage ≤ L), A.toStage h ≅ M.toStage (hm.trans h))
    (htr : ∀ {L L' : I} (h : A.stage ≤ L) (k : L ≤ L'),
      S.tr k (rep h).hom = (rep (h.trans k)).hom) :
    ∃ d : A ≅ M, ∀ (L : I) (h : A.stage ≤ L),
      d.hom = StageSystem.PairCategory.mkHom L h (hm.trans h) (rep h).hom := by
  refine ⟨⟨StageSystem.PairCategory.mkHom A.stage le_rfl hm (rep le_rfl).hom,
    StageSystem.PairCategory.mkHom A.stage hm le_rfl (rep le_rfl).inv, ?_, ?_⟩, ?_⟩
  · rw [StageSystem.PairCategory.mkHom_comp_mkHom, Iso.hom_inv_id,
      ← StageSystem.PairCategory.id_eq_mkHom]
  · rw [StageSystem.PairCategory.mkHom_comp_mkHom, Iso.inv_hom_id,
      ← StageSystem.PairCategory.id_eq_mkHom]
  · intro L h
    change StageSystem.PairCategory.mkHom _ _ _ _ = _
    rw [← StageSystem.PairCategory.mkHom_tr h, htr]

/-- A transport-compatible family of stagewise isomorphisms between two objects of the pair
category, given at every stage above both of their stages, defines an isomorphism of the pair
category represented at every such stage by the given family. -/
theorem pairCategory_exists_iso_of_tr₂ [IsDirectedOrder I] {A B : S.PairCategory}
    (rep : ∀ {L : I} (hA : A.stage ≤ L) (hB : B.stage ≤ L), A.toStage hA ≅ B.toStage hB)
    (htr : ∀ {L L' : I} (hA : A.stage ≤ L) (hB : B.stage ≤ L) (k : L ≤ L'),
      S.tr k (rep hA hB).hom = (rep (hA.trans k) (hB.trans k)).hom) :
    ∃ d : A ≅ B, ∀ (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L),
      d.hom = StageSystem.PairCategory.mkHom L hA hB (rep hA hB).hom := by
  obtain ⟨j, hAj, hBj⟩ := exists_ge_ge A.stage B.stage
  have key : ∀ (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L),
      StageSystem.PairCategory.mkHom j hAj hBj (rep hAj hBj).hom =
        StageSystem.PairCategory.mkHom L hA hB (rep hA hB).hom := by
    intro L hA hB
    obtain ⟨p, hjp, hLp⟩ := exists_ge_ge j L
    rw [← StageSystem.PairCategory.mkHom_tr hjp, ← StageSystem.PairCategory.mkHom_tr hLp,
      htr, htr]
  refine ⟨⟨StageSystem.PairCategory.mkHom j hAj hBj (rep hAj hBj).hom,
    StageSystem.PairCategory.mkHom j hBj hAj (rep hAj hBj).inv, ?_, ?_⟩, ?_⟩
  · rw [StageSystem.PairCategory.mkHom_comp_mkHom, Iso.hom_inv_id,
      ← StageSystem.PairCategory.id_eq_mkHom]
  · rw [StageSystem.PairCategory.mkHom_comp_mkHom, Iso.inv_hom_id,
      ← StageSystem.PairCategory.id_eq_mkHom]
  · intro L hA hB
    exact key L hA hB

/-- The descent endpoint identifying the transition of a stagewise tensor with the tensor of
the transitions. -/
def stageEndpoint {p q s : I} (hp : p ≤ s) (hq : q ≤ s) (x : C p) (y : C q) {L : I}
    (h : s ≤ L) :
    (S.T h).obj ((T s).obj ((S.T hp).obj x, (S.T hq).obj y)) ≅
      (T L).obj ((S.T (hp.trans h)).obj x, (S.T (hq.trans h)).obj y) :=
  (c h).app _ ≪≫ (T L).mapIso (Iso.prod ((S.assoc hp h).app x) ((S.assoc hq h).app y))

/-- Transport of the descent endpoint along a further stage transition. -/
theorem stageEndpoint_transport (tower : StageTensorTower S T c)
    {p q s : I} (hp : p ≤ s) (hq : q ≤ s) (x : C p) (y : C q) {L L' : I}
    (h : s ≤ L) (k : L ≤ L') :
    (S.T k).map (stageEndpoint S T c hp hq x y h).hom ≫
      (c k).hom.app ((S.T (hp.trans h)).obj x, (S.T (hq.trans h)).obj y) ≫
      (T L').map (Prod.mkHom ((S.assoc (hp.trans h) k).hom.app x)
        ((S.assoc (hq.trans h) k).hom.app y)) =
    (S.assoc h k).hom.app _ ≫ (stageEndpoint S T c hp hq x y (h.trans k)).hom := by
  let G := S.T k
  have hn : G.map ((T L).map (Prod.mkHom ((S.assoc hp h).hom.app x)
      ((S.assoc hq h).hom.app y))) ≫
      (c k).hom.app ((S.T (hp.trans h)).obj x, (S.T (hq.trans h)).obj y) =
      (c k).hom.app ((S.T h).obj ((S.T hp).obj x), (S.T h).obj ((S.T hq).obj y)) ≫
        (T L').map (Prod.mkHom (G.map ((S.assoc hp h).hom.app x))
          (G.map ((S.assoc hq h).hom.app y))) :=
    (c k).hom.naturality _
  simp only [stageEndpoint, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, map_mkHom_comp, S.cocycle hp h k x, S.cocycle hq h k y,
    ← map_mkHom_comp, reassoc_of% (tower h k ((S.T hp).obj x) ((S.T hq).obj y))]

/-- The left-nested common-stage tensor identification at a stage `L`. -/
def stageLeftNested {m₁ m₂ m₃ s₁ s₂ : I} (h₁ : m₁ ≤ s₁) (h₂ : m₂ ≤ s₁) (g₁ : s₁ ≤ s₂)
    (g₃ : m₃ ≤ s₂) (x : C m₁) (y : C m₂) (z : C m₃) {L : I} (h : s₂ ≤ L) :
    (S.T h).obj ((T s₂).obj ((S.T g₁).obj ((T s₁).obj ((S.T h₁).obj x, (S.T h₂).obj y)),
      (S.T g₃).obj z)) ≅
      (T L).obj ((T L).obj ((S.T (h₁.trans (g₁.trans h))).obj x,
        (S.T (h₂.trans (g₁.trans h))).obj y), (S.T (g₃.trans h)).obj z) :=
  stageEndpoint S T c g₁ g₃ _ z h ≪≫
    (T L).mapIso (Iso.prod (stageEndpoint S T c h₁ h₂ x y (g₁.trans h)) (Iso.refl _))

/-- The right-nested common-stage tensor identification at a stage `L`. -/
def stageRightNested {m₁ m₂ m₃ t₁ t₂ : I} (f₂ : m₂ ≤ t₁) (f₃ : m₃ ≤ t₁) (f₁ : m₁ ≤ t₂)
    (e₁ : t₁ ≤ t₂) (x : C m₁) (y : C m₂) (z : C m₃) {L : I} (h : t₂ ≤ L) :
    (S.T h).obj ((T t₂).obj ((S.T f₁).obj x,
      (S.T e₁).obj ((T t₁).obj ((S.T f₂).obj y, (S.T f₃).obj z)))) ≅
      (T L).obj ((S.T (f₁.trans h)).obj x, (T L).obj ((S.T (f₂.trans (e₁.trans h))).obj y,
        (S.T (f₃.trans (e₁.trans h))).obj z)) :=
  stageEndpoint S T c f₁ e₁ x _ h ≪≫
    (T L).mapIso (Iso.prod (Iso.refl _) (stageEndpoint S T c f₂ f₃ y z (e₁.trans h)))

theorem stageLeftNested_transport (tower : StageTensorTower S T c)
    {m₁ m₂ m₃ s₁ s₂ : I} (h₁ : m₁ ≤ s₁) (h₂ : m₂ ≤ s₁) (g₁ : s₁ ≤ s₂)
    (g₃ : m₃ ≤ s₂) (x : C m₁) (y : C m₂) (z : C m₃) {L L' : I} (h : s₂ ≤ L) (k : L ≤ L') :
    (S.T k).map (stageLeftNested S T c h₁ h₂ g₁ g₃ x y z h).hom ≫
      (c k).hom.app ((T L).obj ((S.T (h₁.trans (g₁.trans h))).obj x,
        (S.T (h₂.trans (g₁.trans h))).obj y), (S.T (g₃.trans h)).obj z) ≫
      (T L').map (Prod.mkHom ((c k).hom.app ((S.T (h₁.trans (g₁.trans h))).obj x,
        (S.T (h₂.trans (g₁.trans h))).obj y)) (𝟙 _)) ≫
      (T L').map (Prod.mkHom ((T L').map (Prod.mkHom
        ((S.assoc (h₁.trans (g₁.trans h)) k).hom.app x)
        ((S.assoc (h₂.trans (g₁.trans h)) k).hom.app y)))
        ((S.assoc (g₃.trans h) k).hom.app z)) =
    (S.assoc h k).hom.app _ ≫ (stageLeftNested S T c h₁ h₂ g₁ g₃ x y z (h.trans k)).hom := by
  let G := S.T k
  have e₁ := stageEndpoint_transport S T c tower h₁ h₂ x y (g₁.trans h) k
  have e₂ := stageEndpoint_transport S T c tower g₁ g₃ ((T s₁).obj ((S.T h₁).obj x,
    (S.T h₂).obj y)) z h k
  have hn : G.map ((T L).map (Prod.mkHom (stageEndpoint S T c h₁ h₂ x y (g₁.trans h)).hom
      (𝟙 ((S.T (g₃.trans h)).obj z)))) ≫
      (c k).hom.app ((T L).obj ((S.T (h₁.trans (g₁.trans h))).obj x,
        (S.T (h₂.trans (g₁.trans h))).obj y), (S.T (g₃.trans h)).obj z) =
      (c k).hom.app _ ≫ (T L').map (Prod.mkHom
        (G.map (stageEndpoint S T c h₁ h₂ x y (g₁.trans h)).hom)
        (G.map (𝟙 ((S.T (g₃.trans h)).obj z)))) :=
    (c k).hom.naturality _
  simp only [stageLeftNested, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, map_mkHom_comp_assoc', map_mkHom_comp]
  have hc1 := e₁
  rw [← Category.assoc] at hc1
  rw [hc1, Functor.map_id, Category.id_comp, Category.id_comp,
    ← Category.comp_id ((S.assoc (g₃.trans h) k).hom.app z), ← map_mkHom_comp, reassoc_of% e₂]

theorem stageRightNested_transport (tower : StageTensorTower S T c)
    {m₁ m₂ m₃ t₁ t₂ : I} (f₂ : m₂ ≤ t₁) (f₃ : m₃ ≤ t₁) (f₁ : m₁ ≤ t₂)
    (e₁ : t₁ ≤ t₂) (x : C m₁) (y : C m₂) (z : C m₃) {L L' : I} (h : t₂ ≤ L) (k : L ≤ L') :
    (S.T k).map (stageRightNested S T c f₂ f₃ f₁ e₁ x y z h).hom ≫
      (c k).hom.app ((S.T (f₁.trans h)).obj x, (T L).obj ((S.T (f₂.trans (e₁.trans h))).obj y,
        (S.T (f₃.trans (e₁.trans h))).obj z)) ≫
      (T L').map (Prod.mkHom (𝟙 _) ((c k).hom.app ((S.T (f₂.trans (e₁.trans h))).obj y,
        (S.T (f₃.trans (e₁.trans h))).obj z))) ≫
      (T L').map (Prod.mkHom ((S.assoc (f₁.trans h) k).hom.app x)
        ((T L').map (Prod.mkHom
        ((S.assoc (f₂.trans (e₁.trans h)) k).hom.app y)
        ((S.assoc (f₃.trans (e₁.trans h)) k).hom.app z)))) =
    (S.assoc h k).hom.app _ ≫ (stageRightNested S T c f₂ f₃ f₁ e₁ x y z (h.trans k)).hom := by
  let G := S.T k
  have e₁' := stageEndpoint_transport S T c tower f₂ f₃ y z (e₁.trans h) k
  have e₂ := stageEndpoint_transport S T c tower f₁ e₁ x ((T t₁).obj ((S.T f₂).obj y,
    (S.T f₃).obj z)) h k
  have hn : G.map ((T L).map (Prod.mkHom (𝟙 ((S.T (f₁.trans h)).obj x))
      (stageEndpoint S T c f₂ f₃ y z (e₁.trans h)).hom)) ≫
      (c k).hom.app ((S.T (f₁.trans h)).obj x, (T L).obj ((S.T (f₂.trans (e₁.trans h))).obj y,
        (S.T (f₃.trans (e₁.trans h))).obj z)) =
      (c k).hom.app _ ≫ (T L').map (Prod.mkHom
        (G.map (𝟙 ((S.T (f₁.trans h)).obj x)))
        (G.map (stageEndpoint S T c f₂ f₃ y z (e₁.trans h)).hom)) :=
    (c k).hom.naturality _
  simp only [stageRightNested, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, map_mkHom_comp_assoc', map_mkHom_comp]
  have hc1 := e₁'
  rw [← Category.assoc] at hc1
  rw [hc1, Functor.map_id, Category.id_comp, Category.id_comp,
    ← Category.comp_id ((S.assoc (f₁.trans h) k).hom.app x), ← map_mkHom_comp, reassoc_of% e₂]

/-- The stagewise representative of the common-stage associator. -/
def stageAssociatorRep
    (α : ∀ i (X Y Z : C i), (T i).obj ((T i).obj (X, Y), Z) ≅ (T i).obj (X, (T i).obj (Y, Z)))
    {m₁ m₂ m₃ s₁ s₂ t₁ t₂ : I} (h₁ : m₁ ≤ s₁) (h₂ : m₂ ≤ s₁) (g₁ : s₁ ≤ s₂) (g₃ : m₃ ≤ s₂)
    (f₂ : m₂ ≤ t₁) (f₃ : m₃ ≤ t₁) (f₁ : m₁ ≤ t₂) (e₁ : t₁ ≤ t₂)
    (x : C m₁) (y : C m₂) (z : C m₃) {L : I} (hS : s₂ ≤ L) (hT : t₂ ≤ L) :
    (S.T hS).obj ((T s₂).obj ((S.T g₁).obj ((T s₁).obj ((S.T h₁).obj x, (S.T h₂).obj y)),
      (S.T g₃).obj z)) ≅
    (S.T hT).obj ((T t₂).obj ((S.T f₁).obj x,
      (S.T e₁).obj ((T t₁).obj ((S.T f₂).obj y, (S.T f₃).obj z)))) :=
  stageLeftNested S T c h₁ h₂ g₁ g₃ x y z hS ≪≫ α L _ _ _ ≪≫
    (stageRightNested S T c f₂ f₃ f₁ e₁ x y z hT).symm

/-- Transport of the stagewise associator representatives. -/
theorem stageAssociatorRep_tr (tower : StageTensorTower S T c)
    (α : ∀ i (X Y Z : C i), (T i).obj ((T i).obj (X, Y), Z) ≅ (T i).obj (X, (T i).obj (Y, Z)))
    (hα : ∀ i {X X' Y Y' Z Z' : C i} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
      (T i).map (Prod.mkHom ((T i).map (Prod.mkHom f g)) h) ≫ (α i X' Y' Z').hom =
        (α i X Y Z).hom ≫ (T i).map (Prod.mkHom f ((T i).map (Prod.mkHom g h))))
    (hAS : ∀ {i j : I} (h : i ≤ j) (X Y Z : C i),
      (S.T h).map (α i X Y Z).hom ≫ (c h).hom.app (X, (T i).obj (Y, Z)) ≫
        (T j).map (Prod.mkHom (𝟙 _) ((c h).hom.app (Y, Z))) =
      (c h).hom.app ((T i).obj (X, Y), Z) ≫ (T j).map (Prod.mkHom ((c h).hom.app (X, Y)) (𝟙 _)) ≫
        (α j ((S.T h).obj X) ((S.T h).obj Y) ((S.T h).obj Z)).hom)
    {m₁ m₂ m₃ s₁ s₂ t₁ t₂ : I} (h₁ : m₁ ≤ s₁) (h₂ : m₂ ≤ s₁) (g₁ : s₁ ≤ s₂) (g₃ : m₃ ≤ s₂)
    (f₂ : m₂ ≤ t₁) (f₃ : m₃ ≤ t₁) (f₁ : m₁ ≤ t₂) (e₁ : t₁ ≤ t₂)
    (x : C m₁) (y : C m₂) (z : C m₃) {L L' : I} (hS : s₂ ≤ L) (hT : t₂ ≤ L) (k : L ≤ L') :
    S.tr k (stageAssociatorRep S T c α h₁ h₂ g₁ g₃ f₂ f₃ f₁ e₁ x y z hS hT).hom =
      (stageAssociatorRep S T c α h₁ h₂ g₁ g₃ f₂ f₃ f₁ e₁ x y z (hS.trans k)
        (hT.trans k)).hom := by
  let G := S.T k
  have LT := stageLeftNested_transport S T c tower h₁ h₂ g₁ g₃ x y z hS k
  have RT := stageRightNested_transport S T c tower f₂ f₃ f₁ e₁ x y z hT k
  have hA := hAS k ((S.T (h₁.trans (g₁.trans hS))).obj x)
    ((S.T (h₂.trans (g₁.trans hS))).obj y) ((S.T (g₃.trans hS)).obj z)
  have hn : (T L').map (Prod.mkHom ((T L').map (Prod.mkHom
      ((S.assoc (h₁.trans (g₁.trans hS)) k).hom.app x)
      ((S.assoc (h₂.trans (g₁.trans hS)) k).hom.app y))) ((S.assoc (g₃.trans hS) k).hom.app z)) ≫
      (α L' ((S.T ((h₁.trans (g₁.trans hS)).trans k)).obj x)
        ((S.T ((h₂.trans (g₁.trans hS)).trans k)).obj y)
        ((S.T ((g₃.trans hS).trans k)).obj z)).hom =
      (α L' ((S.T k).obj ((S.T (h₁.trans (g₁.trans hS))).obj x))
        ((S.T k).obj ((S.T (h₂.trans (g₁.trans hS))).obj y))
        ((S.T k).obj ((S.T (g₃.trans hS)).obj z))).hom ≫
      (T L').map (Prod.mkHom ((S.assoc (h₁.trans (g₁.trans hS)) k).hom.app x)
        ((T L').map (Prod.mkHom ((S.assoc (h₂.trans (g₁.trans hS)) k).hom.app y)
          ((S.assoc (g₃.trans hS) k).hom.app z)))) := hα L' _ _ _
  simp only [StageSystem.tr, stageAssociatorRep, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [← cancel_epi ((S.assoc hS k).hom.app _), Iso.hom_inv_id_app_assoc]
  rw [← cancel_mono (stageRightNested S T c f₂ f₃ f₁ e₁ x y z (hT.trans k)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← RT, Iso.inv_hom_id_map_assoc,
    reassoc_of% hA, ← hn, reassoc_of% LT]

theorem stageEndpoint_hom_eq {p q s : I} (hp : p ≤ s) (hq : q ≤ s) (x : C p) (y : C q) {L : I}
    (h : s ≤ L) :
    (stageEndpoint S T c hp hq x y h).hom =
      (c h).hom.app ((S.T hp).obj x, (S.T hq).obj y) ≫
        (T L).map (Prod.mkHom ((S.assoc hp h).hom.app x) ((S.assoc hq h).hom.app y)) := rfl

theorem stageLeftNested_hom_eq {m₁ m₂ m₃ s₁ s₂ : I} (h₁ : m₁ ≤ s₁) (h₂ : m₂ ≤ s₁)
    (g₁ : s₁ ≤ s₂) (g₃ : m₃ ≤ s₂) (x : C m₁) (y : C m₂) (z : C m₃) {L : I} (h : s₂ ≤ L) :
    (stageLeftNested S T c h₁ h₂ g₁ g₃ x y z h).hom =
      (stageEndpoint S T c g₁ g₃ _ z h).hom ≫
        (T L).map (Prod.mkHom (stageEndpoint S T c h₁ h₂ x y (g₁.trans h)).hom (𝟙 _)) := rfl

theorem stageRightNested_hom_eq {m₁ m₂ m₃ t₁ t₂ : I} (f₂ : m₂ ≤ t₁) (f₃ : m₃ ≤ t₁)
    (f₁ : m₁ ≤ t₂) (e₁ : t₁ ≤ t₂) (x : C m₁) (y : C m₂) (z : C m₃) {L : I} (h : t₂ ≤ L) :
    (stageRightNested S T c f₂ f₃ f₁ e₁ x y z h).hom =
      (stageEndpoint S T c f₁ e₁ x _ h).hom ≫
        (T L).map (Prod.mkHom (𝟙 _) (stageEndpoint S T c f₂ f₃ y z (e₁.trans h)).hom) := rfl

end

end WeilConjectures
