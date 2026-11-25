/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-! # Descending stagewise isomorphisms to the pair category

Source: blueprint dual-Tate compatibility, Step 5, coefficient-stage descent
(blueprint: lem-pod-reindexing-hom-coefficient-descent).

A family of stagewise isomorphisms between the representatives of two functors into
the pair category of a stage system descends to a unique natural isomorphism, provided
the family is compatible with transport to larger stages and with representatives of
the image arrows.
-/

@[expose] public section
set_option autoImplicit false

universe w u v u' v'
open CategoryTheory

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] {S : StageSystem C} {D : Type u'} [Category.{v'} D]

/-- A transport-compatible family of stagewise isomorphisms represents one class.
Source: blueprint common-stage descent
(blueprint: lem-pod-reindexing-hom-coefficient-descent). -/
theorem mkHom_eq_of_tr {X Y : S.PairCategory} (s : I) (hX : X.stage ≤ s) (hY : Y.stage ≤ s)
    (d : ∀ (L : I) (h : s ≤ L), X.toStage (hX.trans h) ⟶ Y.toStage (hY.trans h))
    (htr : ∀ (L : I) (h : s ≤ L) (M : I) (k : L ≤ M), S.tr k (d L h) = d M (h.trans k))
    (L : I) (h : s ≤ L) :
    PairCategory.mkHom L (hX.trans h) (hY.trans h) (d L h) =
      PairCategory.mkHom s (hX.trans le_rfl) (hY.trans le_rfl) (d s le_rfl) := by
  rw [← PairCategory.mkHom_tr h (d s le_rfl), htr s le_rfl L h]

/-- Stagewise isomorphisms, compatible with transport and with representatives of
the image arrows, descend to a unique natural isomorphism of pair-category functors.
Source: blueprint common-stage descent
(blueprint: lem-pod-reindexing-hom-coefficient-descent).
Proof: the class of the representative is independent of the stage by transport
compatibility. Its inverse class is represented by the inverse isomorphisms.
Naturality is checked at a common stage of a representative of the image arrows.
Every component is prescribed, which gives uniqueness. -/
theorem natIso_existsUnique_of_stage (A B : D ⥤ S.PairCategory) (s : D → I)
    (hA : ∀ P, (A.obj P).stage ≤ s P) (hB : ∀ P, (B.obj P).stage ≤ s P)
    (d : ∀ (P : D) (L : I) (h : s P ≤ L),
      (A.obj P).toStage ((hA P).trans h) ≅ (B.obj P).toStage ((hB P).trans h))
    (htr : ∀ (P : D) (L : I) (h : s P ≤ L) (M : I) (k : L ≤ M),
      S.tr k (d P L h).hom = (d P M (h.trans k)).hom)
    (hnat : ∀ (P Q : D) (f : P ⟶ Q), ∃ (L : I) (hP : s P ≤ L) (hQ : s Q ≤ L)
      (a : (A.obj P).toStage ((hA P).trans hP) ⟶ (A.obj Q).toStage ((hA Q).trans hQ))
      (b : (B.obj P).toStage ((hB P).trans hP) ⟶ (B.obj Q).toStage ((hB Q).trans hQ)),
      A.map f = PairCategory.mkHom L _ _ a ∧ B.map f = PairCategory.mkHom L _ _ b ∧
        a ≫ (d Q L hQ).hom = (d P L hP).hom ≫ b) :
    ∃! α : A ≅ B, ∀ (P : D) (L : I) (h : s P ≤ L),
      α.hom.app P = PairCategory.mkHom L _ _ (d P L h).hom := by
  have key (P : D) (L : I) (h : s P ≤ L) :
      PairCategory.mkHom L _ _ (d P L h).hom =
        PairCategory.mkHom (s P) _ _ (d P (s P) le_rfl).hom :=
    mkHom_eq_of_tr (s P) (hA P) (hB P) (fun L h ↦ (d P L h).hom) (htr P) L h
  let e (P : D) : A.obj P ≅ B.obj P :=
    { hom := PairCategory.mkHom (s P) _ _ (d P (s P) le_rfl).hom
      inv := PairCategory.mkHom (s P) _ _ (d P (s P) le_rfl).inv
      hom_inv_id := by
        rw [PairCategory.mkHom_comp_mkHom, Iso.hom_inv_id,
          ← PairCategory.id_eq_mkHom]
      inv_hom_id := by
        rw [PairCategory.mkHom_comp_mkHom, Iso.inv_hom_id,
          ← PairCategory.id_eq_mkHom] }
  let α : A ≅ B := NatIso.ofComponents e (by
    intro P Q f
    obtain ⟨L, hP, hQ, a, b, ha, hb, hab⟩ := hnat P Q f
    change A.map f ≫ PairCategory.mkHom (s Q) _ _ (d Q (s Q) le_rfl).hom =
      PairCategory.mkHom (s P) _ _ (d P (s P) le_rfl).hom ≫ B.map f
    rw [← key Q L hQ, ← key P L hP, ha, hb, PairCategory.mkHom_comp_mkHom,
      PairCategory.mkHom_comp_mkHom, hab])
  refine ⟨α, fun P L h ↦ (key P L h).symm, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext P
  exact (hβ P (s P) le_rfl).trans (key P (s P) le_rfl)

end CategoryTheory.StageSystem
