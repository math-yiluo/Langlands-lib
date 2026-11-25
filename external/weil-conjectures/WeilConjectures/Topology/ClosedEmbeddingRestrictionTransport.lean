/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import WeilConjectures.Topology.EmbeddingPushforwardTransport
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-!
# Comparison of restriction units under a change of topological universe

Source: Stacks Project, Tag 09ZG, closed-image and universe-transport step.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

/-- Restriction along an embedding is conjugate to restriction to its image after
transport by a homeomorphism, even when the ambient spaces have different universes.
No spectrality, closedness, or connectedness is required for this comparison.

Source: Stacks Project, Tag 09ZG, closed-image and universe-transport step;
Mathlib `CategoryTheory.unit_mateEquiv_symm` supplies the unit comparison.
(blueprint: lem-weil-pbc-closed-embedding-restriction-transport-square)

Proof:
1. The homeomorphism `e` gives an order isomorphism of open sets. Precompose `G`
   with its functor on opposite open sets to obtain `F`. A homeomorphism preserves
   open covers and their pullbacks, so matching families and their unique gluings
   correspond, and `F` is a sheaf. At the top open this gives the equivalence `a`.
2. Since `i` is an embedding, its range with the subspace topology is homeomorphic
   to its domain. Combining this homeomorphism with the restriction of `e` gives
   a homeomorphism between `Z` and `D`. Precomposition on opens identifies the two
   pushforward functors under these sheaf equivalences.
3. Take the mate of the pushforward comparison under the inverse-image
   adjunctions. It is invertible because the vertical sheaf functors are
   equivalences, by `isIso_inverseMate_of_equivalences`. The equation `unit_mateEquiv_symm`
   relates the two units. Compose the global-sections transport, the pushforward
   comparison, and the inverse mate to obtain `b`. Naturality of the
   global-sections transport and the unit equation give the displayed square.
   This includes empty spaces and empty images; no choice of a point is used. -/
theorem closed_embedding_restriction_transport_square
    {X Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsEmbedding i)
    (Y : TopCat.{u + 1}) (e : Y ≃ₜ X) :
    letI : ∀ P : (Opens X)ᵒᵖ ⥤ Type (u + 1),
        (Opens.map i).op.HasPointwiseLeftKanExtension P :=
      fun P U ↦ @Types.hasColimit.{u, u + 1, u}
        (CostructuredArrow.{u, u, u, u} (Opens.map i).op U)
        inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
    let A := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map i) (Type (u + 1))
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
    let D : Set Y := e ⁻¹' Set.range i
    let j : TopCat.of D ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let B := Sheaf.pullbackPushforwardAdjunction (Type (u + 1)) j
    ∀ G : X.Sheaf (Type (u + 1)),
      ∃ (F : Y.Sheaf (Type (u + 1)))
        (a : G.1.obj (op ⊤) ≃ F.1.obj (op ⊤))
        (b : ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map i)
          (Type (u + 1)) (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Z)).obj G).1.obj (op ((Opens.map i).obj ⊤)) ≃
          ((Sheaf.pullback (Type (u + 1)) j).obj F).1.obj (op ((Opens.map j).obj ⊤))),
        ∀ s, b ((A.unit.app G).hom.app (op ⊤) s) =
          (B.unit.app F).hom.app (op ⊤) (a s) := by
  let : ∀ P : (Opens X)ᵒᵖ ⥤ Type (u + 1),
      (Opens.map i).op.HasPointwiseLeftKanExtension P :=
    fun P U ↦ @Types.hasColimit.{u, u + 1, u}
      (CostructuredArrow.{u, u, u, u} (Opens.map i).op U)
      inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
  dsimp only
  intro G
  let L := Functor.sheafPullbackConstruction.sheafPullback
    (Opens.map i) (Type (u + 1))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let R := (Opens.map i).sheafPushforwardContinuous (Type (u + 1))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let A := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map i) (Type (u + 1))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let D : Set Y := e ⁻¹' Set.range i
  let j : TopCat.of D ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let B := Sheaf.pullbackPushforwardAdjunction (Type (u + 1)) j
  obtain ⟨T, S, ⟨a⟩, ⟨r⟩⟩ := embedding_pushforward_transport i hi Y e
  let α := (mateEquiv A B).symm
    (TwoSquare.mk _ S.functor T.functor _ r.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences A B r
  let qY := sheafToPresheaf (Opens.grothendieckTopology Y) (Type (u + 1)) ⋙
    (evaluation (Opens Y)ᵒᵖ (Type (u + 1))).obj (op ⊤)
  let b := (a.app (R.obj (L.obj G))) ≪≫
    qY.mapIso (r.app (L.obj G)) ≪≫
    qY.mapIso ((Sheaf.pushforward (Type (u + 1)) j).mapIso (asIso (α.app G))).symm
  refine ⟨T.functor.obj G, ?_, ?_, ?_⟩
  · exact Iso.toEquiv (a.app G)
  · exact Iso.toEquiv b
  · intro s
    have hunit := unit_mateEquiv_symm A B
      (TwoSquare.mk _ S.functor T.functor _ r.hom) G
    change T.functor.map (A.unit.app G) ≫ (r.app (L.obj G)).hom =
      B.unit.app (T.functor.obj G) ≫
        (Sheaf.pushforward (Type (u + 1)) j).map (α.app G) at hunit
    have ha := a.hom.naturality (A.unit.app G)
    have hsquare :
        (A.unit.app G).hom.app (op ⊤) ≫ b.hom =
          (a.app G).hom ≫ (B.unit.app (T.functor.obj G)).hom.app (op ⊤) := by
      dsimp only [b, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
      change (A.unit.app G).hom.app (op ⊤) ≫ (a.app (R.obj (L.obj G))).hom =
        (a.app G).hom ≫ qY.map (T.functor.map (A.unit.app G)) at ha
      rw [← Category.assoc, ha]
      simp only [Functor.mapIso_inv, asIso_inv]
      rw [Category.assoc, ← Category.assoc (qY.map (T.functor.map (A.unit.app G))),
        ← qY.map_comp, hunit, qY.map_comp, Category.assoc]
      have hcancel :
          qY.map ((Sheaf.pushforward (Type (u + 1)) j).map (α.app G)) ≫
            qY.map ((Sheaf.pushforward (Type (u + 1)) j).map (inv (α.app G))) = 𝟙 _ := by
        rw [← qY.map_comp, ← Functor.map_comp, IsIso.hom_inv_id]
        simp
      rw [hcancel]
      change (a.app G).hom ≫ qY.map (B.unit.app (T.functor.obj G)) ≫ 𝟙 _ =
        (a.app G).hom ≫ qY.map (B.unit.app (T.functor.obj G))
      simp only [Category.comp_id]
    exact congrArg (fun f ↦ f s) hsquare

end TopCat
