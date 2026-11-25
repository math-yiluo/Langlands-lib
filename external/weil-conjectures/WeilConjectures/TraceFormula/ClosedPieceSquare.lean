/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.SourceExchangeKunnethAux

/-!

# The closed piece coefficient and the unit

Let `h : X ⟶ X`, `v : Lh^* K ⟶ K` and `x` a rational point fixed by `h`. The closed piece
coefficient `u^Z = [x, x]_! v_x` on `K^Z = Rx_* Lx^* K` is compatible with `v` along the unit
`η : K ⟶ Rx_* Lx^* K` (blueprint `proposition-additivity-trace-classes--2`, proof of item 2, step
(b)):
```
u^Z ∘ Lh^* η = η ∘ v        (up to R(𝟙)^! ≅ 𝟭),
```
`Correspondence.upperStar_map_unit_comp_graphClosedPieceCoeff` (the curve pieces of a Weil
object are deduced in `WeilConjectures.TraceFormula.CurvePiecesAdditivity`).
By the adjunction `Lx^* ⊣ Rx_*` it suffices to compare the adjoint maps `Lx^* Lh^* K ⟶ Lx^* K`,
which the triangle identities reduce to `Lx^* v`.

The intermediate statements mentioning the concrete proper pushforward diagram `(x, x)` are
private: exporting their statements is expensive.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}

/-- A composite through `G.map` of a transpose `φ ≫ adj.homEquiv θ` is the transpose of
`F.map v` when `F.map φ ≫ θ ≫ u₁ ≫ u₂ = F.map v`: the two composites
```
T --φ--> T' --adj.homEquiv θ--> G B --G u₁--> G B' --G u₂--> G (F K₀) --r--> M
T --v--> K₀ --η--> G (F K₀) --r--> M
```
agree. -/
lemma comp_homEquiv_comp_map_comp_map_comp (adj : F ⊣ G) {T T' K₀ : C} {B B' : D} {M : C}
    (φ : T ⟶ T') (θ : F.obj T' ⟶ B) (u₁ : B ⟶ B') (u₂ : B' ⟶ F.obj K₀) (v : T ⟶ K₀)
    (r : G.obj (F.obj K₀) ⟶ M) (h : F.map φ ≫ θ ≫ u₁ ≫ u₂ = F.map v) :
    φ ≫ adj.homEquiv _ _ θ ≫ G.map u₁ ≫ G.map u₂ ≫ r = v ≫ adj.unit.app K₀ ≫ r := by
  rw [← reassoc_of% (adj.homEquiv_naturality_left φ θ), ← G.map_comp_assoc,
    ← reassoc_of% (adj.homEquiv_naturality_right (F.map φ ≫ θ) (u₁ ≫ u₂))]
  simp only [Category.assoc, h, adj.homEquiv_unit, ← adj.unit_naturality_assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace Correspondence

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

set_option backward.isDefEq.respectTransparency true in
/-- The stalk computation: the composite
```
Lx^* Lh^* K --Lx^* Lh^* η--> Lx^* Lh^* Rx_* Lx^* K ≅ L(𝟙)^* Lx^* Rx_* Lx^* K --ε--> L(𝟙)^* Lx^* K
  ≅ Lx^* K --v_x--> Lx^* K
```
is `Lx^* v`, by the triangle identity of `Lx^* ⊣ Rx_*`. -/
lemma upperStar_map_unit_comp_comp_graphStalkMap :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K)) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).inv.app
        (pointClosedPiece K x) ≫
      eqToHom (by rw [hx, Category.id_comp]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))
        x).hom.app (pointClosedPiece K x) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) ≫
      graphStalkMap K h v x hx =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map v := by
  have h₁ := (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x
    h).inv.naturality ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K)
  have h₂ := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ
    (point k)).hom.naturality ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).counit.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K))
  have h₃ := boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ x
    (pointClosedPiece K x)
  have h₄ := upperStar_map_comp_eqToHom_congrArg ℓ _ hx
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K)
  have h₅ := (boundedConstructibleUpperStarLowerStarAdjunction ℓ x).left_triangle_components K
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂
  dsimp only [Functor.id_obj]
  rw [graphStalkMap, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, eqToHom_trans_assoc,
    reassoc_of% h₄, reassoc_of% h₅, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_app_assoc]

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The coefficient pushforward of a proper pushforward diagram, with its ordinary half written
as an adjoint for `Lg^* ⊣ Rg_*`. -/
lemma ProperPushforwardDiagram.pushforwardCoeff_eq_homEquiv {S Y : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {A : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ A}
    (P : c.ProperPushforwardDiagram Y) :
    P.pushforwardCoeff =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).homEquiv _ _
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ P.g P.b₂).inv.app
              _ ≫
            eqToHom (by rw [P.w₂]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂ P.f).hom.app
              _ ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
                P.f).counit.app A)) ≫
        (boundedConstructibleLowerStar ℓ P.g).map c.u ≫
        (lowerStarUpperShriekExchange ℓ P.w₁).app A := by
  rw [Adjunction.homEquiv_unit]
  rfl

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

/-- **The closed piece coefficient is compatible with the unit** (blueprint
`proposition-additivity-trace-classes--2`, proof of item 2, step (b)): for `x` fixed by `h`, the
closed piece coefficient `u^Z = [x, x]_! v_x` satisfies `u^Z ∘ Lh^* η = η ∘ v` for the unit
`η : K ⟶ Rx_* Lx^* K`, up to `R(𝟙)^! ≅ 𝟭`. -/
theorem upperStar_map_unit_comp_graphClosedPieceCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K) ≫
      graphClosedPieceCoeff K v hx =
      v ≫ (boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app _ := by
  have e₁ := ProperPushforwardDiagram.pushforwardCoeff_eq_homEquiv (graphClosedPieceDiagram K v hx)
  have e₂ : (lowerStarUpperShriekExchange ℓ (graphClosedPieceDiagram K v hx).w₁).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) =
      (boundedConstructibleLowerStar ℓ x).map
          ((boundedConstructibleUpperShriekId ℓ (point k)).hom.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app (pointClosedPiece K x) :=
    lowerStarUpperShriekExchange_app_of_id ℓ x _ _
  have e₃ := upperStar_map_unit_comp_comp_graphStalkMap K v hx
  have hu : (ofEnd _ (graphStalkMap K h v x hx)).u =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) ≫
        graphStalkMap K h v x hx ≫ (boundedConstructibleUpperShriekId ℓ (point k)).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) := rfl
  have e₀ : graphClosedPieceCoeff K v hx = (graphClosedPieceDiagram K v hx).pushforwardCoeff := rfl
  rw [e₀]
  rw [e₁]
  simp only [e₂, hu]
  dsimp only [graphClosedPieceDiagram, ofEnd, ProperPushforwardDiagram.coeff]
  refine CategoryTheory.Adjunction.comp_homEquiv_comp_map_comp_map_comp _ _ _ _ _ _ _ ?_
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]
  exact e₃

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The coefficient pushforward along a proper pushforward diagram only depends on the
coefficient map of the correspondence. -/
lemma ProperPushforwardDiagram.pushforwardCoeff_congr {S Y C D : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
    {A : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c₁ c₂ : C ⟶ S)
    {u u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj A ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj A}
    (hu : u = u') (f : S ⟶ Y) [IsProper f.left] (b₁ b₂ : D ⟶ Y) (g : C ⟶ D) [IsProper g.left]
    (w₁ : g ≫ b₁ = c₁ ≫ f) (w₂ : g ≫ b₂ = c₂ ≫ f) :
    (ProperPushforwardDiagram.mk (c := ⟨C, c₁, c₂, u⟩) f D b₁ b₂ g w₁ w₂).pushforwardCoeff =
      (ProperPushforwardDiagram.mk (c := ⟨C, c₁, c₂, u'⟩) f D b₁ b₂ g w₁ w₂).pushforwardCoeff := by
  subst hu
  rfl

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
