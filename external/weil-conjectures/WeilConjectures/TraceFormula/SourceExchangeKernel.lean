/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunneth

/-!

# Identity (a) of the trace-class source exchange

`κ_Y ∘ ρ_f = Φ ∘ Rq_* κ_X` (`ProEtale.CondensedRing.kernelPushforward_comp_kunnethVerdierMap`,
blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 3), assembled from the evaluation
part and the exceptional Künneth part proved in
`WeilConjectures.TraceFormula.SourceExchangeKunneth`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- Move a mapped composite through two natural isomorphisms, keeping the final map grouped. -/
private lemma map_whiskerLeft_comp_naturality {V W X Y : Type*} [Category V] [Category W]
    [Category X] [Category Y] [MonoidalCategory W]
    (F : W ⥤ Y) (G : V ⥤ W) (H : V ⥤ X) {Lf Sf : X ⥤ Y}
    (s : G ⋙ F ≅ H ⋙ Lf) (σ : Lf ≅ Sf) (A : W) {B₀ B₁ B₂ : W} {V₀ V₁ V₂ : V} {Z : X}
    (a : B₀ ⟶ B₁) (b : B₁ ⟶ B₂) (p : A ⊗ B₂ ⟶ G.obj V₀)
    (y : V₀ ⟶ V₁) (e : V₁ ⟶ V₂) (t : H.obj V₂ ⟶ Z) :
    F.map (A ◁ (a ≫ b) ≫ p ≫ G.map (y ≫ e)) ≫ s.hom.app V₂ ≫ Lf.map t ≫ σ.hom.app Z =
      F.map (A ◁ a) ≫ F.map (A ◁ b) ≫ F.map p ≫ s.hom.app V₀ ≫
        Lf.map (H.map y) ≫ σ.hom.app (H.obj V₁) ≫ Sf.map (H.map e ≫ t) := by
  have hs := s.hom.naturality (y ≫ e)
  have hσ := σ.hom.naturality (H.map e ≫ t)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hs hσ
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hs, hσ]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- **The kernel pushforward and the Künneth–Verdier isomorphisms** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, identity (a)): `κ_Y ∘ ρ_f = Φ ∘ Rq_* κ_X`. -/
theorem kernelPushforward_comp_kunnethVerdierMap :
    kernelPushforward ℓ f K ≫
        kunnethVerdierMap ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
          ((boundedConstructibleLowerStar ℓ f).obj K) =
      (boundedConstructibleLowerStar ℓ (prod.map f f)).map (kunnethVerdierMap ℓ K K) ≫
        classTransportMap ℓ f K := by
  simp only [kernelPushforward, Category.assoc, IsIso.inv_comp_eq]
  apply classTest_injective ℓ (M := (boundedConstructibleLowerStar ℓ f).obj K)
  simp only [classTest_comp ℓ _ (kunnethVerdierMap ℓ
      ((boundedConstructibleLowerStar ℓ f).obj K) ((boundedConstructibleLowerStar ℓ f).obj K)),
    classTest_comp ℓ _ ((boundedConstructibleLowerStar ℓ (prod.map f f)).map
      (kunnethVerdierMap ℓ K K) ≫ classTransportMap ℓ f K),
    classTest_map_comp_classTransportMap, classTest_kunnethVerdierMap]
  simp only [← Functor.map_comp_assoc]
  refine (congrArg (fun t ↦ (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map t ≫
    exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar ℓ f).obj K))
    (MonoidalCategory.whiskerLeft_whiskerLeft_map_comp_evaluation
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar ℓ f).obj K))
    ((boundedConstructibleLowerStar ℓ f).obj K) (lowerStarVerdierDualMap ℓ f K)
    ((ihom.ev ((boundedConstructibleLowerStar ℓ f).obj K)).app (dualizingComplex' ℓ Y))
    _ (MonoidalClosed.whiskerLeft_curry_ihom_ev_app (A :=
        (boundedConstructibleLowerStar ℓ f).obj K) _ _))).trans ?_
  refine (Functor.map_whiskerLeft_map_comp_eq
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar ℓ f).obj K)) _ _ _ _
    (lowerStarTensorMap ℓ f K (verdierDual ℓ K))
    ((boundedConstructibleLowerStar ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)))
    (lowerStarDualizingComplexTrace ℓ f)
    (exceptionalKunnethAdjoint ℓ ((boundedConstructibleLowerStar ℓ f).obj K))
    (prodLowerStarExternalProduct ℓ f f K (dualizingComplex' ℓ X))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
      (externalProduct ℓ K (dualizingComplex' ℓ X))) _ _
    (lowerShriek_map_trace_comp_exceptionalKunnethAdjoint ℓ f K)
    (evaluation_comp_prodLowerStarExternalProduct ℓ f K)).trans ?_
  simp only [classTransport, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map, Category.id_comp,
    Category.comp_id, Category.assoc, leftProjectionNatTrans, curriedTensor_map_app,
    curriedTensor_obj_obj]
  have htransport := Functor.map_whiskerLeft_comp_naturality
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y))
    (boundedConstructibleLowerShriek ℓ (prod.map f f))
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X))
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
      ((boundedConstructibleLowerStar ℓ f).obj K))
    (prodLowerStarExternalProduct ℓ f f K (verdierDual ℓ K))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv.app
      (externalProduct ℓ K (verdierDual ℓ K)))
    (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ (prod.map f f))
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
        ((boundedConstructibleLowerStar ℓ f).obj K)) (externalProduct ℓ K (verdierDual ℓ K)))
    (prodUpperStarCounit ℓ (prod.map_snd f f) K ▷ externalProduct ℓ K (verdierDual ℓ K))
    ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
      (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
        (prod.snd : X ⨯ X ⟶ X)) K (verdierDual ℓ K)) ≫
      (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map
        ((ihom.ev K).app (dualizingComplex' ℓ X))))
    (exceptionalKunnethAdjoint ℓ K)
  dsimp only [externalProduct, verdierDual, dualizingComplex, dualizingComplex', toPoint,
    tensorLeft, Functor.comp_obj, Functor.id_obj, curriedTensor_obj_obj,
    curriedTensor_obj_map] at htransport ⊢
  convert! htransport using 1

end AlgebraicGeometry.ProEtale.CondensedRing
