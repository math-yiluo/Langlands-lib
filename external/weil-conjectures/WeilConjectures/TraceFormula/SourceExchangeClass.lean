/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeCoefficient
public import WeilConjectures.TraceFormula.SourceExchangeProjection

/-!

# The core of the class of the coefficient pushforward

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with `q = f × f`, the test maps of the
class of the coefficient pushforward `[f, g]_! u` and of the transported class of `u` agree up to
the coefficient map
(`ProEtale.CondensedRing.Correspondence.ProperPushforwardDiagram.class_pushforward_core`,
blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 2). This gives identity (b),
`ProperPushforwardDiagram.class_pushforward`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {ℓ} {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

/-- The core of `class_pushforward`: the two ways of transporting `Rp₁'_! (Lp₂'^* K' ⊗ Rb_! 𝟙)`
to `Rf_* Rc₁_! Lc₂^* K` agree. -/
theorem class_pushforward_core :
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (Verdier.leftProjection
            (boundedConstructibleExceptionalProjection ℓ P.pushforward.support)
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _) ≫
          (boundedConstructibleLowerShriek ℓ P.pushforward.support).map
            ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ P.pushforward.support
              prod.snd).inv.app P.coeff)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ P.pushforward.support prod.fst).inv.app
        ((boundedConstructibleUpperStar _ ℓ (P.pushforward.support ≫ prod.snd)).obj P.coeff) ≫
      (boundedConstructibleLowerShriek ℓ (P.pushforward.support ≫ prod.fst)).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj P.coeff)
          P.pushforward.support_snd)) ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj
        ((boundedConstructibleUpperStar _ ℓ P.b₂).obj P.coeff)) P.pushforward.support_fst) ≫
      (boundedConstructibleLowerShriek ℓ P.b₁).map P.pushforwardCoeffUnit ≫
      (lowerStarLowerShriekCompIso ℓ P.w₁).hom.app
        ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K) =
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
          (boundedConstructibleLowerShriek ℓ P.pushforward.support).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
              (boundedConstructibleLowerStar ℓ P.g).map
                (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv)) ≫
      (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
          (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _)) ≫
      (classTransport ℓ P.f K).app ((boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _)) ≫
      (boundedConstructibleLowerStar ℓ P.f).map
        ((boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X)).map
            (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ c.support)
                ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K) (𝟙_ _) ≫
              (boundedConstructibleLowerShriek ℓ c.support).map
                ((ρ_ _).hom ≫
                    (boundedConstructibleUpperStarComp _ ℓ c.support prod.snd).inv.app K)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support prod.fst).inv.app
            ((boundedConstructibleUpperStar _ ℓ (c.support ≫ prod.snd)).obj K) ≫
          (boundedConstructibleLowerShriek ℓ (c.support ≫ prod.fst)).map
            (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj K)
              c.support_snd)) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj
            ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K)) c.support_fst)) := by
  simp only [classTransport, lowerStarLowerShriekCompIso, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, eqToIso.hom, eqToHom_app, Category.id_comp,
    Category.comp_id, Functor.comp_map, Category.assoc]
  simp only [curriedTensor_obj_map, MonoidalCategory.whiskerLeft_comp, Functor.map_comp,
    Category.assoc]
  conv_rhs =>
    simp only [Functor.map_whiskerLeft_hom_app_comp_map_whiskerLeft_inv_app_assoc
      (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y))
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map P.f P.f))
      ((boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _))]
  simp only [← Functor.map_comp (boundedConstructibleLowerStar ℓ P.f)]
  conv_rhs =>
    simp only [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ P.f).hom.naturality]
  simp only [← Category.assoc]
  refine congrArg (· ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ P.f).hom.app _) ?_
  simp only [Category.assoc, Functor.map_comp, leftProjectionNatTrans, curriedTensor_map_app,
    curriedTensor_obj_obj]
  conv_rhs =>
    simp only [Functor.map_map_comp_map_map_assoc_of_eq (boundedConstructibleLowerShriek ℓ P.f)
      (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X))
      (Verdier.leftProjection_naturality_left
          (boundedConstructibleExceptionalProjection ℓ c.support)
        (prodUpperStarCounit ℓ (prod.map_snd P.f P.f) K) (𝟙_ _))]
  have hsq := (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ
      (prod.map_fst P.f P.f)).hom.naturality
      (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ c.support)
        ((boundedConstructibleUpperStar _ ℓ (prod.map P.f P.f)).obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)) (𝟙_ _))
  simp only [Functor.comp_map] at hsq
  conv_rhs => simp only [← reassoc_of% hsq]
  have hc := leftProjection_lowerShriek_comp ℓ c.support (prod.map P.f P.f)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _)
  have h₃ : (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support (prod.map P.f P.f)).hom.app
          (𝟙_ _) ≫
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ (prod.map P.f P.f))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)
        ((boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _)) ≫
      (boundedConstructibleLowerShriek ℓ (prod.map P.f P.f)).map
        (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ c.support)
          ((boundedConstructibleUpperStar _ ℓ (prod.map P.f P.f)).obj
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff)) (𝟙_ _)) =
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ
          (c.support ≫ prod.map P.f P.f))
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _) ≫
      (boundedConstructibleLowerShriek ℓ (c.support ≫ prod.map P.f P.f)).map
        ((boundedConstructibleUpperStarComp _ ℓ c.support (prod.map P.f P.f)).hom.app _ ▷ _) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support
          (prod.map P.f P.f)).hom.app _ := by
    simpa only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using
      (congrArg (· ≫ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support
        (prod.map P.f P.f)).hom.app _) hc).symm
  conv_rhs => simp only [Functor.map_comp₃_assoc_of_eq
    (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)) h₃]
  conv_rhs => simp only [map_leftProjection_lowerShriek_comp_unit ℓ P.g P.pushforward.support
      P.g_comp_support]
  refine whisker_eq _ (whisker_eq _ ?_)
  unfold pushforwardCoeffUnit
  dsimp only [Functor.comp_obj]
  have hcoh := lowerShriek_pushforwardCoeff_coherence ℓ P.g P.pushforward.support c.support
    (prod.map P.f P.f) P.f prod.fst prod.snd prod.fst prod.snd
    (b₁ := P.b₁) (b₂ := P.b₂) (c₁ := c.c₁) (c₂ := c.c₂) P.pushforward.support_fst
    P.pushforward.support_snd c.support_fst c.support_snd P.g_comp_support
    (prod.map_fst P.f P.f) (prod.map_snd P.f P.f) P.w₁ P.w₂ K
  refine Eq.trans ?_ (hcoh.trans ?_)
  -- Normalize the coefficient abbreviation before comparing the long composites.
  all_goals simp only [coeff, Functor.comp_obj]
  all_goals rfl

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
