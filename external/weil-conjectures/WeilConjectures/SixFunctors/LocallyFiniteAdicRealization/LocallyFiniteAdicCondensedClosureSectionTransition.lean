/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedSectionScalarComposition

/-! # Section reconstruction of the finite closure transition

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-finite-condensed-closure-section-transition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
private theorem reconstruction_transition_square
    {E L D E₀ L₀ D₀ : Type*}
    [Category E] [Category L] [Category D]
    [Category E₀] [Category L₀] [Category D₀]
    (S : D ⥤ D₀) (H : E ⥤ L) (LE : E ⥤ D) (LL : L ⥤ D)
    (U : E ⥤ E₀) (V : L ⥤ L₀) (P : E₀ ⥤ D₀) (Q : L₀ ⥤ D₀)
    (J : E₀ ⥤ L₀)
    (a : LE ⋙ S ≅ U ⋙ P) (b : LL ⋙ S ≅ V ⋙ Q)
    (d : H ⋙ LL ≅ LE) (c : H ⋙ V ≅ U ⋙ J) (j : J ⋙ Q ≅ P)
    (M : E) (N : L) (F : E₀) (G : L₀)
    (e : U.obj M ≅ F) (f : V.obj N ≅ G)
    (σ : H.obj M ⟶ N) (τ : J.obj F ⟶ G)
    (hs : S.map (d.inv.app M) ≫ b.hom.app (H.obj M) =
      a.hom.app M ≫ j.inv.app (U.obj M) ≫ Q.map (c.inv.app M))
    (hσ : V.map σ = c.hom.app M ≫ J.map e.hom ≫ τ ≫ f.inv) :
    S.map (d.inv.app M ≫ LL.map σ) ≫ b.hom.app N ≫ Q.map f.hom =
      a.hom.app M ≫ P.map e.hom ≫ j.inv.app F ≫ Q.map τ := by
  have hn := b.hom.naturality σ
  dsimp only [Functor.comp_map] at hn
  rw [S.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  rw [← Category.assoc (S.map (d.inv.app M)) (b.hom.app (H.obj M)), hs]
  simp only [Category.assoc]
  rw [hσ]
  simp only [Q.map_comp, Category.assoc]
  have hc : Q.map (c.inv.app M) ≫ Q.map (c.hom.app M) = 𝟙 _ :=
    (Q.mapIso (c.app M)).inv_hom_id
  have hf : Q.map f.inv ≫ Q.map f.hom = 𝟙 _ :=
    (Q.mapIso f).inv_hom_id
  erw [reassoc_of% hc, hf, Category.comp_id]
  rw [← reassoc_of% (j.inv.naturality e.hom)]

private theorem whisker_factor
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (F : A ⥤ B) (S : B ⥤ C) (T : C ⥤ D) (U : C ⥤ E) (P : E ⥤ D)
    {H : B ⥤ D} {V : B ⥤ E} {W : A ⥤ E}
    (a : H ≅ S ⋙ T) (b : T ≅ U ⋙ P) (c : S ⋙ U ≅ V) (d : F ⋙ V ≅ W) :
    Functor.isoWhiskerLeft F a ≪≫ Functor.isoWhiskerLeft (F ⋙ S) b ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft F c) P ≪≫
        Functor.isoWhiskerRight d P =
      Functor.isoWhiskerLeft F
        (a ≪≫ Functor.isoWhiskerLeft S b ≪≫ Functor.isoWhiskerRight c P) ≪≫
        Functor.isoWhiskerRight d P := by
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Category.assoc]

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization
set_option allowUnsafeReducibility true in
attribute [local reducible] closureRing ProEtale.constructibleExtendScalars
  ProEtale.constructibleToPadicAlgCl finiteCondensedClosureFunctor
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

private theorem closureSectionComparison_factor (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    finiteCondensedClosureSectionComparison l X A E =
      Functor.isoWhiskerLeft
        (finiteCondensedFunctor l X A E ⋙
          (ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj X l E)).ι)
        (finiteCondensedClosureEncoding l X A E) ≪≫
      Functor.isoWhiskerRight (finiteCondensedComparison l X A E)
        (pbcDerivedExtend (A.closure.leg E)) := by
  unfold finiteCondensedClosureSectionComparison finiteCondensedClosureEncoding
  exact whisker_factor _ _ _ _ _ _ _ _ _

private theorem finiteScalarEncoding_map (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E) :
    ((ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj X l L)).ι ⋙
        (finiteCondensedEncoding l X A L).functor).map
        ((finiteCondensedScalarComparison l X A h).hom.app K) =
      (finiteCondensedScalarEncoding l X A h).hom.app
        (((ProEtale.boundedConstructible
          (ProEtale.padicSubfieldRingObj X l E)).ι).obj
            ((finiteCondensedFunctor l X A E).obj K)) ≫
      (pbcDerivedExtend (A.scalar.coefficient h).coefficient).map
        ((finiteCondensedComparison l X A E).hom.app K) ≫
      (scalarComparison l X A.toCore A.scalar h).inv.app K ≫
      (finiteCondensedComparison l X A L).inv.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
          K) := by
  unfold finiteCondensedScalarComparison
  dsimp only [ProEtale.constructibleExtendScalars]
  -- Cancel the preimage before expanding the composite functor map.
  simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Functor.comp_map, Category.assoc]

private theorem internalClosureComp_map {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (M : ProEtale.PadicSubfieldConstructible X l E) :
    (ProEtale.boundedConstructible (ProEtale.padicAlgClRingObj X l)).ι.map
        ((ProEtale.constructibleToPadicAlgClCompIso X l h).inv.app M) =
      (ProEtale.derivedExtendScalarsCompIso X l h).inv.app M.obj := by
  unfold ProEtale.constructibleToPadicAlgClCompIso
  dsimp only [ProEtale.constructibleExtendScalars, ProEtale.constructibleToPadicAlgCl]
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.refl_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.comp_id,
    ObjectProperty.ι_obj]

private theorem internalClosureComp_hom {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (M : ProEtale.PadicSubfieldConstructible X l E) :
    ((ProEtale.constructibleToPadicAlgClCompIso X l h).inv.app M).hom =
      (ProEtale.derivedExtendScalarsCompIso X l h).inv.app M.obj :=
  internalClosureComp_map l X h M

/-- Section reconstruction carries the condensed closure transition to the inverse
of the ordinary closure comparison, before restriction to integral objects.

Source: BS 6.8.2 and 6.8.14(2), the section-reconstruction part of the finite
coefficient comparison.
(blueprint: lem-sf-finite-condensed-closure-section-transition).

Proof in words: expand finiteCondensedClosureTransition and its finite scalar
comparison. The fully faithful encoding cancellation gives the specified scalar
encoding on applying the finite section equivalence. Naturality of its counit
cancels the finite reconstruction factors. The finite and closure section scalar
comparisons are the mates of the identity on underlying sections. Pasting their
unit equations identifies their composite with the section comparison of the
internal tensor associator. The actual coefficient square and the closure cocone
identify the remaining ordinary extension associator. Cancellation of these
invertible comparisons leaves the inverse of closureComparison. This calculation
is in the ambient derived category and holds for every raw stage object; it uses
neither the raw integral lift nor a native coefficient system. The identity field
inclusion uses the same adjunction unit and multiplication by one. Zero objects
and the empty scheme satisfy the same naturality equations.
-/
theorem finiteCondensedClosureSectionComparison_transition
    (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E) :
    (integralSections l X).map
        ((finiteCondensedClosureTransition l X A h).hom.app K) ≫
      (finiteCondensedClosureSectionComparison l X A L).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
          K) =
    (finiteCondensedClosureSectionComparison l X A E).hom.app K ≫
      (closureComparison l X A.toCore A.scalar A.closure h).inv.app K  := by
  let M := ((finiteCondensedFunctor l X A E).obj K).obj
  let N := ((finiteCondensedFunctor l X A L).obj
    (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K)).obj
  have hp := reconstruction_transition_square
    (integralSections l X) (ProEtale.derivedExtendScalarsSubfield X l h)
    (ProEtale.derivedExtendScalarsToPadicAlgCl X l E)
    (ProEtale.derivedExtendScalarsToPadicAlgCl X l L)
    (finiteCondensedEncoding l X A E).functor
    (finiteCondensedEncoding l X A L).functor
    (pbcDerivedExtend (A.closure.leg E)) (pbcDerivedExtend (A.closure.leg L))
    (pbcDerivedExtend (A.scalar.coefficient h).coefficient)
    (finiteCondensedClosureEncoding l X A E) (finiteCondensedClosureEncoding l X A L)
    (ProEtale.derivedExtendScalarsCompIso X l h)
    (finiteCondensedScalarEncoding l X A h)
    (Adjunction.leftAdjointCompIso
      (pbcDerivedScalarAdjunction (A.scalar.coefficient h).coefficient)
      (pbcDerivedScalarAdjunction (A.closure.leg L))
      (pbcDerivedScalarAdjunction (A.closure.leg E))
      (pbcDerivedRestrictComp (A.scalar.coefficient h).coefficient
        (A.closure.leg L) (A.closure.leg E) (A.closure.cocone h)))
    M N _ _ ((finiteCondensedComparison l X A E).app K)
    ((finiteCondensedComparison l X A L).app
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K))
    ((ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj X l L)).ι.map
      ((finiteCondensedScalarComparison l X A h).hom.app K))
    ((scalarComparison l X A.toCore A.scalar h).inv.app K)
    (finiteCondensedClosureEncoding_comp l X A h M)
    (finiteScalarEncoding_map l X A h K)
  dsimp only [M, N] at hp
  dsimp only [ProEtale.constructibleToPadicAlgCl]
  dsimp only [closureRing] at *
  rw [closureSectionComparison_factor, closureSectionComparison_factor]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map]
  simpa only [finiteCondensedClosureTransition,
    closureComparison, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Iso.symm_hom, internalClosureComp_map, Functor.comp_map, Category.assoc,
    ProEtale.constructibleToPadicAlgCl, ObjectProperty.lift, ObjectProperty.ι_obj,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom, Iso.app_hom,
    ObjectProperty.FullSubcategory.comp_hom, internalClosureComp_hom] using hp

end WeilConjectures.LocallyFiniteAdicRealization
