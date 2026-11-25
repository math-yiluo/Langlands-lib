/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions

/-! # Evaluation of the ordinary transported open-system counit

Source: Stacks Project, Tags 03DJ and 0941. All equalities here precede localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  PresheafOfModules.sheafification
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] (o : Operations l E j)

private theorem equivalence_counit_cancel
    {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {M : C} {N : D} (f : e.functor.obj M ⟶ N) :
    e.functor.map (e.unitIso.hom.app M ≫ e.inverse.map f) ≫
      e.counitIso.hom.app N = f := by
  have hn := e.counitIso.hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Category.assoc, hn]
  simpa only [← Category.assoc, Category.id_comp] using
    congrArg (fun g ↦ g ≫ f) (e.functor_unitIso_comp M)

private theorem transported_counit_evaluation
    {A B C a b c : Type*}
    [Category A] [Category B] [Category C] [Category a] [Category b] [Category c]
    (e : A ≌ B) (e' : a ≌ b) {F : B ⥤ C} {G : C ⥤ B}
    {L : b ⥤ c} {R : c ⥤ b} (adj : F ⊣ G) (adj' : L ⊣ R)
    (E : C ⥤ c) (V : B ⥤ b) (W : A ⥤ a)
    (τ : e.functor ⋙ V ≅ W ⋙ e'.functor)
    (μ : F ⋙ E ≅ V ⋙ L) (ν : G ⋙ V ≅ E ⋙ R)
    (hε : ∀ N : C, L.map (ν.hom.app N) ≫ adj'.counit.app (E.obj N) =
      μ.inv.app (G.obj N) ≫ E.map (adj.counit.app N)) (N : C) :
    (e'.functor ⋙ L).map
        (e'.unitIso.hom.app (W.obj (e.inverse.obj (G.obj N))) ≫
          e'.inverse.map (τ.inv.app (e.inverse.obj (G.obj N)) ≫
            V.map (e.counitIso.hom.app (G.obj N)) ≫ ν.hom.app N)) ≫
      (e'.toAdjunction.comp adj').counit.app (E.obj N) =
    L.map (τ.inv.app (e.inverse.obj (G.obj N))) ≫
      μ.inv.app (e.functor.obj (e.inverse.obj (G.obj N))) ≫
      E.map ((e.toAdjunction.comp adj).counit.app N) := by
  let z := τ.inv.app (e.inverse.obj (G.obj N)) ≫
    V.map (e.counitIso.hom.app (G.obj N)) ≫ ν.hom.app N
  have hc := equivalence_counit_cancel e' z
  simp only [Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Functor.comp_map]
  dsimp only [z, Equivalence.counit, Functor.comp_obj] at hc ⊢
  rw [← L.map_comp_assoc, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hε]
  have hn := μ.inv.naturality (e.counitIso.hom.app (G.obj N))
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

private theorem transported_counit_comparison
    {A B C a b c : Type*}
    [Category A] [Category B] [Category C] [Category a] [Category b] [Category c]
    (e : A ≌ B) (e' : a ≌ b) {F : B ⥤ C} {G : C ⥤ B}
    {L : b ⥤ c} {R : c ⥤ b} (adj : F ⊣ G) (adj' : L ⊣ R)
    (E : C ⥤ c) (V : B ⥤ b) (W : A ⥤ a)
    (τ : e.functor ⋙ V ≅ W ⋙ e'.functor)
    (μ : F ⋙ E ≅ V ⋙ L) (ν : G ⋙ V ≅ E ⋙ R)
    (hε : ∀ N : C, L.map (ν.hom.app N) ≫ adj'.counit.app (E.obj N) =
      μ.inv.app (G.obj N) ≫ E.map (adj.counit.app N)) (N : C) :
    let ρ := e'.unitIso.app (W.obj (e.inverse.obj (G.obj N))) ≪≫
      e'.inverse.mapIso (τ.app (e.inverse.obj (G.obj N))).symm ≪≫
      e'.inverse.mapIso (V.mapIso (e.counitIso.app (G.obj N))) ≪≫
      e'.inverse.mapIso (ν.app N)
    let η : (e.functor ⋙ F) ⋙ E ≅ W ⋙ (e'.functor ⋙ L) :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.functor μ ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight τ L ≪≫
          Functor.associator _ _ _
    (e'.functor ⋙ L).map ρ.hom ≫
        (e'.toAdjunction.comp adj').counit.app (E.obj N) =
      η.inv.app (e.inverse.obj (G.obj N)) ≫
        E.map ((e.toAdjunction.comp adj).counit.app N) := by
  have h := transported_counit_evaluation e e' adj adj' E V W τ μ ν hε N
  simpa only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, NatTrans.vcomp_app',
    Functor.comp_obj, Functor.id_obj, Functor.map_comp, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id, Category.assoc] using h

/-- The actual restriction evaluation, including the coefficient equivalence units
and counits. Source: Stacks 03DJ, 0941
(blueprint: lem-sf-open-system-counit-evaluation). -/
abbrev counitRestrictionEvaluation (n : ℕ) (N : coefficientSequenceModules l E X) :
    (coefficientSequenceEvaluation l E U n).obj ((systemRestriction l E j o).obj N) ≅
      (finiteRestriction l E j o n).obj ((coefficientSequenceEvaluation l E X n).obj N) :=
  (o.finite n).unitIso.app _ ≪≫
    (o.finite n).inverse.mapIso
      ((o.transportEvaluation n).app ((systemRestriction l E j o).obj N)).symm ≪≫
    (o.finite n).inverse.mapIso
      ((SemilinearSections.evaluation.{t+1, t, max u (t + 1)}
        ((ProEt.topology X).over (openObject j))
        (fun k ↦ (rings l E X k).over (openObject j))
        (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
          (openObject j)).map (transitions l E X k)) n).mapIso
        (o.systems.counitIso.app _)) ≪≫
    (o.finite n).inverse.mapIso ((o.openSystems.restrictionEvaluation n).app N)

/-- The transported ordinary open-system counit evaluates to the finite counit.
Source: Stacks Project, Tags 03DJ and 0941; the ordinary evaluation calculation
in step 2 of `lem-sf-open-restriction-counit-on-good-complexes`.
(blueprint: lem-sf-open-system-counit-evaluation).

Proof: expand the counit of the composite adjunction into the equivalence counit
and the localized open counit. Use naturality of extension evaluation to move the
equivalence counit across it. Substitute the specified counit evaluation equation
of openSystems. In the remaining finite equivalence, naturality of its counit
moves transportEvaluation across the finite restriction comparison. The finite
equivalence triangle identity cancels its unit with its counit. This leaves the
same ordinary system counit evaluated at the finite level. -/
theorem openSystemCounitEvaluation (n : ℕ) (N : coefficientSequenceModules l E X) :
    (finiteExtension l E j o n).map (counitRestrictionEvaluation l E j o n N).hom ≫
      ((o.finite n).toAdjunction.comp
        (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t + 1)}
          (rings l E X n) (openObject j))).counit.app
            ((coefficientSequenceEvaluation l E X n).obj N) =
    (extensionEvaluation l E j o n).inv.app ((systemRestriction l E j o).obj N) ≫
      (coefficientSequenceEvaluation l E X n).map
        ((ordinarySystemAdjunction l E j o).counit.app N) := by
  exact transported_counit_comparison o.systems (o.finite n)
    o.openSystems.ordinaryAdjunction
    (@SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t + 1)}
      X.ProEt _ (ProEt.topology X)
      (SemilinearSections.abelianSheafify.{t+1, t, max u (t + 1)} (ProEt.topology X))
      (SemilinearSections.locallyBijective.{t+1, t, max u (t + 1)} (ProEt.topology X))
      (rings l E X n) (openObject j))
    (SemilinearSections.evaluation.{t+1, t, max u (t + 1)}
      (ProEt.topology X) (rings l E X) (transitions l E X) n)
    (SemilinearSections.evaluation.{t+1, t, max u (t + 1)}
      ((ProEt.topology X).over (openObject j))
      (fun k ↦ (rings l E X k).over (openObject j))
      (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
        (openObject j)).map (transitions l E X k)) n)
    (coefficientSequenceEvaluation l E U n)
    (o.transportEvaluation n) (o.openSystems.extensionEvaluation n)
    (o.openSystems.restrictionEvaluation n)
    (fun M ↦ o.openSystems.counit_evaluation n M) N

end WeilConjectures.CanonicalOpenRestriction
