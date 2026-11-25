/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence
import WeilConjectures.TraceFormula.Supporting.NormalizedIntegralGeometricCoherence
import WeilConjectures.TraceFormula.Supporting.NormalizedIntegralMixedCoherence
import WeilConjectures.TraceFormula.Supporting.NormalizedIntegralScalarCoherence
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
/-! # One normalized pullback comparison system for every coefficient inclusion

Source: Stacks Project, Tags 099N, 0D6D, 06YY and 0941; blueprint trace-transport,
prop-trf-karoubi-independence.proof.md, final common-stage transport paragraph.
(blueprint: lem-trf-integral-pullback-comparison-realization).

The existing structures specify the actual quotient diagrams, counits and realization
maps. This interface puts their single simultaneous system outside the coefficient
quantifiers, as required for descent and coefficient towers.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem mixed_unit_of_composition
    {A B : Type*} [Category* A] [Category* B]
    (U : A ⥤ A) (V : B ⥤ B) (S : A ⥤ B)
    (e : U ≅ 𝟭 A) (f : V ≅ 𝟭 B) (c : U ≅ U ⋙ U) (d : V ≅ V ⋙ V)
    (κ : U ⋙ S ≅ S ⋙ V)
    (hc : ∀ N, c.hom.app N ≫ U.map (e.hom.app N) = 𝟙 _)
    (hd : ∀ N, d.hom.app N ≫ V.map (f.hom.app N) = 𝟙 _)
    (hm : ∀ N, S.map (c.hom.app N) ≫ κ.hom.app (U.obj N) ≫
      V.map (κ.hom.app N) = κ.hom.app N ≫ d.hom.app (S.obj N)) (N : A) :
    κ.hom.app N ≫ f.hom.app (S.obj N) = S.map (e.hom.app N) := by
  have hcu : c.hom.app N = U.map (e.inv.app N) := by
    apply (cancel_mono (U.map (e.hom.app N))).1
    simpa only [← U.map_comp, Iso.inv_hom_id_app, U.map_id, Functor.id_obj] using hc N
  have hn := κ.hom.naturality (e.inv.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have h : V.map (S.map (e.inv.app N) ≫ κ.hom.app N) = d.hom.app (S.obj N) := by
    apply (cancel_epi (κ.hom.app N)).1
    rw [V.map_comp, ← Category.assoc, ← hn, ← hcu]
    simpa only [Category.assoc] using hm N
  have hh : V.map ((S.map (e.inv.app N) ≫ κ.hom.app N) ≫
      f.hom.app (S.obj N)) = V.map (𝟙 (S.obj N)) := by
    rw [V.map_comp, h, hd, V.map_id]
  let : V.Faithful := Functor.Faithful.of_iso f.symm
  have heq := V.map_injective hh
  apply (cancel_epi (S.map (e.inv.app N))).1
  simpa only [Category.assoc, ← S.map_comp, Iso.inv_hom_id_app, S.map_id, Functor.id_obj] using heq

private theorem exchange_congr
    {A B : Type*} [Category* A] [Category* B] {I : Type*}
    (F : I → A ⥤ A) (G : I → B ⥤ B) (S : A ⥤ B)
    (κ : ∀ i, F i ⋙ S ⟶ S ⋙ G i) {i j : I} (h : i = j) (N : A) :
    S.map ((eqToHom (congrArg F h)).app N) ≫ (κ j).app N =
      (κ i).app N ≫ (eqToHom (congrArg G h)).app (S.obj N) := by
  subst j
  simp only [eqToHom_refl, NatTrans.id_app, S.map_id, Category.id_comp]
  exact Category.comp_id _ |>.symm

private theorem system_scalar_scheme_unit
    (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)
    (hQ : IntegralQuotientMixedCoherence.{u, u} l)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (N : coefficientSequenceModules l E X) :
    (integralComparisonSequenceScalarPullback l E L ι (𝟙 X)).hom.app N ≫
        (integralComparisonSequenceUnit l L X).hom.app
          ((integralComparisonSequenceScalarModel l E L ι X).E.obj N) =
      (integralComparisonSequenceScalarModel l E L ι X).E.map
        ((integralComparisonSequenceUnit l E X).hom.app N) := by
  apply mixed_unit_of_composition
    (integralComparisonSequencePullback l E (𝟙 X))
    (integralComparisonSequencePullback l L (𝟙 X))
    (integralComparisonSequenceScalarModel l E L ι X).E
    (integralComparisonSequenceUnit l E X) (integralComparisonSequenceUnit l L X)
    ((eqToIso (congrArg (integralComparisonSequencePullback l E)
      (Category.id_comp (𝟙 X)))).symm ≪≫
      integralComparisonSequenceComposition l E (𝟙 X) (𝟙 X))
    ((eqToIso (congrArg (integralComparisonSequencePullback l L)
      (Category.id_comp (𝟙 X)))).symm ≪≫
      integralComparisonSequenceComposition l L (𝟙 X) (𝟙 X))
    (integralComparisonSequenceScalarPullback l E L ι (𝟙 X))
  · intro J
    have h := NatTrans.congr_app (hQ.ordinary_unital E (𝟙 X)).2 J
    change (integralComparisonSequenceComposition l E (𝟙 X) (𝟙 X)).hom.app J ≫
      (integralComparisonSequencePullback l E (𝟙 X)).map
        ((integralComparisonSequenceUnit l E X).hom.app J) =
      (eqToHom (congrArg (integralComparisonSequencePullback l E)
        (Category.id_comp (𝟙 X)))).app J at h
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app]
    rw [Category.assoc, h]
    simp only [eqToHom_refl, NatTrans.id_app]
    exact Category.id_comp _
  · intro J
    have h := NatTrans.congr_app (hQ.ordinary_unital L (𝟙 X)).2 J
    change (integralComparisonSequenceComposition l L (𝟙 X) (𝟙 X)).hom.app J ≫
      (integralComparisonSequencePullback l L (𝟙 X)).map
        ((integralComparisonSequenceUnit l L X).hom.app J) =
      (eqToHom (congrArg (integralComparisonSequencePullback l L)
        (Category.id_comp (𝟙 X)))).app J at h
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app]
    rw [Category.assoc, h]
    simp only [eqToHom_refl, NatTrans.id_app]
    exact Category.id_comp _
  · intro J
    have h := NatTrans.congr_app (hQ.ordinary_mixed E L ι (𝟙 X) (𝟙 X)) J
    have ht := exchange_congr (integralComparisonSequencePullback l E)
      (integralComparisonSequencePullback l L) ((integralComparisonSequenceScalarModel l E L ι X).E)
      (fun f ↦ (integralComparisonSequenceScalarPullback l E L ι f).hom)
      (Category.id_comp (𝟙 X)).symm J
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app]
    simp only [Functor.map_comp, Category.assoc]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at h
    rw [h, ← Category.assoc, ht]
    simp only [Category.assoc]

/-- There is one specified quotient-diagram comparison system for all coefficient fields
and inclusions, with all the existing naturality, mixed, unit and tower equations.
Source: Stacks 099N, 0D6D, 06YY, 0941; blueprint final common-stage transport paragraph
(blueprint: lem-trf-integral-pullback-comparison-realization).

Proof: choose flat-term K-flat representatives and their simultaneous actual quotient
complexes, with the quotient transition maps. Resolve whole towers by K-injectives and
use the ordinary limit-cone map to define the derived-limit counit. Levelwise change of
rings and the quotient-module action give the entire-diagram comparison arrows. Their
realizations are eta, lambda and mu; derived completeness and the reduction theorem
make these invertible on every constructible input. This construction uses the same
reduction calculus and counit for every field and every inclusion, before either is
fixed. Inverse eta after realization of the finite compositor gives c; inverse mu after
lambda gives a. Naturality, equality of scheme maps, composition and all finite
iterations hold on the whole quotient diagrams, so realization preserves them. For
identity coefficients the quotient counit and completeness map give multiplication.
For a tower of inclusions the scalar comparison is the ordinary tensor associator
conjugated by the same completion comparisons chi. Thus all unit, tower and mixed
squares hold for this one system simultaneously. Localization preserves these
equalities. No perfectness or finite Tor-amplitude condition was used. -/
theorem integralPullbackComparisonRealization_simultaneous (l : ℕ) [Fact l.Prime] :
    ∃ C : IntegralComparisonSystem.{u} l,
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
        (ι : E →ₐ[ℚ_[l]] L), IntegralComparisonRealizationCoherence l E L ι C := by
  classical
  obtain ⟨C⟩ := ambientComparisonSystem_exists.{u} l
  refine ⟨C, ?_⟩
  intro E _ _ _ L _ _ _ ι
  have hQ := integralQuotientMixedCoherence.{u, u} l
  obtain ⟨hn, hm⟩ := normalizedIntegralMixedCoherence l C E L ι
  obtain ⟨hu, hi, ht⟩ := normalizedIntegralScalarCoherence l C E L ι
  refine {
    composition := fun F _ _ _ ↦ normalizedIntegralGeometricCoherence l C F
    systemScalarComposition := ?_
    naturality := hn
    scalarComposition := hm
    rationalScalarComposition := ?_
    systemScalarSchemeUnit := system_scalar_scheme_unit l E L ι hQ
    scalarSchemeUnit := hu
    systemScalarIdentity := ?_
    scalarIdentity := hi
    systemScalarTower := ?_
    scalarTower := ht }
  · intro V W Z _ _ _ h k N
    exact congrArg (fun t ↦ t.app N) (hQ.ordinary_mixed E L ι h k)
  · intro V W Z _ _ _ h k K
    exact congrArg (sfRationalConstructibleLocalization l L Z).map (hm h k K)
  · intro X Y _ _ f N
    exact congrArg (fun t ↦ t.app N) (hQ.ordinary_scalar_unit E f)
  · intro M _ _ _ j X Y _ _ f N
    exact congrArg (fun t ↦ t.app N) (hQ.ordinary_scalar_tower E L ι M j f)

end WeilConjectures
