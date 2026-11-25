/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence

/-! # NormalizedIntegralMixedCoherence

(blueprint: lem-trf-normalized-integral-mixed-coherence). -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem mate_postcompose
    {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (L : B ⥤ C) (adj : R ⊣ L)
    {F : C} {O N : B} (b : F ⟶ L.obj O) (z : O ⟶ N) :
    R.map (b ≫ L.map z) ≫ adj.counit.app N =
      R.map b ≫ adj.counit.app O ≫ z := by
  simpa only [Functor.map_comp, Functor.comp_map, Functor.id_map, Category.assoc] using
    congrArg (fun q ↦ R.map b ≫ q) (adj.counit.naturality z)

private theorem mate_comparison
    {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (L : B ⥤ C) (adj : R ⊣ L)
    {F G : C} {O N : B} (b : F ≅ L.obj O) (c : G ≅ L.obj N) (t : O ⟶ N) :
    R.map (b.hom ≫ L.map t ≫ c.inv) ≫
        (R.map c.hom ≫ adj.counit.app N) =
      (R.map b.hom ≫ adj.counit.app O) ≫ t := by
  calc
    _ = R.map (b.hom ≫ L.map t) ≫ adj.counit.app N := by
      rw [← Category.assoc, ← R.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      simpa only [Category.assoc] using mate_postcompose R L adj b.hom t

private theorem reduction_reflects
    {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (L : B ⥤ C) (adj : R ⊣ L)
    {K J : C} [Mono (adj.unit.app J)] (f g : K ⟶ J)
    (h : R.map f = R.map g) : f = g := by
  apply (cancel_mono (adj.unit.app J)).1
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  dsimp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [hf, hg]
  exact congrArg (fun t ↦ adj.unit.app K ≫ L.map t) h

private theorem composition_reduction
    (D : IntegralComparisonSystem.{u} l) {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    ((D.coefficient E).system Z).reduction.map
        (integralComparisonComposition l E D h k K).hom ≫
      (integralComparisonPullbackCounit l E h ((D.coefficient E).system W)
        ((D.coefficient E).system Z) ((D.coefficient E).roos Z)
        ((D.coefficient E).pullback h)).app
          ((integralDerivedPullback l E k).obj K.obj) ≫
      (integralComparisonDerivedSequencePullback l E h).map
        ((integralComparisonPullbackCounit l E k ((D.coefficient E).system V)
          ((D.coefficient E).system W) ((D.coefficient E).roos W)
          ((D.coefficient E).pullback k)).app K.obj) =
    (integralComparisonPullbackCounit l E (h ≫ k) ((D.coefficient E).system V)
      ((D.coefficient E).system Z) ((D.coefficient E).roos Z)
      ((D.coefficient E).pullback (h ≫ k))).app K.obj ≫
        (integralComparisonSystemComposition l E h k).hom.app
          (((D.coefficient E).system V).reduction.obj K.obj) := by
  have hh := mate_comparison _ _ ((D.coefficient E).system Z).adjunction
    (((D.coefficient E).pullback (h ≫ k)).realization.app K.obj)
    (integralComparisonEta l E D h k K)
    ((integralComparisonSystemComposition l E h k).hom.app
      (((D.coefficient E).system V).reduction.obj K.obj))
  have he := mate_postcompose _ _ ((D.coefficient E).system Z).adjunction
    (((D.coefficient E).pullback h).realization.hom.app
      ((integralDerivedPullback l E k).obj K.obj))
    ((integralComparisonDerivedSequencePullback l E h).map
      ((integralComparisonPullbackCounit l E k ((D.coefficient E).system V)
        ((D.coefficient E).system W) ((D.coefficient E).roos W)
        ((D.coefficient E).pullback k)).app K.obj))
  have hEta := he
  change
      ((D.coefficient E).system Z).reduction.map
          (integralComparisonEta l E D h k K).hom ≫
        ((D.coefficient E).system Z).adjunction.counit.app _ = _ at hEta
  rw [hEta] at hh
  simpa only [integralComparisonComposition, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, integralComparisonPullbackCounit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using hh

private theorem scalar_reduction
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    ((D.coefficient L).system X).reduction.map
        (integralComparisonScalar l E L ι D f K).hom ≫
      (integralComparisonPullbackCounit l L f ((D.coefficient L).system Y)
        ((D.coefficient L).system X) ((D.coefficient L).roos X)
        ((D.coefficient L).pullback f)).app
          ((integralScalarExtension l E L ι Y).obj K.obj) ≫
      (integralComparisonDerivedSequencePullback l L f).map
        ((integralComparisonScalarCounit l E L ι Y ((D.coefficient E).system Y)
          ((D.coefficient L).system Y) ((D.coefficient L).roos Y)
          ((D.scalar E L ι).model Y)).app K.obj) =
    (integralComparisonScalarCounit l E L ι X ((D.coefficient E).system X)
      ((D.coefficient L).system X) ((D.coefficient L).roos X)
      ((D.scalar E L ι).model X)).app ((integralDerivedPullback l E f).obj K.obj) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          ((integralComparisonPullbackCounit l E f ((D.coefficient E).system Y)
            ((D.coefficient E).system X) ((D.coefficient E).roos X)
            ((D.coefficient E).pullback f)).app K.obj) ≫
        (integralComparisonSystemScalarPullback l E L ι f).hom.app
          (((D.coefficient E).system Y).reduction.obj K.obj) := by
  let R := ((D.coefficient L).system X).reduction
  let T := coefficientSequenceLimit l L X
  let adj := ((D.coefficient L).system X).adjunction
  have hh := mate_comparison R T adj
    (integralComparisonLambda l E L ι D f K)
    (integralComparisonMu l E L ι D f K) (𝟙 _)
  have hLam := mate_postcompose R T adj (((D.scalar E L ι).model X).realization.hom.app
      ((integralDerivedPullback l E f).obj K.obj))
    ((integralComparisonDerivedSequenceScalar l E L ι X).map
      ((integralComparisonPullbackCounit l E f ((D.coefficient E).system Y)
        ((D.coefficient E).system X) ((D.coefficient E).roos X)
        ((D.coefficient E).pullback f)).app K.obj))
  have hMu := mate_postcompose R T adj (((D.coefficient L).pullback f).realization.hom.app
      ((integralScalarExtension l E L ι Y).obj K.obj))
    ((integralComparisonDerivedSequencePullback l L f).map
      ((integralComparisonScalarCounit l E L ι Y ((D.coefficient E).system Y)
        ((D.coefficient L).system Y) ((D.coefficient L).roos Y)
        ((D.scalar E L ι).model Y)).app K.obj) ≫
      (integralComparisonSystemScalarPullback l E L ι f).inv.app
        (((D.coefficient E).system Y).reduction.obj K.obj))
  have hLam' := hLam
  change R.map (integralComparisonLambda l E L ι D f K).hom ≫
      adj.counit.app _ = _ at hLam'
  have hMu' : R.map (integralComparisonMu l E L ι D f K).hom ≫
      adj.counit.app _ =
        R.map (((D.coefficient L).pullback f).realization.hom.app
          ((integralScalarExtension l E L ι Y).obj K.obj)) ≫
        adj.counit.app _ ≫
        (integralComparisonDerivedSequencePullback l L f).map
          ((integralComparisonScalarCounit l E L ι Y ((D.coefficient E).system Y)
            ((D.coefficient L).system Y) ((D.coefficient L).roos Y)
            ((D.scalar E L ι).model Y)).app K.obj) ≫
        (integralComparisonSystemScalarPullback l E L ι f).inv.app
          (((D.coefficient E).system Y).reduction.obj K.obj) := by
    simpa only [integralComparisonMu, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Functor.comp_obj, Functor.id_obj, Category.assoc] using hMu
  rw (transparency := .all) [T.map_id, Category.id_comp, Category.comp_id] at hh
  rw (transparency := .all) [hLam', hMu'] at hh
  have h := congrArg (fun a ↦ a ≫
    (integralComparisonSystemScalarPullback l E L ι f).hom.app
      (((D.coefficient E).system Y).reduction.obj K.obj)) hh
  simpa only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    integralComparisonScalarCounit, integralComparisonPullbackCounit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using h

/-- The mixed comparison is natural and commutes with geometric composition.
Source: Stacks 06YY, 0D6D and 0941, mixed common-stage transport.
Proof: give the words S U_h U_k and U_h U_k S their counit coordinates. The
primitive mixed square is exactly lambda followed by inverse mu. Naturality of
these two transformations proves the first assertion by cancelling mu. For the
second, paste the compositor and mixed squares in the two orders. Whole-system
mixed coherence identifies the resulting system transformations. Word cut and
counit naturality identify each whiskered coordinate; cancel the common invertible
coordinate. Full-subcategory morphism extensionality yields the asserted equation.
(blueprint: lem-trf-normalized-integral-mixed-coherence). -/
theorem normalizedIntegralMixedCoherence
    (l : ℕ) [Fact l.Prime] (D : IntegralComparisonSystem.{u} l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    (∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K J : sfIntegralConstructibleCategory l E Y) (r : K ⟶ J),
    (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E f).map r.hom) ≫
        (integralComparisonScalar l E L ι D f J).hom =
      (integralComparisonScalar l E L ι D f K).hom ≫
        (integralDerivedPullback l L f).map ((integralScalarExtension l E L ι Y).map r.hom)) ∧
    (∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
    integralComparisonScalarSquareLeft l E L ι D h k K =
      integralComparisonScalarSquareRight l E L ι D h k K) := by
  constructor
  · intro X Y _ _ f K J r
    let a := (D.coefficient E).system Y
    let b := (D.coefficient E).system X
    let d := (D.coefficient L).system Y
    let LL := coefficientSequenceLimit l L X
    let T := integralComparisonDerivedSequenceScalar l E L ι X
    let F := integralComparisonDerivedSequencePullback l L f
    let q := integralComparisonPullbackCounit l E f a b ((D.coefficient E).roos X)
      ((D.coefficient E).pullback f)
    let t := integralComparisonScalarCounit l E L ι Y a d ((D.coefficient L).roos Y)
      ((D.scalar E L ι).model Y)
    let lam := Functor.whiskerLeft (integralDerivedPullback l E f)
        ((D.scalar E L ι).model X).realization.hom ≫
      Functor.whiskerRight q (T ⋙ LL)
    let mu := Functor.whiskerLeft (integralScalarExtension l E L ι Y)
        ((D.coefficient L).pullback f).realization.hom ≫
      Functor.whiskerRight t (F ⋙ LL) ≫
      Functor.whiskerRight (Functor.whiskerLeft a.reduction
        (integralComparisonSystemScalarPullback l E L ι f).inv) LL
    have hlam := lam.naturality r.hom
    have hmu := mu.naturality r.hom
    change _ ≫ ((integralComparisonLambda l E L ι D f J).hom ≫
      (integralComparisonMu l E L ι D f J).inv) =
      ((integralComparisonLambda l E L ι D f K).hom ≫
        (integralComparisonMu l E L ι D f K).inv) ≫ _
    have hlam' : (integralScalarExtension l E L ι X).map
          ((integralDerivedPullback l E f).map r.hom) ≫
        (integralComparisonLambda l E L ι D f J).hom =
      (integralComparisonLambda l E L ι D f K).hom ≫
        (a.reduction ⋙ integralComparisonDerivedSequencePullback l E f ⋙ T ⋙ LL).map r.hom := by
      exact hlam
    have hmu' : (integralDerivedPullback l L f).map
          ((integralScalarExtension l E L ι Y).map r.hom) ≫
        (integralComparisonMu l E L ι D f J).hom =
      (integralComparisonMu l E L ι D f K).hom ≫
        (a.reduction ⋙ integralComparisonDerivedSequencePullback l E f ⋙ T ⋙ LL).map r.hom := by
      exact hmu
    apply (cancel_mono (integralComparisonMu l E L ι D f J).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hmu', Iso.inv_hom_id_assoc]
    exact hlam'
  · intro V W Z _ _ _ h k K
    apply ObjectProperty.hom_ext
    change (integralScalarExtensionOfUniverses l E L ι Z).map
        (integralComparisonComposition l E D h k K).hom ≫
      (integralComparisonScalar l E L ι D h
        ((constructibleIntegralPullback l E k).obj K)).hom ≫
      (integralDerivedPullback l L h).map
        (integralComparisonScalar l E L ι D k K).hom =
      (integralComparisonScalar l E L ι D (h ≫ k) K).hom ≫
      (integralComparisonComposition l L D h k
        ((integralComparisonConstructibleScalar l E L ι V).obj K)).hom
    let RE (A : Scheme.{u}) := ((D.coefficient E).system A).reduction
    let RL (A : Scheme.{u}) := ((D.coefficient L).system A).reduction
    let UE {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonDerivedSequencePullback l E f
    let UL {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonDerivedSequencePullback l L f
    let S (A : Scheme.{u}) := integralComparisonDerivedSequenceScalar l E L ι A
    let rE {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonPullbackCounit l E f ((D.coefficient E).system B)
        ((D.coefficient E).system A) ((D.coefficient E).roos A)
        ((D.coefficient E).pullback f)
    let rL {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonPullbackCounit l L f ((D.coefficient L).system B)
        ((D.coefficient L).system A) ((D.coefficient L).roos A)
        ((D.coefficient L).pullback f)
    let rS (A : Scheme.{u}) := integralComparisonScalarCounit l E L ι A
      ((D.coefficient E).system A) ((D.coefficient L).system A)
      ((D.coefficient L).roos A) ((D.scalar E L ι).model A)
    let PK := (constructibleIntegralPullback l E k).obj K
    let TK := (integralComparisonConstructibleScalar l E L ι V).obj K
    let PTK := (constructibleIntegralPullback l L k).obj TK
    let ah := (integralComparisonScalar l E L ι D h PK).hom
    let ak := (integralComparisonScalar l E L ι D k K).hom
    let a := (integralComparisonScalar l E L ι D (h ≫ k) K).hom
    let cE := (integralComparisonComposition l E D h k K).hom
    let cL := (integralComparisonComposition l L D h k TK).hom
    have nh := (rL h).naturality ak
    have ns := (rS Z).naturality cE
    have na := (integralComparisonSystemScalarPullback l E L ι h).hom.naturality
      ((rE k).app K.obj)
    have nc := (integralComparisonSystemComposition l L h k).hom.naturality
      ((rS V).app K.obj)
    dsimp only [Functor.comp_map] at nh ns na nc
    have ce := composition_reduction l E D h k K
    have cl := composition_reduction l L D h k TK
    have sh := scalar_reduction l E L ι D h PK
    have sk := scalar_reduction l E L ι D k K
    have shk := scalar_reduction l E L ι D (h ≫ k) K
    have sk' := congrArg (UL h).map sk
    have ce' := congrArg (S Z).map ce
    simp only [Functor.map_comp] at sk' ce'
    have mix := NatTrans.congr_app
      ((integralQuotientMixedCoherence.{u, u} l).derived_mixed E L ι h k)
        ((RE V).obj K.obj)
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at mix
    let := (D.scalar E L ι).effective V K
    let := (D.coefficient L).effective k TK
    let := (D.coefficient L).effective h PTK
    let target := (constructibleIntegralPullback l L h).obj PTK
    let hcomplete : IsIso (((D.coefficient L).system Z).adjunction.unit.app
        ((integralDerivedPullback l L h).obj
          ((integralDerivedPullback l L k).obj
            ((integralScalarExtension l E L ι V).obj K.obj)))) := by
      with_unfolding_all exact (D.coefficient L).complete Z target
    apply reduction_reflects (RL Z) (coefficientSequenceLimit l L Z)
      ((D.coefficient L).system Z).adjunction
    apply (cancel_mono ((rL h).app PTK.obj ≫
      (UL h).map ((rL k).app TK.obj) ≫
      (UL h).map ((UL k).map ((rS V).app K.obj)))).1
    simp only [Functor.map_comp, Category.assoc]
    change (RL Z).map ((integralScalarExtensionOfUniverses l E L ι Z).map cE) ≫
      (RL Z).map ah ≫ (RL Z).map ((integralDerivedPullback l L h).map ak) ≫
      (rL h).app PTK.obj ≫ (UL h).map ((rL k).app TK.obj) ≫
      (UL h).map ((UL k).map ((rS V).app K.obj)) = _
    dsimp only [ah, ak, a, cE, cL, PK, TK, PTK]
    rewrite (transparency := .default) [reassoc_of% nh]
    rewrite (transparency := .default) [sk']
    rewrite (transparency := .default) [reassoc_of% sh]
    rewrite (transparency := .default) [← reassoc_of% na]
    rewrite (transparency := .default) [reassoc_of% ns]
    rewrite (transparency := .default) [reassoc_of% ce']
    rewrite (transparency := .default) [mix]
    rewrite (transparency := .default) [← reassoc_of% shk]
    rewrite (transparency := .default) [nc]
    rewrite (transparency := .default) [reassoc_of% cl]
    rfl

end WeilConjectures
