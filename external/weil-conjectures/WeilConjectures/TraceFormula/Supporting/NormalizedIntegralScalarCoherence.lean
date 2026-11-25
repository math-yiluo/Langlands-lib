/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import WeilConjectures.TraceFormula.Integral.IntegralScalarCounitNormalization
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

/-! # NormalizedIntegralScalarCoherence

(blueprint: lem-trf-normalized-integral-scalar-coherence). -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

noncomputable section Proofs

private theorem mate_paste
    {C A : Type*} [Category C] [Category A]
    {R : C ⥤ A} {L : A ⥤ C} (adj : R ⊣ L)
    {X Y : C} {N M : A} (f : X ⟶ Y) (b : Y ⟶ L.obj N)
    (d : X ⟶ L.obj M) (s : N ⟶ M) (h : f ≫ b ≫ L.map s = d) :
    R.map f ≫ (R.map b ≫ adj.counit.app N) ≫ s =
      R.map d ≫ adj.counit.app M := by
  have he := adj.counit.naturality s
  dsimp only [Functor.comp_map, Functor.id_map] at he
  calc
    _ = R.map f ≫ R.map b ≫ R.map (L.map s) ≫ adj.counit.app M := by
      simp only [Category.assoc]
      rw [← he]
    _ = R.map (f ≫ b ≫ L.map s) ≫ adj.counit.app M := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [h]

private theorem mate_identity
    {C A : Type*} [Category C] [Category A]
    {R : C ⥤ A} {L : A ⥤ C} (adj : R ⊣ L)
    {X Y : C} {N : A} (b : X ⟶ L.obj N) (t : N ⟶ R.obj Y)
    (v : X ⟶ Y) (h : b ≫ L.map t = v ≫ adj.unit.app Y) :
    (R.map b ≫ adj.counit.app N) ≫ t = R.map v := by
  have hn := adj.counit.naturality t
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Category.assoc, ← hn]
  rw [← Category.assoc, ← R.map_comp, h, R.map_comp, Category.assoc,
    adj.left_triangle_components]
  simp

private theorem map_injective_at
    {C A : Type*} [Category C] [Category A]
    {R : C ⥤ A} {L : A ⥤ C} (adj : R ⊣ L)
    {X Y : C} [Mono (adj.unit.app Y)] {f g : X ⟶ Y}
    (h : R.map f = R.map g) : f = g := by
  apply (cancel_mono (adj.unit.app Y)).1
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  dsimp only [Functor.comp_map, Functor.id_map] at hf hg
  rw [hf, hg, h]

private theorem transport_unit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (F : C ⥤ D) (G : A ⥤ B) (P : C ⥤ A) (Q : D ⥤ B)
    (S : C ⥤ C) (T : D ⥤ D) (s : A ⥤ A) (t : B ⥤ B)
    (c : F ⋙ Q ⟶ P ⋙ G) (cS : S ⋙ P ⟶ P ⋙ s) (cT : T ⋙ Q ⟶ Q ⋙ t)
    (k : G ⋙ t ⟶ s ⋙ G) (es : s ⟶ 𝟭 A) (et : t ⟶ 𝟭 B)
    (K : C) (a : T.obj (F.obj K) ⟶ F.obj (S.obj K))
    (eS : S.obj K ⟶ K) (eT : T.obj (F.obj K) ⟶ F.obj K)
    (hS : cS.app K ≫ es.app (P.obj K) = P.map eS)
    (hT : cT.app (F.obj K) ≫ et.app (Q.obj (F.obj K)) = Q.map eT)
    (hk : k.app (P.obj K) ≫ G.map (es.app (P.obj K)) = et.app (G.obj (P.obj K)))
    (ha : Q.map a ≫ c.app (S.obj K) ≫ G.map (cS.app K) =
      cT.app (F.obj K) ≫ t.map (c.app K) ≫ k.app (P.obj K))
    [Mono (c.app K)] : Q.map (a ≫ F.map eS) = Q.map eT := by
  apply (cancel_mono (c.app K)).1
  have hn := c.naturality eS
  have he := et.naturality (c.app K)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hn he
  rw [Q.map_comp, Category.assoc, hn]
  rw [← hS, G.map_comp]
  rw [reassoc_of% ha, hk, he]
  rw [← Category.assoc, hT]

private theorem mate_post
    {C A : Type*} [Category C] [Category A]
    {R : C ⥤ A} {L : A ⥤ C} (adj : R ⊣ L)
    {X : C} {N M : A} (b : X ⟶ L.obj N) (t : N ⟶ M) :
    R.map (b ≫ L.map t) ≫ adj.counit.app M =
      (R.map b ≫ adj.counit.app N) ≫ t := by
  have hn := adj.counit.naturality t
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [R.map_comp, Category.assoc, hn]
  simp only [Category.assoc]

private theorem transport_tower
    {C0 C1 C2 D0 D1 D2 A0 A1 A2 B0 B1 B2 : Type*}
    [Category C0] [Category C1] [Category C2] [Category D0] [Category D1] [Category D2]
    [Category A0] [Category A1] [Category A2] [Category B0] [Category B1] [Category B2]
    {P0 : C0 ⥤ A0} {P1 : C1 ⥤ A1} {P2 : C2 ⥤ A2}
    {Q0 : D0 ⥤ B0} {Q1 : D1 ⥤ B1} {Q2 : D2 ⥤ B2}
    {U0 : C0 ⥤ D0} {U1 : C1 ⥤ D1} {U2 : C2 ⥤ D2}
    {u0 : A0 ⥤ B0} {u1 : A1 ⥤ B1} {u2 : A2 ⥤ B2}
    {S : C0 ⥤ C1} {T : C1 ⥤ C2} {V : C0 ⥤ C2}
    {SX : D0 ⥤ D1} {TX : D1 ⥤ D2} {VX : D0 ⥤ D2}
    {s : A0 ⥤ A1} {t : A1 ⥤ A2} {v : A0 ⥤ A2}
    {sx : B0 ⥤ B1} {tx : B1 ⥤ B2} {vx : B0 ⥤ B2}
    (c0 : U0 ⋙ Q0 ⟶ P0 ⋙ u0) (c1 : U1 ⋙ Q1 ⟶ P1 ⋙ u1)
    (c2 : U2 ⋙ Q2 ⟶ P2 ⋙ u2)
    (cSX : SX ⋙ Q1 ⟶ Q0 ⋙ sx) (cTX : TX ⋙ Q2 ⟶ Q1 ⋙ tx)
    (cVX : VX ⋙ Q2 ⟶ Q0 ⋙ vx)
    (cSY : S ⋙ P1 ⟶ P0 ⋙ s) (cTY : T ⋙ P2 ⟶ P1 ⋙ t)
    (cVY : V ⋙ P2 ⟶ P0 ⋙ v)
    (kS : u0 ⋙ sx ⟶ s ⋙ u1) (kT : u1 ⋙ tx ⟶ t ⋙ u2)
    (kV : u0 ⋙ vx ⟶ v ⋙ u2)
    (bX : sx ⋙ tx ⟶ vx) (bY : s ⋙ t ⟶ v)
    (K : C0) (aS : SX.obj (U0.obj K) ⟶ U1.obj (S.obj K))
    (aT : TX.obj (U1.obj (S.obj K)) ⟶ U2.obj (T.obj (S.obj K)))
    (aV : VX.obj (U0.obj K) ⟶ U2.obj (V.obj K))
    (aX : TX.obj (SX.obj (U0.obj K)) ⟶ VX.obj (U0.obj K))
    (aY : T.obj (S.obj K) ⟶ V.obj K)
    (hS : Q1.map aS ≫ c1.app (S.obj K) ≫ u1.map (cSY.app K) =
      cSX.app (U0.obj K) ≫ sx.map (c0.app K) ≫ kS.app (P0.obj K))
    (hT : Q2.map aT ≫ c2.app (T.obj (S.obj K)) ≫ u2.map (cTY.app (S.obj K)) =
      cTX.app (U1.obj (S.obj K)) ≫ tx.map (c1.app (S.obj K)) ≫ kT.app (P1.obj (S.obj K)))
    (hV : Q2.map aV ≫ c2.app (V.obj K) ≫ u2.map (cVY.app K) =
      cVX.app (U0.obj K) ≫ vx.map (c0.app K) ≫ kV.app (P0.obj K))
    (hX : cTX.app (SX.obj (U0.obj K)) ≫ tx.map (cSX.app (U0.obj K)) ≫
      bX.app (Q0.obj (U0.obj K)) = Q2.map aX ≫ cVX.app (U0.obj K))
    (hY : cTY.app (S.obj K) ≫ t.map (cSY.app K) ≫ bY.app (P0.obj K) =
      P2.map aY ≫ cVY.app K)
    (hk : tx.map (kS.app (P0.obj K)) ≫ kT.app (s.obj (P0.obj K)) ≫
      u2.map (bY.app (P0.obj K)) = bX.app (u0.obj (P0.obj K)) ≫ kV.app (P0.obj K))
    [Mono (c2.app (V.obj K) ≫ u2.map (cVY.app K))] :
    Q2.map (TX.map aS ≫ aT ≫ U2.map aY) = Q2.map (aX ≫ aV) := by
  have hn2 := c2.naturality aY
  have hnT := cTX.naturality aS
  have hnk := kT.naturality (cSY.app K)
  have hnb := bX.naturality (c0.app K)
  dsimp only [Functor.comp_map] at hn2 hnT hnk hnb
  apply (cancel_mono (c2.app (V.obj K) ≫ u2.map (cVY.app K))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn2]
  rw [← u2.map_comp, ← hY, u2.map_comp, u2.map_comp]
  rw [reassoc_of% hT, reassoc_of% hnT, reassoc_of% hnk.symm]
  rw [← tx.map_comp_assoc, ← tx.map_comp_assoc]
  try simp only [Category.assoc]
  rw [hS]
  simp only [Functor.map_comp, Category.assoc]
  rw [hk, reassoc_of% hnb, reassoc_of% hX]
  rw [← hV]

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

private theorem system_scheme_unit
    (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)
    (hQ : IntegralQuotientMixedCoherence.{u, u} l)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (N : coefficientSequenceDerived l E X) :
    (integralComparisonSystemScalarPullback l E L ι (𝟙 X)).hom.app N ≫
        (integralComparisonSystemUnit l L X).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) =
      (integralComparisonDerivedSequenceScalar l E L ι X).map
        ((integralComparisonSystemUnit l E X).hom.app N) := by
  apply mixed_unit_of_composition
    (integralComparisonDerivedSequencePullback l E (𝟙 X))
    (integralComparisonDerivedSequencePullback l L (𝟙 X))
    (integralComparisonDerivedSequenceScalar l E L ι X)
    (integralComparisonSystemUnit l E X) (integralComparisonSystemUnit l L X)
    ((eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
      (Category.id_comp (𝟙 X)))).symm ≪≫
      integralComparisonSystemComposition l E (𝟙 X) (𝟙 X))
    ((eqToIso (congrArg (integralComparisonDerivedSequencePullback l L)
      (Category.id_comp (𝟙 X)))).symm ≪≫
      integralComparisonSystemComposition l L (𝟙 X) (𝟙 X))
    (integralComparisonSystemScalarPullback l E L ι (𝟙 X))
  · intro J
    have h := NatTrans.congr_app (hQ.derived_unital E (𝟙 X)).2 J
    change (integralComparisonSystemComposition l E (𝟙 X) (𝟙 X)).hom.app J ≫
      (integralComparisonDerivedSequencePullback l E (𝟙 X)).map
        ((integralComparisonSystemUnit l E X).hom.app J) =
      (eqToHom (congrArg (integralComparisonDerivedSequencePullback l E)
        (Category.id_comp (𝟙 X)))).app J at h
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app]
    rw [Category.assoc, h]
    simp only [eqToHom_refl, NatTrans.id_app]
    exact Category.id_comp _
  · intro J
    have h := NatTrans.congr_app (hQ.derived_unital L (𝟙 X)).2 J
    change (integralComparisonSystemComposition l L (𝟙 X) (𝟙 X)).hom.app J ≫
      (integralComparisonDerivedSequencePullback l L (𝟙 X)).map
        ((integralComparisonSystemUnit l L X).hom.app J) =
      (eqToHom (congrArg (integralComparisonDerivedSequencePullback l L)
        (Category.id_comp (𝟙 X)))).app J at h
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app]
    rw [Category.assoc, h]
    simp only [eqToHom_refl, NatTrans.id_app]
    exact Category.id_comp _
  · intro J
    have h := NatTrans.congr_app (hQ.derived_mixed E L ι (𝟙 X) (𝟙 X)) J
    have ht := exchange_congr (integralComparisonDerivedSequencePullback l E)
      (integralComparisonDerivedSequencePullback l L)
      (integralComparisonDerivedSequenceScalar l E L ι X)
      (fun f ↦ (integralComparisonSystemScalarPullback l E L ι f).hom)
      (Category.id_comp (𝟙 X)).symm J
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app]
    simp only [Functor.map_comp, Category.assoc]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at h
    rw [h, ← Category.assoc, ht]
    simp only [Category.assoc]

section Coordinates
variable (l : ℕ) [Fact l.Prime] (D : IntegralComparisonSystem.{u} l)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private abbrev pullC {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  integralComparisonPullbackCounit l E f ((D.coefficient E).system Y)
    ((D.coefficient E).system X) ((D.coefficient E).roos X)
    ((D.coefficient E).pullback f)

private abbrev scalarC (X : Scheme.{u}) :
    integralScalarExtension l E L ι X ⋙ ((D.coefficient L).system X).reduction ⟶
      ((D.coefficient E).system X).reduction ⋙
        integralComparisonDerivedSequenceScalar l E L ι X :=
  integralComparisonScalarCounit l E L ι X ((D.coefficient E).system X)
    ((D.coefficient L).system X) ((D.coefficient L).roos X) ((D.scalar E L ι).model X)

private theorem scalar_obj (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    ((integralComparisonConstructibleScalar l E L ι X).obj K).obj =
      (integralScalarExtension l E L ι X).obj K.obj := rfl

private theorem pull_obj {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    ((constructibleIntegralPullback l E f).obj K).obj =
      (integralDerivedPullback l E f).obj K.obj := rfl

private theorem mixed_counit {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    ((D.coefficient L).system X).reduction.map
        (integralComparisonScalar l E L ι D f K).hom ≫
      (pullC l D L f).app ((integralScalarExtension l E L ι Y).obj K.obj) ≫
      (integralComparisonDerivedSequencePullback l L f).map
        ((scalarC l D E L ι Y).app K.obj) =
    (scalarC l D E L ι X).app ((integralDerivedPullback l E f).obj K.obj) ≫
      (integralComparisonDerivedSequenceScalar l E L ι X).map
        ((pullC l D E f).app K.obj) ≫
      (integralComparisonSystemScalarPullback l E L ι f).hom.app
        (((D.coefficient E).system Y).reduction.obj K.obj) := by
  let A := integralComparisonScalar l E L ι D f K
  let B := ((D.coefficient L).pullback f).realization.hom.app
    ((integralScalarExtension l E L ι Y).obj K.obj)
  let C := ((D.scalar E L ι).model X).realization.hom.app
    ((integralDerivedPullback l E f).obj K.obj)
  let F := coefficientSequenceLimit l L X
  let s := (integralComparisonDerivedSequencePullback l L f).map
    ((scalarC l D E L ι Y).app K.obj)
  let t := (integralComparisonDerivedSequenceScalar l E L ι X).map
    ((pullC l D E f).app K.obj)
  let k := (integralComparisonSystemScalarPullback l E L ι f).app
    (((D.coefficient E).system Y).reduction.obj K.obj)
  have raw : A.hom ≫ B ≫ F.map s = C ≫ F.map (t ≫ k.hom) := by
    have hh : A.hom ≫ (integralComparisonMu l E L ι D f K).hom =
        (integralComparisonLambda l E L ι D f K).hom := by
      dsimp only [A, integralComparisonScalar, Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh' := hh =≫ F.map k.hom
    dsimp only [integralComparisonMu, integralComparisonLambda, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, asIso_hom] at hh'
    simp only [Category.assoc] at hh'
    change A.hom ≫ B ≫ F.map s ≫ F.map k.inv ≫ F.map k.hom =
      C ≫ F.map t ≫ F.map k.hom at hh'
    simpa only [Functor.comp_obj, Category.assoc, ← F.map_comp, k.inv_hom_id,
      F.map_id, Category.comp_id] using hh'
  have hp := mate_paste ((D.coefficient L).system X).adjunction
    A.hom B (C ≫ F.map (t ≫ k.hom)) s raw
  rw [mate_post ((D.coefficient L).system X).adjunction C (t ≫ k.hom)] at hp
  simpa only [A, B, C, s, t, k, pullC, scalarC, integralComparisonPullbackCounit,
    integralComparisonScalarCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Iso.app_hom, Category.assoc] using hp

private theorem pull_identity (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X) :
    (pullC l D E (𝟙 X)).app K.obj ≫
      (integralComparisonSystemUnit l E X).hom.app
        (((D.coefficient E).system X).reduction.obj K.obj) =
    ((D.coefficient E).system X).reduction.map (integralComparisonUnit l E D X K).hom := by
  apply mate_identity ((D.coefficient E).system X).adjunction
  dsimp only [integralComparisonUnit, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_inv, asIso_hom, Iso.app_hom]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem scheme_identity (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralComparisonScalar l E L ι D (𝟙 X) K).hom ≫
        (integralComparisonUnit l L D X
          ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom =
      (integralScalarExtension l E L ι X).map (integralComparisonUnit l E D X K).hom := by
  let A := integralComparisonScalar l E L ι D (𝟙 X) K
  let k := integralComparisonSystemScalarPullback l E L ι (𝟙 X)
  let R := ((D.coefficient L).system X).reduction
  let G := integralComparisonDerivedSequenceScalar l E L ι X
  let := (D.scalar E L ι).effective X K
  have : IsIso (((D.coefficient L).system X).adjunction.unit.app
      ((integralScalarExtension l E L ι X).obj K.obj)) := by
    simpa only [scalar_obj] using (D.coefficient L).complete X
      ((integralComparisonConstructibleScalar l E L ι X).obj K)
  have hi : A.inv ≫ (integralScalarExtension l E L ι X).map
      (integralComparisonUnit l E D X K).hom =
      (integralComparisonUnit l L D X
        ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom := by
    apply map_injective_at ((D.coefficient L).system X).adjunction
    apply transport_unit
      (integralScalarExtension l E L ι X) G
      ((D.coefficient E).system X).reduction R
      (integralDerivedPullback l E (𝟙 X)) (integralDerivedPullback l L (𝟙 X))
      (integralComparisonDerivedSequencePullback l E (𝟙 X))
      (integralComparisonDerivedSequencePullback l L (𝟙 X))
      (scalarC l D E L ι X) (pullC l D E (𝟙 X)) (pullC l D L (𝟙 X))
      k.inv (integralComparisonSystemUnit l E X).hom
      (integralComparisonSystemUnit l L X).hom K.obj
    · exact pull_identity l D E X K
    · exact pull_identity l D L X ((integralComparisonConstructibleScalar l E L ι X).obj K)
    · apply (cancel_epi (k.hom.app
        (((D.coefficient E).system X).reduction.obj K.obj))).1
      simp only [Iso.hom_inv_id_app_assoc]
      exact (system_scheme_unit l E L ι (integralQuotientMixedCoherence.{u, u} l)
        X (((D.coefficient E).system X).reduction.obj K.obj)).symm
    · have hm := mixed_counit l D E L ι (𝟙 X) K
      apply (cancel_epi (R.map A.hom)).1
      simp only [← R.map_comp_assoc, A.hom_inv_id, R.map_id,
        Category.id_comp]
      rw [reassoc_of% hm]
      simp only [k, G, Functor.comp_obj, Iso.hom_inv_id_app, Category.comp_id]
  change A.hom ≫ _ = _
  apply (cancel_epi A.inv).1
  simpa only [← Category.assoc, A.inv_hom_id, Category.id_comp] using hi.symm

private theorem scalar_identity {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonScalar l E E (AlgHom.id ℚ_[l] E) D f K).hom ≫
        (integralDerivedPullback l E f).map (integralComparisonScalarUnit l E Y K).hom =
      (integralComparisonScalarUnit l E X ((constructibleIntegralPullback l E f).obj K)).hom := by
  let := (D.coefficient E).effective f K
  have : IsIso (((D.coefficient E).system X).adjunction.unit.app
      ((integralDerivedPullback l E f).obj K.obj)) := by
    simpa only [pull_obj] using
      (D.coefficient E).complete X ((constructibleIntegralPullback l E f).obj K)
  apply map_injective_at ((D.coefficient E).system X).adjunction
  apply transport_unit
    (integralDerivedPullback l E f) (integralComparisonDerivedSequencePullback l E f)
    ((D.coefficient E).system Y).reduction ((D.coefficient E).system X).reduction
    (integralScalarExtension l E E (AlgHom.id ℚ_[l] E) Y)
    (integralScalarExtension l E E (AlgHom.id ℚ_[l] E) X)
    (integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) Y)
    (integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) X)
    (pullC l D E f) (scalarC l D E E (AlgHom.id ℚ_[l] E) Y)
    (scalarC l D E E (AlgHom.id ℚ_[l] E) X)
    (integralComparisonSystemScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom
    (integralComparisonSystemScalarUnit l E Y).hom
    (integralComparisonSystemScalarUnit l E X).hom K.obj
  · exact (integralScalarCounitNormalization l D).1 E Y K
  · exact (integralScalarCounitNormalization l D).1 E X
      ((constructibleIntegralPullback l E f).obj K)
  · exact NatTrans.congr_app ((integralQuotientMixedCoherence.{u, u} l).derived_scalar_unit E f)
      (((D.coefficient E).system Y).reduction.obj K.obj)
  · exact mixed_counit l D E E (AlgHom.id ℚ_[l] E) f K

private theorem scalar_tower
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    (integralScalarExtension l L M j X).map (integralComparisonScalar l E L ι D f K).hom ≫
        (integralComparisonScalar l L M j D f
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom ≫
        (integralDerivedPullback l M f).map
          (integralComparisonScalarAssociator l E L ι M j Y K).hom =
      (integralComparisonScalarAssociator l E L ι M j X
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
        (integralComparisonScalar l E M (j.comp ι) D f K).hom := by
  let KV := (integralComparisonConstructibleScalar l E M (j.comp ι) Y).obj K
  have : IsIso ((scalarC l D E M (j.comp ι) Y).app K.obj) :=
    (D.scalar E M (j.comp ι)).effective Y K
  have : IsIso ((pullC l D M f).app
      ((integralScalarExtension l E M (j.comp ι) Y).obj K.obj)) := by
    simpa only [KV, scalar_obj] using (D.coefficient M).effective f KV
  have : IsIso (((D.coefficient M).system X).adjunction.unit.app
      ((integralDerivedPullback l M f).obj
        ((integralScalarExtension l E M (j.comp ι) Y).obj K.obj))) := by
    simpa only [pull_obj, KV, scalar_obj] using
      (D.coefficient M).complete X ((constructibleIntegralPullback l M f).obj KV)
  apply map_injective_at ((D.coefficient M).system X).adjunction
  apply transport_tower
    (pullC l D E f) (pullC l D L f) (pullC l D M f)
    (scalarC l D E L ι X) (scalarC l D L M j X) (scalarC l D E M (j.comp ι) X)
    (scalarC l D E L ι Y) (scalarC l D L M j Y) (scalarC l D E M (j.comp ι) Y)
    (integralComparisonSystemScalarPullback l E L ι f).hom
    (integralComparisonSystemScalarPullback l L M j f).hom
    (integralComparisonSystemScalarPullback l E M (j.comp ι) f).hom
    (integralComparisonSystemScalarComposition l E L M ι j X).hom
    (integralComparisonSystemScalarComposition l E L M ι j Y).hom K.obj
  · exact mixed_counit l D E L ι f K
  · exact mixed_counit l D L M j f
      ((integralComparisonConstructibleScalar l E L ι Y).obj K)
  · exact mixed_counit l D E M (j.comp ι) f K
  · exact (integralScalarCounitNormalization l D).2 E L M ι j X
      ((constructibleIntegralPullback l E f).obj K)
  · exact (integralScalarCounitNormalization l D).2 E L M ι j Y K
  · exact NatTrans.congr_app
      ((integralQuotientMixedCoherence.{u, u} l).derived_scalar_tower E L ι M j f)
      (((D.coefficient E).system Y).reduction.obj K.obj)

end Coordinates
end Proofs

/-- The normalized mixed comparison respects scheme and coefficient units and towers.
Source: Stacks 06YY and 0941, scalar normalization in common-stage transport.
Proof: the scalar-model unit equation identifies multiplication with the whole
system scalar unitor after precomposition with chi. Its associativity equation
identifies the system associator with the ordinary derived tensor associator after
the same completion comparisons. The ordinary scalar models agree by their
balanced tensor generator formulas and universal derived counits. Cancel chi to
obtain the completed scalar unit and associator squares. Paste these squares
with the primitive mixed squares. Quotient scalar-unit and scalar-tower coherence
then give the coefficient identity and tower conclusions by cancellation of the
common word coordinate. For scheme identities derive the mixed-unit square from
the mixed-composition square at two identities and both geometric unit laws:
the identity pullback functor is isomorphic to the identity, hence faithful, so
cancelling its action gives the desired mixed unitor. Transport this square by
the counit coordinates. All equations include identity embeddings and zero inputs.
(blueprint: lem-trf-normalized-integral-scalar-coherence). -/
theorem normalizedIntegralScalarCoherence
    (l : ℕ) [Fact l.Prime] (D : IntegralComparisonSystem.{u} l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    (∀ (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X),
    (integralComparisonScalar l E L ι D (𝟙 X) K).hom ≫
        (integralComparisonUnit l L D X
          ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom =
      (integralScalarExtension l E L ι X).map (integralComparisonUnit l E D X K).hom) ∧
    (∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralComparisonScalar l E E (AlgHom.id ℚ_[l] E) D f K).hom ≫
        (integralDerivedPullback l E f).map (integralComparisonScalarUnit l E Y K).hom =
      (integralComparisonScalarUnit l E X ((constructibleIntegralPullback l E f).obj K)).hom) ∧
    (∀ (M : Type u) [Field M] [Algebra ℚ_[l] M]
    [FiniteDimensional ℚ_[l] M] (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y),
    (integralScalarExtension l L M j X).map (integralComparisonScalar l E L ι D f K).hom ≫
        (integralComparisonScalar l L M j D f
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom ≫
        (integralDerivedPullback l M f).map
          (integralComparisonScalarAssociator l E L ι M j Y K).hom =
      (integralComparisonScalarAssociator l E L ι M j X
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
        (integralComparisonScalar l E M (j.comp ι) D f K).hom) := by
  refine ⟨scheme_identity l D E L ι, scalar_identity l D E, ?_⟩
  intro M _ _ _ j X Y _ _ f K
  exact scalar_tower l D E L ι M j f K

end WeilConjectures
