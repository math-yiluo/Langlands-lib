/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalCompositionCoherence
import WeilConjectures.SmoothPurity.Common.CommonStageRationalCompositionNaturality
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality

/-! Fixed-stage square for the common-stage pullback/tensor composition representative.

Source: Stacks 07A4 and 0941, and the finite coefficient-field paragraph of the
common-stage composition proof.  At one coefficient field containing all stages,
the prescribed representative formulas reduce the two composites to the rational
pullback/tensor composition equation.  This theorem records that fixed-stage
calculation separately from the choice of a representative for the first route.
(blueprint: lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.StageSystem.PairCategory
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.StageHom
  commonStagePullbackObject commonStageTensorObject
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

private theorem tensor_map_heq {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B A' B' M N M' N' : C}
    (hA : A = M) (hB : B = N) (hA' : A' = M') (hB' : B' = N')
    {a : A ⟶ A'} {b : B ⟶ B'} {f : M ⟶ M'} {g : N ⟶ N'}
    (ha : HEq a f) (hb : HEq b g) :
    HEq (T.map (Prod.mkHom a b)) (T.map (Prod.mkHom f g)) := by
  cases hA; cases hB; cases hA'; cases hB'; cases ha; cases hb
  rfl

private theorem component_hom_heq {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (e : ∀ M, F.obj M ≅ G.obj M)
    {M N : C} (h : M = N) : HEq (e M).hom (e N).hom := by
  cases h
  rfl

private theorem comparison_hom_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D)
    (e : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    {M N M' N' : C} (hM : M = M') (hN : N = N') :
    HEq (e M N).hom (e M' N').hom := by
  cases hM; cases hN
  rfl

private theorem conjugated_composition
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (H : D ⥤ E) (G : C ⥤ E)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (W : E × E ⥤ E)
    (μF : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (μH : ∀ M N, H.obj (V.obj (M, N)) ≅ W.obj (H.obj M, H.obj N))
    (μG : ∀ M N, G.obj (U.obj (M, N)) ≅ W.obj (G.obj M, G.obj N))
    (γ : G ≅ F ⋙ H)
    (hn : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      H.map (V.map (Prod.mkHom a b)) ≫ (μH M' N').hom =
        (μH M N).hom ≫ W.map (Prod.mkHom (H.map a) (H.map b)))
    (hc : ∀ M N, (μG M N).hom ≫
      W.map (Prod.mkHom (γ.hom.app M) (γ.hom.app N)) =
      γ.hom.app (U.obj (M, N)) ≫ H.map (μF M N).hom ≫
        (μH (F.obj M) (F.obj N)).hom)
    {M N T : C} {FM FN FT TX : D} {GM GN GT HFT HTX HFM HFN B Z : E}
    (t : T ≅ U.obj (M, N)) (p : GT ≅ G.obj T)
    (fm : FM ≅ F.obj M) (fn : FN ≅ F.obj N) (ft : FT ≅ F.obj T)
    (tx : TX ≅ V.obj (FM, FN)) (gm : GM ≅ G.obj M) (gn : GN ≅ G.obj N)
    (hft : HFT ≅ H.obj FT) (htx : HTX ≅ H.obj TX)
    (hfm : HFM ≅ H.obj FM) (hfn : HFN ≅ H.obj FN)
    (b : B ≅ W.obj (GM, GN)) (z : Z ≅ W.obj (HFM, HFN)) :
    (p.hom ≫ G.map t.hom ≫ (μG M N).hom ≫
        W.map (Prod.mkHom gm.inv gn.inv) ≫ b.inv) ≫
      (b.hom ≫ W.map (Prod.mkHom
        (gm.hom ≫ γ.hom.app M ≫ H.map fm.inv ≫ hfm.inv)
        (gn.hom ≫ γ.hom.app N ≫ H.map fn.inv ≫ hfn.inv)) ≫ z.inv) =
    (p.hom ≫ γ.hom.app T ≫ H.map ft.inv ≫ hft.inv) ≫
      (hft.hom ≫ H.map (ft.hom ≫ F.map t.hom ≫ (μF M N).hom ≫
        V.map (Prod.mkHom fm.inv fn.inv) ≫ tx.inv) ≫ htx.inv) ≫
      (htx.hom ≫ H.map tx.hom ≫ (μH FM FN).hom ≫
        W.map (Prod.mkHom hfm.inv hfn.inv) ≫ z.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp_assoc ft.inv ft.hom, Iso.inv_hom_id, H.map_id, Category.id_comp]
  rw [← H.map_comp_assoc tx.inv tx.hom, Iso.inv_hom_id, H.map_id, Category.id_comp]
  rw [← W.map_comp_assoc]
  simp only [prod_comp, Iso.inv_hom_id_assoc]
  rw [reassoc_of% (hn fm.inv fn.inv)]
  rw [← reassoc_of% (γ.hom.naturality t.hom)]
  rw [← reassoc_of% (hc M N)]
  rw [← W.map_comp_assoc, ← W.map_comp_assoc]
  simp only [prod_comp, Category.assoc]

attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  commonStageTensorComparison commonStagePullbackComparison
  pullbackTensorRationalComposition canonicalRationalPullbackTensor

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/--
At a fixed common coefficient stage, the rational composition square identifies
the representative of the right route with any representative of the left route.

Source: Stacks 07A4 and 0941, finite coefficient representative calculation.
Proof: enlarge the coefficient field until it contains every object stage and the
chosen representative.  Expand common-stage pullback, tensor, comparison, and
composition maps using their prescribed formulas.  Adjacent comparison
isomorphisms cancel, leaving exactly
`canonicalRationalPullbackTensor_composition` at that finite coefficient.  The
rational composition theorem proves the resulting stage equality, and the
common-stage quotient constructor transports it to the displayed `HEq`.
(blueprint: lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation).
-/
theorem commonStageCompositionFiniteRepresentative_stageEquation {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedPullback l Ω (h ≫ f)).obj
      ((commonStageDerivedTensor l Ω Y).obj (M, N))).stage ≤ L)
    (hB : ((commonStageDerivedTensor l Ω Z).obj
      ((commonStageDerivedPullback l Ω h).obj
        ((commonStageDerivedPullback l Ω f).obj M),
        (commonStageDerivedPullback l Ω h).obj
          ((commonStageDerivedPullback l Ω f).obj N))).stage ≤ L)
    (r : ((commonStageDerivedPullback l Ω (h ≫ f)).obj
      ((commonStageDerivedTensor l Ω Y).obj (M, N))).toStage hA ⟶
      ((commonStageDerivedTensor l Ω Z).obj
        ((commonStageDerivedPullback l Ω h).obj
          ((commonStageDerivedPullback l Ω f).obj M),
          (commonStageDerivedPullback l Ω h).obj
            ((commonStageDerivedPullback l Ω f).obj N))).toStage hB)
    (hleft : HEq
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
          (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) M).hom)
          (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom)))
      (GeneralAlgebraicallyClosedCoefficients.ofHom _ _ L hA hB r)) :
    HEq
      (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
          (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M, N))).hom ≫
        ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
        ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom)
      (GeneralAlgebraicallyClosedCoefficients.ofHom _ _ L hA hB r) := by
  let F := commonStageDerivedPullback l Ω f
  let H := commonStageDerivedPullback l Ω h
  let G := commonStageDerivedPullback l Ω (h ≫ f)
  let TY := commonStageDerivedTensor l Ω Y
  let TX := commonStageDerivedTensor l Ω X
  let TZ := commonStageDerivedTensor l Ω Z
  let P := commonStagePullbackObject l Ω f
  let Q := commonStagePullbackObject l Ω h
  let R := commonStagePullbackObject l Ω (h ≫ f)
  let OY := commonStageTensorObject l Ω Y
  let OX := commonStageTensorObject l Ω X
  let OZ := commonStageTensorObject l Ω Z
  have ho {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)] (A) :
      (commonStageDerivedPullback l Ω g).obj A = commonStagePullbackObject l Ω g A := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 A
  have hot {W : Scheme.{u}} [∀ w : W, Invertible (l : W.residueField w)] (A B) :
      (commonStageDerivedTensor l Ω W).obj (A, B) = commonStageTensorObject l Ω W A B := by
    unfold commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 A B
  have hmap {A B A' B' : generalAlgebraicallyClosedConstructibleCategory l Ω X}
      (hA' : A = A') (hB' : B = B') (K : AlgebraicallyClosedCoefficients.Index l Ω)
      (ha : A'.stage ≤ K) (hb : B'.stage ≤ K)
      (a : A ⟶ B) (b : A'.toStage ha ⟶ B'.toStage hb)
      (he : HEq a (ofHom A' B' K ha hb b)) :
      HEq (H.map a) (ofHom (Q A') (Q B') K ha hb
        ((commonStagePullbackComparison l Ω h A' K ha).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) h).map b ≫
          (commonStagePullbackComparison l Ω h B' K hb).inv)) := by
    subst A B
    cases he
    exact (commonStageDerivedPullback_existsUnique l Ω h).exists.choose_spec.2
      A' B' K ha hb b
  let K := (OY M N).stage
  have hMN : (OY M N).stage ≤ K := le_rfl
  have hM : M.stage ≤ K :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1
  have hN : N.stage ≤ K :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2
  have hcomp (A : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (ha : A.stage ≤ K) :=
    (pullbackTensorCommonComposition_existsUnique l Ω f h A).exists.choose_spec K ha
  have hμ {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (A B : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (hab : (commonStageTensorObject l Ω W A B).stage ≤ K) :=
    (canonicalCommonStagePullbackTensor_existsUnique l Ω g A B).exists.choose_spec K hab
  have hcM := hcomp M hM
  have hcN := hcomp N hN
  have hcT := hcomp (OY M N) hMN
  have hμG := hμ (h ≫ f) M N hMN
  have hμF := hμ f M N hMN
  have hμH := hμ h (P M) (P N) hMN
  have hcT' := (component_hom_heq G (F ⋙ H)
    (pullbackTensorCommonComposition l Ω f h) (hot M N)).trans hcT
  have hμH' := (comparison_hom_heq H TX TZ
    (canonicalCommonStagePullbackTensor l Ω h) (ho f M) (ho f N)).trans hμH
  have hμFmap := hmap
    (show F.obj (TY.obj (M, N)) = P (OY M N) by rw [hot, ho])
    (show TX.obj (F.obj M, F.obj N) = OX (P M) (P N) by rw [ho f, ho f, hot])
    K hMN hMN _ _ hμF
  let ca (A : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (ha : A.stage ≤ K) :=
    (commonStagePullbackComparison l Ω (h ≫ f) A K ha).hom ≫
      (pullbackTensorRationalComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) f h (A.toStage ha)).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) h).map
        (commonStagePullbackComparison l Ω f A K ha).inv ≫
      (commonStagePullbackComparison l Ω h (P A) K ha).inv
  have htensor := (commonStageDerivedTensor_existsUnique l Ω Z).exists.choose_spec.2
    (R M) (R N) (Q (P M)) (Q (P N)) K hMN hMN (ca M hM) (ca N hN)
  have htensor' := (tensor_map_heq TZ (ho (h ≫ f) M) (ho (h ≫ f) N)
    (by rw [ho f, ho h]) (by rw [ho f, ho h]) hcM hcN).trans htensor
  have hA' : G.obj (TY.obj (M, N)) = R (OY M N) := by rw [hot, ho]
  have hB' : TZ.obj (G.obj M, G.obj N) = OZ (R M) (R N) := by rw [ho, ho, hot]
  have hC' : TZ.obj (H.obj (F.obj M), H.obj (F.obj N)) =
      OZ (Q (P M)) (Q (P N)) := by rw [ho f, ho f, ho h, ho h, hot]
  have hD' : H.obj (F.obj (TY.obj (M, N))) = Q (P (OY M N)) := by rw [hot, ho, ho]
  have hE' : H.obj (TX.obj (F.obj M, F.obj N)) = Q (OX (P M) (P N)) := by
    rw [ho f, ho f, hot, ho]
  have hl := heq_comp hA' hB' hC' hμG htensor'
  have hr := heq_comp hA' hD' hC' hcT' (heq_comp hD' hE' hC' hμFmap hμH')
  have hs : HEq
      ((canonicalCommonStagePullbackTensor l Ω (h ≫ f) M N).hom ≫
        TZ.map (Prod.mkHom (pullbackTensorCommonComposition l Ω f h M).hom
          (pullbackTensorCommonComposition l Ω f h N).hom))
      ((pullbackTensorCommonComposition l Ω f h (TY.obj (M, N))).hom ≫
        H.map (canonicalCommonStagePullbackTensor l Ω f M N).hom ≫
        (canonicalCommonStagePullbackTensor l Ω h (F.obj M) (F.obj N)).hom) := by
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ofHom _ _ K _ _ _ ≫ ofHom _ _ K _ _ _ =
      ofHom _ _ K _ _ _ ≫ (ofHom _ _ K _ _ _ ≫ ofHom _ _ K _ _ _)
    simp only [ofHom, mkHom_comp_mkHom]
    apply congrArg (ofHom _ _ K _ _)
    dsimp only [pullbackTensorAtCommonStage, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.prod_hom]
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K
    let γ : rationalDerivedPullback l E (h ≫ f) ≅
        rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E h :=
      NatIso.ofComponents (pullbackTensorRationalComposition l E f h)
        (fun a ↦ commonStageRationalComposition_naturality l E f h a)
    exact conjugated_composition
      (rationalDerivedPullback l E f) (rationalDerivedPullback l E h)
      (rationalDerivedPullback l E (h ≫ f))
      (rationalDerivedTensor l E Y) (rationalDerivedTensor l E X)
      (rationalDerivedTensor l E Z)
      (canonicalRationalPullbackTensor l E f) (canonicalRationalPullbackTensor l E h)
      (canonicalRationalPullbackTensor l E (h ≫ f)) γ
      (fun a b ↦ canonicalRationalPullbackTensor_naturality l E h a b)
      (pullbackTensorRationalCompositionCoherence l E f h)
      (commonStageTensorComparison l Ω Y M N K hMN)
      (commonStagePullbackComparison l Ω (h ≫ f) (OY M N) K hMN)
      (commonStagePullbackComparison l Ω f M K hM)
      (commonStagePullbackComparison l Ω f N K hN)
      (commonStagePullbackComparison l Ω f (OY M N) K hMN)
      (commonStageTensorComparison l Ω X (P M) (P N) K hMN)
      (commonStagePullbackComparison l Ω (h ≫ f) M K hM)
      (commonStagePullbackComparison l Ω (h ≫ f) N K hN)
      (commonStagePullbackComparison l Ω h (P (OY M N)) K hMN)
      (commonStagePullbackComparison l Ω h (OX (P M) (P N)) K hMN)
      (commonStagePullbackComparison l Ω h (P M) K hM)
      (commonStagePullbackComparison l Ω h (P N) K hN)
      (commonStageTensorComparison l Ω Z (R M) (R N) K hMN)
      (commonStageTensorComparison l Ω Z (Q (P M)) (Q (P N)) K hMN)
  exact hs.symm.trans hleft

end WeilConjectures
