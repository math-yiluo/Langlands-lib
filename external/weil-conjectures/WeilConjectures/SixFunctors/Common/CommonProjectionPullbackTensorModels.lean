/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorNaturality
public import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackStages
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorModelMap
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCoefficientUnit
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import all Mathlib.Logic.Small.Defs
/-! # The finite-model calculation for the common-stage tensor/pullback square -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option Elab.async false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.pairFunctorCoherent
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  StageSystem.instCategoryPairCategory Functor.category
attribute [local irreducible] StageSystem.PairCategory.categoryStruct rationalDerivedPullback
  rationalDerivedTensor commonStageDerivedPullback
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso
  canonicalRationalPullbackTensor GeneralAlgebraicallyClosedCoefficients.unitor
set_option allowUnsafeReducibility true in
attribute [local irreducible] ScalarLocalization.category
  ScalarLocalization.linear sfIntegralConstructible

private theorem replace_square_iso
    {A : Type*} [Category* A] {P Q R S : A}
    (f : P ⟶ Q) (a : R ≅ Q) (b c : S ≅ P) (μ : S ⟶ R)
    (h : f ≫ a.inv = b.inv ≫ μ) (he : c = b) :
    f ≫ a.inv = c.inv ≫ μ := by
  rw [he]
  exact h

private theorem representative_model_square
    {A B : Type*} [Category* A] [Category* B] (I : A ⥤ B)
    {M N M' N' : B} (hM : M = M') (hN : N = N')
    {P Q P' Q' : A} (a : M' ≅ I.obj P) (b : N' ≅ I.obj Q)
    (c : P ≅ P') (d : Q ≅ Q') (f : M ⟶ N) (g : P' ⟶ Q')
    (h : HEq f (a.hom ≫ I.map (c.hom ≫ g ≫ d.inv) ≫ b.inv)) :
    f ≫ (eqToIso hN ≪≫ b ≪≫ I.mapIso d).hom =
      (eqToIso hM ≪≫ a ≪≫ I.mapIso c).hom ≫ I.map g := by
  subst M' N'
  rw [eq_of_heq h]
  simp [Functor.map_comp, Category.assoc]

private theorem coefficient_unit_square
    {A B B' : Type*} [Category* A] [Category* B] [Category* B']
    (F : A ⥤ B) (J : B ⥤ B')
    (RY : A × A ⥤ A) (RX : B × B ⥤ B)
    {M N M' N' : A} {P Q : B} {K L : B'}
    (uM : M' ≅ M) (uN : N' ≅ N) (vM : P ≅ F.obj M) (vN : Q ≅ F.obj N)
    (p : P ≅ F.obj M') (q : Q ≅ F.obj N')
    (hp : p.hom ≫ F.map uM.hom = vM.hom)
    (hq : q.hom ≫ F.map uN.hom = vN.hom)
    (μ₀ : F.obj (RY.obj (M, N)) ⟶ RX.obj (F.obj M, F.obj N))
    (μ₁ : F.obj (RY.obj (M', N')) ⟶ RX.obj (F.obj M', F.obj N'))
    (hn : F.map (RY.map (Prod.mkHom uM.hom uN.hom)) ≫ μ₀ =
      μ₁ ≫ RX.map (Prod.mkHom (F.map uM.hom) (F.map uN.hom)))
    (a : K ≅ J.obj (F.obj (RY.obj (M', N')))) (b : L ≅ J.obj (RX.obj (P, Q)))
    (ν : K ⟶ L)
    (hm : ν ≫ b.hom = a.hom ≫
      J.map (μ₁ ≫ RX.map (Prod.mkHom p.inv q.inv))) :
    J.map μ₀ ≫ (b ≪≫ J.mapIso (RX.mapIso (Iso.prod vM vN))).inv =
      (a ≪≫ J.mapIso (F.mapIso (RY.mapIso (Iso.prod uM uN)))).inv ≫ ν := by
  have hp' : p.inv ≫ vM.hom = F.map uM.hom := by
    rw [← hp, Iso.inv_hom_id_assoc]
  have hq' : q.inv ≫ vN.hom = F.map uN.hom := by
    rw [← hq, Iso.inv_hom_id_assoc]
  have hu : RX.map (Prod.mkHom p.inv q.inv) ≫
      RX.map (Prod.mkHom vM.hom vN.hom) =
      RX.map (Prod.mkHom (F.map uM.hom) (F.map uN.hom)) := by
    rw [← RX.map_comp]
    congr 1
    ext <;> dsimp <;> assumption
  have hh : ν ≫ (b ≪≫ J.mapIso (RX.mapIso (Iso.prod vM vN))).hom =
      (a ≪≫ J.mapIso (F.mapIso (RY.mapIso (Iso.prod uM uN)))).hom ≫ J.map μ₀ := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
    calc
      ν ≫ (b.hom ≫ J.map (RX.map (Prod.mkHom vM.hom vN.hom))) =
          a.hom ≫ J.map ((μ₁ ≫ RX.map (Prod.mkHom p.inv q.inv)) ≫
            RX.map (Prod.mkHom vM.hom vN.hom)) := by
        rw [← Category.assoc, hm]
        simp only [Functor.map_comp, Category.assoc]
      _ = a.hom ≫ J.map (μ₁ ≫
          RX.map (Prod.mkHom (F.map uM.hom) (F.map uN.hom))) := by
        rw [Category.assoc, hu]
      _ = a.hom ≫ J.map (F.map (RY.map (Prod.mkHom uM.hom uN.hom)) ≫ μ₀) := by
        rw [hn]
      _ = _ := by simp only [Functor.map_comp, Category.assoc]
  apply (cancel_mono (b ≪≫ J.mapIso (RX.mapIso (Iso.prod vM vN))).hom).1
  apply (cancel_epi
    ((a ≪≫ J.mapIso (F.mapIso (RY.mapIso (Iso.prod uM uN)))).hom)).1
  simpa only [Functor.map_comp, Category.assoc, Iso.inv_hom_id,
    Functor.map_id, Category.comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.id_comp] using hh.symm

private theorem five_iso_hom
    {A : Type*} [Category* A] {K₀ K₁ K₂ K₃ K₄ K₅ : A}
    (a : K₀ ≅ K₁) (b : K₁ ≅ K₂) (c : K₂ ≅ K₃) (d : K₃ ≅ K₄) (e : K₅ ≅ K₄) :
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e.symm).hom =
      (a ≪≫ b).hom ≫ (c.hom ≫ d.hom) ≫ e.inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]

private theorem stage_mapIso_trans
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A B : I → Type*} [∀ i, Category* (A i)] [∀ i, Category* (B i)]
    {S : StageSystem A} {T : StageSystem B} (F : S.Morphism T) (i : I)
    {K : S.PairCategory} {P Q : A i} (a : K ≅ (S.ι i).obj P) (b : P ≅ Q) :
    F.functor.mapIso (a ≪≫ (S.ι i).mapIso b) =
      F.functor.mapIso a ≪≫ (T.ι i).mapIso ((F.Φ i).mapIso b) := by
  apply Iso.ext
  change F.functor.map (a.hom ≫ (S.ι i).map b.hom) =
    F.functor.map a.hom ≫ (T.ι i).map ((F.Φ i).map b.hom)
  rw [Functor.map_comp, F.functor_map_ι]

private theorem inclusionTensorModel_pullback_square
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hc : StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun L ↦ rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω L) f)
      (commonStagePullbackTransition l Ω f))
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (M N : Stage l Ω Y E)
    (μ : (StageSystem.Morphism.functor
      (commonProjectionPullbackStages l Ω f hc)).obj ((commonStageDerivedTensor l Ω Y).obj
          ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M, (inclusion (l := l) (Ω := Ω) (Y := Y)
          E).obj N)) ⟶
      (commonStageDerivedTensor l Ω X).obj ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj
          ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).obj
          M), (inclusion (l := l) (Ω := Ω) (Y := X) E).obj ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).obj N)))
    (hrep : HEq μ
      (ofHom
        (commonStagePullbackObject l Ω f
          (commonStageTensorObject l Ω Y ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M)
              ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj N)))
        (commonStageTensorObject l Ω X
          (commonStagePullbackObject l Ω f ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M))
          (commonStagePullbackObject l Ω f ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj N)))
        E (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)
        (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)
        (pullbackTensorAtCommonStage l Ω f ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M)
            ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj N) E
          (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)).hom)) :
  let G := (commonProjectionPullbackStages l Ω f hc).functor
  let F := rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
  let IY := inclusion (l := l) (Ω := Ω) (Y := Y) E
  let IX := inclusion (l := l) (Ω := Ω) (Y := X) E
  let P := IY.obj M
  let Q := IY.obj N
  let g := (canonicalRationalPullbackTensor l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
      (P.toStage (le_rfl : E ≤ E)) (Q.toStage (le_rfl : E ≤ E))).hom ≫
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) X).map
      (Prod.mkHom (commonStagePullbackComparison l Ω f P E le_rfl).inv
        (commonStagePullbackComparison l Ω f Q E le_rfl).inv)
  μ ≫ (commonInclusionTensorModel l Ω X E (F.obj M) (F.obj N)).hom =
    G.map (commonInclusionTensorModel l Ω Y E M N).hom ≫ IX.map g := by
  dsimp only
  let G := (commonProjectionPullbackStages l Ω f hc).functor
  let F := rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
  let IY := inclusion (l := l) (Ω := Ω) (Y := Y) E
  let IX := inclusion (l := l) (Ω := Ω) (Y := X) E
  let P := IY.obj M
  let Q := IY.obj N
  let O := commonStageTensorObject l Ω Y P Q
  let O' := commonStageTensorObject l Ω X
    (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q)
  have h : O.stage ≤ E := by
    change E.val ⊔ E.val ≤ E.val
    exact sup_le le_rfl le_rfl
  let c := commonStagePullbackComparison l Ω f O E h ≪≫
    F.mapIso (commonStageTensorComparison l Ω Y P Q E h)
  let d := commonStageTensorComparison l Ω X
    (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q) E h
  let g := (canonicalRationalPullbackTensor l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
      (P.toStage (le_rfl : E ≤ E)) (Q.toStage (le_rfl : E ≤ E))).hom ≫
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) X).map
      (Prod.mkHom (commonStagePullbackComparison l Ω f P E le_rfl).inv
        (commonStagePullbackComparison l Ω f Q E le_rfl).inv)
  have he : (pullbackTensorAtCommonStage l Ω f P Q E h).hom =
      c.hom ≫ g ≫ d.inv := by
    exact five_iso_hom
      (commonStagePullbackComparison l Ω f O E h)
      (F.mapIso (commonStageTensorComparison l Ω Y P Q E h))
      (canonicalRationalPullbackTensor l
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f _ _)
      ((rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) X).mapIso
        (Iso.prod (commonStagePullbackComparison l Ω f P E le_rfl).symm
          (commonStagePullbackComparison l Ω f Q E le_rfl).symm)) d
  have hr := StageSystem.mkHom_eq_isoToStage (S := stageSystem l Ω X) h h
    (pullbackTensorAtCommonStage l Ω f P Q E h).hom
  rw [he] at hr
  have hre : HEq μ
      (((stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f O) h).hom ≫
        IX.map (c.hom ≫ g ≫ d.inv) ≫
          ((stageSystem l Ω X).isoToStage O' h).inv) := by
    rw [he] at hrep
    exact hrep.trans (heq_of_eq hr)
  have hm := representative_model_square IX
    (congrArg G.obj ((commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 P Q))
    ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1
      (IX.obj (F.obj M)) (IX.obj (F.obj N)))
    ((stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f O) h)
    ((stageSystem l Ω X).isoToStage O' h) c d μ g hre
  have hmodel : μ ≫ (commonInclusionTensorModel l Ω X E (F.obj M) (F.obj N)).hom =
      G.map (commonInclusionTensorModel l Ω Y E M N).hom ≫ IX.map g := by
    rw [commonProjectionPullbackTensorModelMap l Ω f hc E M N]
    unfold commonInclusionTensorModel
    exact hm
  exact hmodel

attribute [local irreducible] commonStageDerivedTensor

private theorem inclusionTensorComparison_hom
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) (M N : Stage l Ω W E) :
    let I := inclusion (l := l) (Ω := Ω) (Y := W) E
    let R := rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) W
    let U := operationStageTransitionIso l Ω W E E le_rfl ≪≫ unitor l Ω W E
    (commonInclusionTensorComparison l Ω W E).hom.app (M, N) =
      (commonInclusionTensorModel l Ω W E M N ≪≫
        I.mapIso (R.mapIso (Iso.prod (U.app M) (U.app N)))).inv := by
  unfold commonInclusionTensorComparison
  rfl

private theorem model_square_to_components
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P Q : C} {R S : D} (a : R ≅ S) (b : P ≅ Q)
    (f : G.obj Q ⟶ S) (μ : G.obj P ⟶ R) (tx : S ⟶ R) (ty : Q ⟶ P)
    (hx : tx = a.inv) (hy : ty = b.inv)
    (h : f ≫ a.inv = (G.mapIso b).inv ≫ μ) :
    f ≫ tx = G.map ty ≫ μ := by
  rw [hx, hy]
  exact h

/-- The finite representative yields the square on included objects.
Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-projection-inclusion-pullback-tensor-square).
Proof: apply the stage-morphism coherence law to the change-of-stage isomorphism.
The representative formula then identifies the two composites between the finite
models of the common tensors. Rational pullback/tensor naturality moves the two
source coefficient-unit maps through the rational comparison. The coefficient-unit
identity identifies their pullbacks with the two target coefficient-unit maps.
Cancel the tensor-model isomorphisms to obtain the displayed square. -/
theorem commonProjectionInclusionPullbackTensorSquare
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hc : StageSystem.pairFunctorCoherent (stageSystem l Ω Y) (stageSystem l Ω X)
      (fun L ↦ rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω L) f)
      (commonStagePullbackTransition l Ω f))
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (M N : Stage l Ω Y E)
    (μ : (StageSystem.Morphism.functor
      (commonProjectionPullbackStages l Ω f hc)).obj ((commonStageDerivedTensor l Ω Y).obj
          ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M, (inclusion (l := l) (Ω := Ω) (Y := Y)
          E).obj N)) ⟶
      (commonStageDerivedTensor l Ω X).obj ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj
          ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).obj
          M), (inclusion (l := l) (Ω := Ω) (Y := X) E).obj ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).obj N)))
    (hrep : HEq μ
      (ofHom
        (commonStagePullbackObject l Ω f
          (commonStageTensorObject l Ω Y ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M)
              ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj N)))
        (commonStageTensorObject l Ω X
          (commonStagePullbackObject l Ω f ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M))
          (commonStagePullbackObject l Ω f ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj N)))
        E (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)
        (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)
        (pullbackTensorAtCommonStage l Ω f ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M)
            ((inclusion (l := l) (Ω := Ω) (Y := Y) E).obj N) E
          (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)).hom)) :
    (inclusion (l := l) (Ω := Ω) (Y := X) E).map ((canonicalRationalPullbackTensor l
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f M N).hom) ≫
      (commonInclusionTensorComparison l Ω X E).hom.app ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).obj M,(rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f).obj N) =
    (StageSystem.Morphism.functor
      (commonProjectionPullbackStages l Ω f hc)).map ((commonInclusionTensorComparison l Ω Y
          E).hom.app (M,N)) ≫ μ := by
  let G := (commonProjectionPullbackStages l Ω f hc).functor
  let F : Stage l Ω Y E ⥤ Stage l Ω X E :=
    rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
  let IY := inclusion (l := l) (Ω := Ω) (Y := Y) E
  let IX := inclusion (l := l) (Ω := Ω) (Y := X) E
  let P := IY.obj M
  let Q := IY.obj N
  have hmodel := inclusionTensorModel_pullback_square l Ω f hc E M N μ hrep
  let RY : Stage l Ω Y E × Stage l Ω Y E ⥤ Stage l Ω Y E :=
    rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) Y
  let RX : Stage l Ω X E × Stage l Ω X E ⥤ Stage l Ω X E :=
    rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) X
  let UY := operationStageTransitionIso l Ω Y E E le_rfl ≪≫ unitor l Ω Y E
  let UX := operationStageTransitionIso l Ω X E E le_rfl ≪≫ unitor l Ω X E
  have huMP := commonStagePullbackComparison_self_unit l Ω f P
  have huNP := commonStagePullbackComparison_self_unit l Ω f Q
  have huM := congrArg Iso.hom huMP
  have huN := congrArg Iso.hom huNP
  have hh := coefficient_unit_square F IX RY RX
    (UY.app M) (UY.app N) (UX.app (F.obj M)) (UX.app (F.obj N))
    (commonStagePullbackComparison l Ω f P E le_rfl)
    (commonStagePullbackComparison l Ω f Q E le_rfl) huM huN
    (canonicalRationalPullbackTensor l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f M N).hom
    (canonicalRationalPullbackTensor l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
      (P.toStage (le_rfl : E ≤ E)) (Q.toStage (le_rfl : E ≤ E))).hom
    (canonicalRationalPullbackTensor_naturality l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f
      (UY.hom.app M) (UY.hom.app N))
    (G.mapIso (commonInclusionTensorModel l Ω Y E M N))
    (commonInclusionTensorModel l Ω X E (F.obj M) (F.obj N)) μ hmodel
  have heq := stage_mapIso_trans (commonProjectionPullbackStages l Ω f hc) E
    (commonInclusionTensorModel l Ω Y E M N)
    (RY.mapIso (Iso.prod (UY.app M) (UY.app N)))
  change G.mapIso (commonInclusionTensorModel l Ω Y E M N ≪≫
      IY.mapIso (RY.mapIso (Iso.prod (UY.app M) (UY.app N)))) =
    G.mapIso (commonInclusionTensorModel l Ω Y E M N) ≪≫
      IX.mapIso (F.mapIso (RY.mapIso (Iso.prod (UY.app M) (UY.app N)))) at heq
  have hh' := replace_square_iso _ _ _ _ μ hh heq
  exact model_square_to_components G
    (commonInclusionTensorModel l Ω X E (F.obj M) (F.obj N) ≪≫
      IX.mapIso (RX.mapIso (Iso.prod (UX.app (F.obj M)) (UX.app (F.obj N)))))
    (commonInclusionTensorModel l Ω Y E M N ≪≫
      IY.mapIso (RY.mapIso (Iso.prod (UY.app M) (UY.app N))))
    (IX.map (canonicalRationalPullbackTensor l
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f M N).hom) μ _ _
    (inclusionTensorComparison_hom l Ω X E (F.obj M) (F.obj N))
    (inclusionTensorComparison_hom l Ω Y E M N) hh'

end WeilConjectures
