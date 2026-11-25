/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExchangeProjectionSquares
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCompactificationExchangeSquare
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCanonicalIsoSquare
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares

/-! # Ordinary coefficient squares for compactification composites

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp ringedSquare Compositors.square

private theorem proper_projection_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
    (L : Integral l E U.left) (H : Integral l E V.left) :
    (ordinaryTensorReduction l E a.ringedModels V.left).app
        ((ringedPush l E f.left).obj L, H) ≫
      (calculus l E V.left).systemClosed.tensor.map
        (Prod.mkHom ((ordinaryPushReduction l E o a.realizationModel f.left).app L) (𝟙 _)) ≫
      ((properProjection l E o f.left).app ((calculus l E U.left).reduction.obj L)).app
        ((calculus l E V.left).reduction.obj H) =
    (calculus l E V.left).reduction.map
      (((ringedProperProjection l E a.ringedModels f.left).app L).app H) ≫
    (ordinaryPushReduction l E o a.realizationModel f.left).app
      ((a.ringedModels.tensor U.left).ordinary.tensor.obj
        (L, (ringedPull l E f.left).obj H)) ≫
    (Operations.push l E o f.left).map
      ((ordinaryTensorReduction l E a.ringedModels U.left).app
          (L, (ringedPull l E f.left).obj H) ≫
        (calculus l E U.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((a.realizationModel.reductionPull f.left).hom.app H))) := by
  let X₀ : ULift.{u} Bool → Over B := fun b ↦ match b.down with
    | false => U
    | true => V
  let K₀ : ∀ b, Integral l E (X₀ b).left := fun b ↦ match b with
    | ⟨false⟩ => L
    | ⟨true⟩ => H
  have h := (ordinaryExchangeProjectionSquares l E o a (X := X₀) K₀).2 f hf
    (.var (⟨false⟩ : ULift.{u} Bool)) (.var (⟨true⟩ : ULift.{u} Bool))
  dsimp only [Expression.ordinaryReduction, Expression.ringedObj, Expression.systemObj,
    Expression.evaluate, ringedInterpretation, systemInterpretation, Functor.comp_obj,
    Functor.prod'_obj, Pi.eval, inputReduction, Functor.pi, X₀, K₀] at h
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc] using h

private theorem proper_projection_coeff_natural
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
    (L : Integral l E U.left) (H : Integral l E V.left)
    (M : System l E U.left) (N : System l E V.left)
    (q : (calculus l E U.left).reduction.obj L ⟶ M)
    (r : (calculus l E V.left).reduction.obj H ⟶ N) :
    (ordinaryTensorReduction l E a.ringedModels V.left).app
        ((ringedPush l E f.left).obj L, H) ≫
      (calculus l E V.left).systemClosed.tensor.map
        (Prod.mkHom
          ((ordinaryPushReduction l E o a.realizationModel f.left).app L ≫
            (Operations.push l E o f.left).map q) r) ≫
      ((properProjection l E o f.left).app M).app N =
    (calculus l E V.left).reduction.map
      (((ringedProperProjection l E a.ringedModels f.left).app L).app H) ≫
    (ordinaryPushReduction l E o a.realizationModel f.left).app
      ((a.ringedModels.tensor U.left).ordinary.tensor.obj
        (L, (ringedPull l E f.left).obj H)) ≫
    (Operations.push l E o f.left).map
      ((ordinaryTensorReduction l E a.ringedModels U.left).app
          (L, (ringedPull l E f.left).obj H) ≫
        (calculus l E U.left).systemClosed.tensor.map
          (Prod.mkHom q ((a.realizationModel.reductionPull f.left).hom.app H ≫
            (pull l E f.left).map r))) := by
  have hp := proper_projection_coeff l E o a f hf L H
  have hn := (Functor.uncurry.map (properProjection l E o f.left)).naturality
    (Prod.mkHom q r)
  have hn' : (calculus l E V.left).systemClosed.tensor.map
      (Prod.mkHom ((Operations.push l E o f.left).map q) r) ≫
      ((properProjection l E o f.left).app M).app N =
    ((properProjection l E o f.left).app ((calculus l E U.left).reduction.obj L)).app
      ((calculus l E V.left).reduction.obj H) ≫
    (Operations.push l E o f.left).map
      ((calculus l E U.left).systemClosed.tensor.map
        (Prod.mkHom q ((pull l E f.left).map r))) := by
    simpa [Functor.uncurry_obj_map, Functor.curryObj,
      ← CategoryTheory.Functor.map_comp] using! hn
  let T := (calculus l E V.left).systemClosed.tensor
  have hfactor : T.map
      (Prod.mkHom
        ((ordinaryPushReduction l E o a.realizationModel f.left).app L ≫
          (Operations.push l E o f.left).map q) r) =
    T.map (Prod.mkHom ((ordinaryPushReduction l E o a.realizationModel f.left).app L)
      (𝟙 _)) ≫
    T.map (Prod.mkHom ((Operations.push l E o f.left).map q) r) := by
    simp only [← T.map_comp, prod_comp, Category.id_comp]
  dsimp only [T] at hfactor
  conv_lhs =>
    rhs
    lhs
    erw [hfactor]
  simp only [Category.assoc]
  conv_lhs =>
    rhs
    rhs
    erw [hn']
  rw [← Category.assoc, ← Category.assoc]
  conv_lhs =>
    lhs
    rw [Category.assoc]
    erw [hp]
  simp only [← CategoryTheory.Functor.map_comp, prod_comp, Category.id_comp,
    Category.assoc]

private theorem open_projection_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (L : Integral l E U) (H : Integral l E V) (M : System l E U) (N : System l E V)
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (r : (calculus l E V).reduction.obj H ⟶ N) :
    (ordinaryTensorReduction l E a.ringedModels V).app ((ringedOpen l E j).obj L, H) ≫
      (calculus l E V).systemClosed.tensor.map
        (Prod.mkHom
          (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
            (Operations.shriek l E o j).map q) r) ≫
      (a.openComparisons.projection j).hom.app (M, N) =
    (calculus l E V).reduction.map ((a.ringedOpenComparisons.projection j).hom.app (L, H)) ≫
      GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app
        ((a.ringedModels.tensor U).ordinary.tensor.obj (L, (ringedPull l E j).obj H))) ≫
      (Operations.shriek l E o j).map
        ((ordinaryTensorReduction l E a.ringedModels U).app (L, (ringedPull l E j).obj H) ≫
          (calculus l E U).systemClosed.tensor.map
            (Prod.mkHom q ((a.realizationModel.reductionPull j).hom.app H ≫
              (pull l E j).map r))) := by
  have h := open_projection_inverse_square l E o a j L H M N q r
  have hi := inverse_square (calculus l E V).reduction
    ((a.ringedOpenComparisons.projection j).app (L, H)).symm
    ((a.openComparisons.projection j).app (M, N)).symm
    (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app
        ((a.ringedModels.tensor U).ordinary.tensor.obj (L, (ringedPull l E j).obj H))) ≫
      (Operations.shriek l E o j).map
        ((ordinaryTensorReduction l E a.ringedModels U).app (L, (ringedPull l E j).obj H) ≫
          (calculus l E U).systemClosed.tensor.map
            (Prod.mkHom q ((a.realizationModel.reductionPull j).hom.app H ≫
              (pull l E j).map r))))
    ((ordinaryTensorReduction l E a.ringedModels V).app ((ringedOpen l E j).obj L, H) ≫
      (calculus l E V).systemClosed.tensor.map
        (Prod.mkHom
          (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
            (Operations.shriek l E o j).map q) r))
    (by simpa only [Iso.symm_hom, Iso.app_inv, Category.assoc] using h)
  simpa only [Iso.symm_inv, Iso.app_hom, Category.assoc] using hi

private theorem compact_pull_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W : Scheme.{u}} (i : U ⟶ V) (g : V ⟶ W) (f : U ⟶ W) (w : f = i ≫ g)
    (H : Integral l E W) (N : System l E W)
    (r : (calculus l E W).reduction.obj H ⟶ N) :
    (a.realizationModel.reductionPull i).hom.app ((ringedPull l E g).obj H) ≫
      (pull l E i).map
        ((a.realizationModel.reductionPull g).hom.app H ≫ (pull l E g).map r) ≫
      (a.compositors.pullComp i g).inv.app N ≫
      eqToHom (congrArg (fun h : U ⟶ W ↦ (pull l E h).obj N) w.symm) =
    (calculus l E U).reduction.map
      ((ringedPullComp l E i g).inv.app H ≫
        eqToHom (congrArg (fun h : U ⟶ W ↦ (ringedPull l E h).obj H) w.symm)) ≫
      (a.realizationModel.reductionPull f).hom.app H ≫ (pull l E f).map r := by
  subst f
  simp only [eqToHom_refl, Category.comp_id]
  have hn := (a.compositors.pullComp i g).inv.naturality r
  dsimp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of%
    (pull_comp_inverse l E o a.realizationModel a.compositors i g H)]

private theorem open_inverse_naturality
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    {L H : Integral l E U} (h : L ⟶ H) :
    GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
      (Operations.shriek l E o j).map ((calculus l E U).reduction.map h) =
    (calculus l E V).reduction.map ((ringedOpen l E j).map h) ≫
      GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app H) := by
  have hL : IsIso ((a.realizationModel.openReduction l E j).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  have hH : IsIso ((a.realizationModel.openReduction l E j).app H) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j H
  have hn := (a.realizationModel.openReduction l E j).naturality h
  dsimp only [Functor.comp_map] at hn
  simp only [GeneratorReduction.inverseOrZero_eq_inv]
  apply (cancel_epi ((a.realizationModel.openReduction l E j).app L)).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem tensor_right_square
    (o : Operations l E) (a : AmbientModels l E o) {W : Scheme.{u}}
    (L H₁ H₂ : Integral l E W) (M N₁ N₂ : System l E W)
    (q : (calculus l E W).reduction.obj L ⟶ M)
    (r₁ : (calculus l E W).reduction.obj H₁ ⟶ N₁)
    (r₂ : (calculus l E W).reduction.obj H₂ ⟶ N₂)
    (α : H₁ ⟶ H₂) (β : N₁ ⟶ N₂)
    (h : r₁ ≫ β = (calculus l E W).reduction.map α ≫ r₂) :
    (ordinaryTensorReduction l E a.ringedModels W).app (L, H₁) ≫
      (calculus l E W).systemClosed.tensor.map (Prod.mkHom q r₁) ≫
      (calculus l E W).systemClosed.tensor.map (Prod.mkHom (𝟙 M) β) =
    (calculus l E W).reduction.map
      ((a.ringedModels.tensor W).ordinary.tensor.map (Prod.mkHom (𝟙 L) α)) ≫
      (ordinaryTensorReduction l E a.ringedModels W).app (L, H₂) ≫
      (calculus l E W).systemClosed.tensor.map (Prod.mkHom q r₂) := by
  let T := (calculus l E W).systemClosed.tensor
  have hn := (ordinaryTensorReduction l E a.ringedModels W).naturality
    (Prod.mkHom (𝟙 L) α)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [CategoryTheory.Functor.map_id] at hn
  rw [← T.map_comp]
  simp only [prod_comp, Category.comp_id, h]
  rw [show T.map (Prod.mkHom q ((calculus l E W).reduction.map α ≫ r₂)) =
    T.map (Prod.mkHom (𝟙 _) ((calculus l E W).reduction.map α)) ≫
      T.map (Prod.mkHom q r₂) by
        simp only [← T.map_comp, prod_comp, Category.id_comp]]
  rw [← Category.assoc, ← hn]
  simp only [T, Category.assoc]

private theorem open_map_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    {L H : Integral l E U} {M N : System l E U}
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (r : (calculus l E U).reduction.obj H ⟶ N)
    (α : L ⟶ H) (β : M ⟶ N)
    (h : q ≫ β = (calculus l E U).reduction.map α ≫ r) :
    (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
      (Operations.shriek l E o j).map q) ≫ (Operations.shriek l E o j).map β =
    (calculus l E V).reduction.map ((ringedOpen l E j).map α) ≫
      (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app H) ≫
        (Operations.shriek l E o j).map r) := by
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, ← Category.assoc,
    open_inverse_naturality l E o a j α, Category.assoc]

private theorem push_map_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (f : U ⟶ V)
    {L H : Integral l E U} {M N : System l E U}
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (r : (calculus l E U).reduction.obj H ⟶ N)
    (α : L ⟶ H) (β : M ⟶ N)
    (h : q ≫ β = (calculus l E U).reduction.map α ≫ r) :
    ((ordinaryPushReduction l E o a.realizationModel f).app L ≫
      (Operations.push l E o f).map q) ≫ (Operations.push l E o f).map β =
    (calculus l E V).reduction.map ((ringedPush l E f).map α) ≫
      ((ordinaryPushReduction l E o a.realizationModel f).app H ≫
        (Operations.push l E o f).map r) := by
  have hn := (ordinaryPushReduction l E o a.realizationModel f).naturality α
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]

private theorem compact_projection_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
    (e : Expression B I X U) (t : Expression B I X V) :
    (Expression.tensor (.compactSupport f cf e) t).ordinaryReduction l E o a K ≫
        compactificationProjection l E o a.compositors a.openComparisons cf
          (e.systemObj l E o ((inputReduction l E X).obj K))
          (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V.left).reduction.map
          (ringedCompactificationProjection l E a.ringedModels a.ringedOpenComparisons cf
            (e.ringedObj l E a.ringedModels K)
            (t.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f cf (.tensor e (.pull f t))).ordinaryReduction
          l E o a K := by
  let L := e.ringedObj l E a.ringedModels K
  let H := t.ringedObj l E a.ringedModels K
  let M := e.systemObj l E o ((inputReduction l E X).obj K)
  let N := t.systemObj l E o ((inputReduction l E X).obj K)
  let q := e.ordinaryReduction l E o a K
  let r := t.ordinaryReduction l E o a K
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E cf.i).app L) ≫
      (Operations.shriek l E o cf.i).map q
  let rg := (a.realizationModel.reductionPull cf.g).hom.app H ≫ (pull l E cf.g).map r
  let rgi := (a.realizationModel.reductionPull cf.i).hom.app
      ((ringedPull l E cf.g).obj H) ≫ (pull l E cf.i).map rg
  let rf := (a.realizationModel.reductionPull f.left).hom.app H ≫ (pull l E f.left).map r
  let α := (ringedPullComp l E cf.i cf.g).inv.app H ≫
    eqToHom (congrArg (fun g : U.left ⟶ V.left ↦ (ringedPull l E g).obj H) cf.comm.symm)
  let β := (a.compositors.pullComp cf.i cf.g).inv.app N ≫
    eqToHom (congrArg (fun g : U.left ⟶ V.left ↦ (pull l E g).obj N) cf.comm.symm)
  let A := (a.ringedModels.tensor cf.Z).ordinary.tensor.obj
    ((ringedOpen l E cf.i).obj L, (ringedPull l E cf.g).obj H)
  let C := (a.ringedModels.tensor U.left).ordinary.tensor.obj
    (L, (ringedPull l E cf.i).obj ((ringedPull l E cf.g).obj H))
  let D := (a.ringedModels.tensor U.left).ordinary.tensor.obj
    (L, (ringedPull l E f.left).obj H)
  let qA := (ordinaryTensorReduction l E a.ringedModels cf.Z).app
      ((ringedOpen l E cf.i).obj L, (ringedPull l E cf.g).obj H) ≫
    (calculus l E cf.Z).systemClosed.tensor.map (Prod.mkHom qJ rg)
  let qC := (ordinaryTensorReduction l E a.ringedModels U.left).app
      (L, (ringedPull l E cf.i).obj ((ringedPull l E cf.g).obj H)) ≫
    (calculus l E U.left).systemClosed.tensor.map (Prod.mkHom q rgi)
  let qD := (ordinaryTensorReduction l E a.ringedModels U.left).app
      (L, (ringedPull l E f.left).obj H) ≫
    (calculus l E U.left).systemClosed.tensor.map (Prod.mkHom q rf)
  let qJC := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E cf.i).app C) ≫
      (Operations.shriek l E o cf.i).map qC
  let qJD := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E cf.i).app D) ≫
      (Operations.shriek l E o cf.i).map qD
  have h₀ := proper_projection_coeff_natural l E o a (compactProper (f := f) cf)
    (inferInstance : IsProper cf.g) ((ringedOpen l E cf.i).obj L) H
    ((Operations.shriek l E o cf.i).obj M) N qJ r
  have h₁ : qA ≫ (a.openComparisons.projection cf.i).hom.app (M, (pull l E cf.g).obj N) =
      (calculus l E cf.Z).reduction.map
        ((a.ringedOpenComparisons.projection cf.i).hom.app
          (L, (ringedPull l E cf.g).obj H)) ≫ qJC := by
    simpa only [qA, qJC, qJ, C, qC, rgi, Category.assoc] using!
      open_projection_coeff l E o a cf.i L ((ringedPull l E cf.g).obj H)
        M ((pull l E cf.g).obj N) q rg
  have h₂ : qC ≫ (calculus l E U.left).systemClosed.tensor.map (Prod.mkHom (𝟙 M) β) =
      (calculus l E U.left).reduction.map
        ((a.ringedModels.tensor U.left).ordinary.tensor.map (Prod.mkHom (𝟙 L) α)) ≫ qD := by
    have hc : rgi ≫ β = (calculus l E U.left).reduction.map α ≫ rf := by
      simpa only [rgi, rg, rf, α, β, Category.assoc] using!
        compact_pull_coeff l E o a cf.i cf.g f.left cf.comm H N r
    simpa only [qC, qD, Category.assoc] using!
      tensor_right_square l E o a L _ _ M _ _ q rgi rf α β hc
  have h₂' := open_map_square l E o a cf.i qC qD
    ((a.ringedModels.tensor U.left).ordinary.tensor.map (Prod.mkHom (𝟙 L) α))
    ((calculus l E U.left).systemClosed.tensor.map (Prod.mkHom (𝟙 M) β)) h₂
  have hp₁ := push_map_square l E o a cf.g qA qJC
    ((a.ringedOpenComparisons.projection cf.i).hom.app (L, (ringedPull l E cf.g).obj H))
    ((a.openComparisons.projection cf.i).hom.app (M, (pull l E cf.g).obj N)) h₁
  have hp₂ := push_map_square l E o a cf.g qJC qJD
    ((ringedOpen l E cf.i).map
      ((a.ringedModels.tensor U.left).ordinary.tensor.map (Prod.mkHom (𝟙 L) α)))
    ((Operations.shriek l E o cf.i).map
      ((calculus l E U.left).systemClosed.tensor.map (Prod.mkHom (𝟙 M) β))) h₂'
  have h := paste_three (calculus l E V.left).reduction
    ((ordinaryTensorReduction l E a.ringedModels V.left).app
        ((ringedPush l E cf.g).obj ((ringedOpen l E cf.i).obj L), H) ≫
      (calculus l E V.left).systemClosed.tensor.map
        (Prod.mkHom ((ordinaryPushReduction l E o a.realizationModel cf.g).app
          ((ringedOpen l E cf.i).obj L) ≫ (Operations.push l E o cf.g).map qJ) r))
    ((ordinaryPushReduction l E o a.realizationModel cf.g).app A ≫
      (Operations.push l E o cf.g).map qA)
    ((ordinaryPushReduction l E o a.realizationModel cf.g).app
      ((ringedOpen l E cf.i).obj C) ≫ (Operations.push l E o cf.g).map qJC)
    ((ordinaryPushReduction l E o a.realizationModel cf.g).app
      ((ringedOpen l E cf.i).obj D) ≫ (Operations.push l E o cf.g).map qJD)
    (((ringedProperProjection l E a.ringedModels cf.g).app ((ringedOpen l E cf.i).obj L)).app H)
    ((ringedPush l E cf.g).map
      ((a.ringedOpenComparisons.projection cf.i).hom.app (L, (ringedPull l E cf.g).obj H)))
    ((ringedPush l E cf.g).map ((ringedOpen l E cf.i).map
      ((a.ringedModels.tensor U.left).ordinary.tensor.map (Prod.mkHom (𝟙 L) α))))
    (((properProjection l E o cf.g).app ((Operations.shriek l E o cf.i).obj M)).app N)
    ((Operations.push l E o cf.g).map
      ((a.openComparisons.projection cf.i).hom.app (M, (pull l E cf.g).obj N)))
    ((Operations.push l E o cf.g).map ((Operations.shriek l E o cf.i).map
      ((calculus l E U.left).systemClosed.tensor.map (Prod.mkHom (𝟙 M) β))))
    (by simpa only [A, qA, rg, compactProper, Over.homMk_left, Category.assoc] using! h₀)
    hp₁ hp₂
  simpa only [Expression.ordinaryReduction, compactificationProjection,
    ringedCompactificationProjection, CategoryTheory.Functor.map_comp, Category.assoc,
    L, H, M, N, q, r, qJ, rg, rf, α, β, A, C, D, qA, qC, qD, qJC, qJD] using! h

/-- Ordinary coefficient squares for the fixed open/proper compactification words.
Source: blueprint fix-prop-coherence, expansion of compactification exchange and projection.
(blueprint: lem-sf-integral-ordinary-compactification-squares).

Proof: the exchange clause is ordinaryCompactificationExchangeSquare. For projection,
expand the three factors: proper projection, proper image of open projection, and
open/proper image of the inverse pull compositor with the actual cf.comm equation.
Specialize the primitive proper-projection square to formal variables and insert
both child coefficients by naturality. Invert the prescribed open projection square;
use naturality of inverse open reduction to lift the inverse pull-composition square.
Whisker these equalities by proper image and paste them using paste_three. This
proves the projection clause completely, with no new projection obligation. -/
theorem ordinaryCompactificationSquares
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    (∀ {U V U' V' : Over B}
      (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
      (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
      (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
      (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U),
      (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K) ∧
    (∀ {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (e : Expression B I X U) (t : Expression B I X V),
      (Expression.tensor (.compactSupport f cf e) t).ordinaryReduction l E o a K ≫
        compactificationProjection l E o a.compositors a.openComparisons cf
          (e.systemObj l E o ((inputReduction l E X).obj K))
          (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V.left).reduction.map
          (ringedCompactificationProjection l E a.ringedModels a.ringedOpenComparisons cf
            (e.ringedObj l E a.ringedModels K)
            (t.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f cf (.tensor e (.pull f t))).ordinaryReduction
          l E o a K) := by
  constructor
  · intro U V U' V' f f' cf cf' x y z wi wp hi e
    exact ordinaryCompactificationExchangeSquare l E o a K f f' cf cf' x y z wi wp hi e
  · intro U V f cf e t
    exact compact_projection_square l E o a K f cf e t

end WeilConjectures.IntegralSystemRealization
