/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.CanonicalReductionTensorPull
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat

/-! # Ordinary coefficient projection square

Source: blueprint fix-prop-coherence, the projection component of the normalized
mate argument for `lem-sf-integral-ordinary-exchange-projection-squares`.

The ordinary tensor/pullback comparison supplies the compatibility hypothesis
of the generic right-adjoint projection mate theorem. Naturality then inserts
the two expression coefficient maps. -/

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

private def curryComparison {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (B : C × C ⥤ C) (S : D × D ⥤ D)
    (t : B ⋙ F ⟶ F.prod F ⋙ S) :
    (Functor.postcompose₂.obj F).obj (Functor.curryObj B) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (Functor.curry.obj S) where
  app M :=
    { app := fun N ↦ t.app (M, N)
      naturality := by
        intro N N' f
        change F.map (B.map (Prod.mkHom (𝟙 M) f)) ≫ t.app (M, N') =
          t.app (M, N) ≫ S.map (Prod.mkHom (𝟙 (F.obj M)) (F.map f))
        simpa only [Functor.comp_map, Functor.prod_map, F.map_id] using
          t.naturality (Prod.mkHom (𝟙 M) f) }
  naturality := by
    intro M M' f
    ext N
    change F.map (B.map (Prod.mkHom f (𝟙 N))) ≫ t.app (M', N) =
      t.app (M, N) ≫ S.map (Prod.mkHom (F.map f) (𝟙 (F.obj N)))
    simpa only [Functor.comp_map, Functor.prod_map, F.map_id] using
      t.naturality (Prod.mkHom f (𝟙 N))

private theorem inverseComparisonSquare {C : Type*} [Category C]
    {A B M N : C} (r : A ≅ B) (s : M ≅ N) (x : B ⟶ N) (y : A ⟶ M)
    (h : r.hom ≫ x = y ≫ s.hom) : x ≫ s.inv = r.inv ≫ y := by
  apply (cancel_epi r.hom).1
  rw [← Category.assoc, h, Category.assoc, s.hom_inv_id, Category.comp_id]
  simp

/-- The coefficient comparison required by the generic mate lemma.

Source: `canonicalReductionTensorPull`, the normalized tensor/pullback square
in blueprint fix-prop-coherence. Invert the tensor of the pullback coefficient
isomorphisms and the pullback coefficient isomorphism of the tensor object.
Currying the resulting identity gives exactly the generic mate hypothesis.

(blueprint: lem-sf-integral-ordinary-projection-square)
-/
private theorem projectionMateCompatibility
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {U V : Over B} (f : U ⟶ V) :
    let P := IntegralSystemRealization.pull l E f.left
    let T := Functor.curryObj (calculus l E U.left).systemClosed.tensor
    let Sρ := Functor.curryObj (a.ringedModels.tensor V.left).ordinary.tensor
    ∀ (a₁ b : DerivedCategory (V.left.proEtaleRingModules
      ((PurCompactSupport.completed l E).ring V.left))),
      P.map (((curryComparison (calculus l E V.left).reduction
        (a.ringedModels.tensor V.left).ordinary.tensor
        (calculus l E V.left).systemClosed.tensor
        (ordinaryTensorReduction l E a.ringedModels V.left)).app a₁).app b) ≫
      ((Functor.curry.mapIso (pullbackTensorSystemComparison l E f.left) ≪≫
        P.curryObjProdComp P (calculus l E U.left).systemClosed.tensor).hom.app
        ((calculus l E V.left).reduction.obj a₁)).app
          ((calculus l E V.left).reduction.obj b) ≫
      (T.map ((a.realizationModel.reductionPull f.left).inv.app a₁)).app
        (P.obj ((calculus l E V.left).reduction.obj b)) ≫
      (T.obj ((ringedPull l E f.left ⋙ (calculus l E U.left).reduction).obj a₁)).map
        ((a.realizationModel.reductionPull f.left).inv.app b) =
      (a.realizationModel.reductionPull f.left).inv.app ((Sρ.obj a₁).obj b) ≫
      (calculus l E U.left).reduction.map
        (((Functor.curry.mapIso (ringedTensorPull l E a.ringedModels f.left) ≪≫
          (ringedPull l E f.left).curryObjProdComp (ringedPull l E f.left)
            (a.ringedModels.tensor U.left).ordinary.tensor).hom.app a₁).app b) ≫
      (((curryComparison (calculus l E U.left).reduction
        (a.ringedModels.tensor U.left).ordinary.tensor
        (calculus l E U.left).systemClosed.tensor
        (ordinaryTensorReduction l E a.ringedModels U.left)).app
        ((ringedPull l E f.left).obj a₁)).app
          ((ringedPull l E f.left).obj b)) := by
  dsimp only
  intro M N
  let α := a.realizationModel.reductionPull f.left
  let Q := (calculus l E U.left).systemClosed.tensor
  have h := canonicalReductionTensorPull l E o a.realizationModel a.ringedModels f.left M N
  have hi := inverseComparisonSquare
    (α.app ((a.ringedModels.tensor V.left).ordinary.tensor.obj (M, N)))
    (Q.mapIso ((α.app M).prod (α.app N)))
    ((pull l E f.left).map
      ((ordinaryTensorReduction l E a.ringedModels V.left).app (M, N)) ≫
      (pullbackTensorSystemComparison l E f.left).hom.app
        ((calculus l E V.left).reduction.obj M, (calculus l E V.left).reduction.obj N))
    ((calculus l E U.left).reduction.map
      ((ringedTensorPull l E a.ringedModels f.left).hom.app (M, N)) ≫
      (ordinaryTensorReduction l E a.ringedModels U.left).app
        ((ringedPull l E f.left).obj M, (ringedPull l E f.left).obj N))
    (by simpa only [α, Q, ordinaryTensorReduction, Functor.mapIso_hom,
      Iso.prod_hom, Iso.app_hom, Category.assoc] using h)
  simp only [Functor.mapIso_inv, Iso.prod_inv] at hi
  change (pull l E f.left).map
      ((ordinaryTensorReduction l E a.ringedModels V.left).app (M, N)) ≫
    ((pullbackTensorSystemComparison l E f.left).hom.app
      ((calculus l E V.left).reduction.obj M, (calculus l E V.left).reduction.obj N) ≫
        𝟙 _) ≫
    Q.map (Prod.mkHom (α.inv.app M) (𝟙 _)) ≫
    Q.map (Prod.mkHom (𝟙 _) (α.inv.app N)) =
    α.inv.app ((a.ringedModels.tensor V.left).ordinary.tensor.obj (M, N)) ≫
    (calculus l E U.left).reduction.map
      ((ringedTensorPull l E a.ringedModels f.left).hom.app (M, N) ≫ 𝟙 _) ≫
    (ordinaryTensorReduction l E a.ringedModels U.left).app
      ((ringedPull l E f.left).obj M, (ringedPull l E f.left).obj N)
  simp only [Category.comp_id]
  simpa only [Iso.app_inv, ← Category.assoc, ← Functor.map_comp,
    prod_comp, Prod.mkHom, Category.comp_id, Category.id_comp] using hi

private theorem projectionNaturality
    {C D : Type*} [Category C] [Category D]
    (P : D ⥤ C) (G : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (π : G ⋙ Functor.curryObj S ⟶
      (Functor.postcompose₂.obj G).obj
        ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj P).obj
          (Functor.curryObj T)))
    {M M' : C} {L L' : D} (q : M ⟶ M') (r : L ⟶ L') :
    S.map (Prod.mkHom (G.map q) r) ≫ (π.app M').app L' =
      (π.app M).app L ≫ G.map (T.map (Prod.mkHom q (P.map r))) := by
  have h := (Functor.uncurry.map π).naturality (Prod.mkHom q r)
  change (S.map (Prod.mkHom (G.map q) (𝟙 L)) ≫
    S.map (Prod.mkHom (𝟙 (G.obj M')) r)) ≫ (π.app M').app L' =
    (π.app M).app L ≫
      (G.map (T.map (Prod.mkHom q (𝟙 (P.obj L)))) ≫
        G.map (T.map (Prod.mkHom (𝟙 M') (P.map r)))) at h
  simpa only [← Functor.map_comp, prod_comp, Prod.mkHom, Category.comp_id, Category.id_comp]
    using h

/-- Projection component of the ordinary coefficient mate square.
Source: Stacks Tags 07A7 and 0E48; blueprint fix-prop-coherence.
(blueprint: lem-sf-integral-ordinary-projection-square).

Proof: invert `canonicalReductionTensorPull` to obtain the compatibility
hypothesis of `Adjunction.rightAdjointProjectionMap_mate`. The counit mate
identity identifies its direct-image comparison with `ordinaryPushReduction`.
Postcompose the mate equation with the tensor of the two expression coefficient
maps. Cancel the inverse/hom pullback coefficient maps and use naturality of
the proper projection to obtain the displayed equality.
-/
theorem ordinaryProjectionSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    ∀ {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) (t : Expression B I X V),
      (Expression.tensor (.push f hf e) t).ordinaryReduction l E o a K ≫
        ((properProjection l E o f.left).app
          (e.systemObj l E o ((inputReduction l E X).obj K))).app
            (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V.left).reduction.map
          (((ringedProperProjection l E a.ringedModels f.left).app
            (e.ringedObj l E a.ringedModels K)).app (t.ringedObj l E a.ringedModels K)) ≫
        (Expression.push f hf (.tensor e (.pull f t))).ordinaryReduction l E o a K := by
  intro U V f hf e t
  let P := IntegralSystemRealization.pull l E f.left
  let G := Operations.push l E o f.left
  let T := Functor.curryObj (calculus l E U.left).systemClosed.tensor
  let S := Functor.curryObj (calculus l E V.left).systemClosed.tensor
  let Tρ := Functor.curryObj (a.ringedModels.tensor U.left).ordinary.tensor
  let Sρ := Functor.curryObj (a.ringedModels.tensor V.left).ordinary.tensor
  have hm := Adjunction.rightAdjointProjectionMap_mate
    (T₁ := Tρ) (S₁ := Sρ) (T₂ := T) (S₂ := S)
    (ringedAdj l E f.left) (o.direct f.left).adj
    (Functor.curry.mapIso (ringedTensorPull l E a.ringedModels f.left) ≪≫
      Functor.curryObjProdComp (ringedPull l E f.left) (ringedPull l E f.left)
        (a.ringedModels.tensor U.left).ordinary.tensor).hom
    (Functor.curry.mapIso (pullbackTensorSystemComparison l E f.left) ≪≫
      Functor.curryObjProdComp P P (calculus l E U.left).systemClosed.tensor).hom
    (curryComparison (calculus l E V.left).reduction
      (a.ringedModels.tensor V.left).ordinary.tensor
      (calculus l E V.left).systemClosed.tensor
      (ordinaryTensorReduction l E a.ringedModels V.left))
    (curryComparison (calculus l E U.left).reduction
      (a.ringedModels.tensor U.left).ordinary.tensor
      (calculus l E U.left).systemClosed.tensor
      (ordinaryTensorReduction l E a.ringedModels U.left))
    (a.realizationModel.reductionPull f.left).inv
    (ordinaryPushReduction l E o a.realizationModel f.left)
    (projectionMateCompatibility l E o a f)
    (fun M ↦ by
      simpa only [ordinaryPushReduction] using
        mateEquiv_counit (ringedAdj l E f.left) (o.direct f.left).adj
          (TwoSquare.mk _ _ _ _ (a.realizationModel.reductionPull f.left).inv) M)
    (e.ringedObj l E a.ringedModels K) (t.ringedObj l E a.ringedModels K)
  let q := Expression.ordinaryReduction l E o a e K
  let r := Expression.ordinaryReduction l E o a t K
  let z := (calculus l E U.left).systemClosed.tensor.map
    (Prod.mkHom q ((a.realizationModel.reductionPull f.left).hom.app
      (t.ringedObj l E a.ringedModels K) ≫ P.map r))
  have hm' := congrArg (fun m ↦ m ≫ G.map z) hm
  simp only [Expression.ordinaryReduction, properProjection, ringedProperProjection]
  convert hm'.symm using 1 <;>
    simp only [curryComparison, Category.assoc]
  · apply congrArg (fun m ↦
      (ordinaryTensorReduction l E a.ringedModels V.left).app
        ((ringedPush l E f.left).obj (e.ringedObj l E a.ringedModels K),
          t.ringedObj l E a.ringedModels K) ≫ m)
    have hz :
        (T.obj ((calculus l E U.left).reduction.obj
          (e.ringedObj l E a.ringedModels K))).map
          ((a.realizationModel.reductionPull f.left).inv.app
            (t.ringedObj l E a.ringedModels K)) ≫ z =
        (calculus l E U.left).systemClosed.tensor.map (Prod.mkHom q (P.map r)) := by
      simp only [T, z, Functor.curryObj, ← Functor.map_comp]
      congr 1
      ext <;> simp
    change (calculus l E V.left).systemClosed.tensor.map
      (Prod.mkHom
        ((ordinaryPushReduction l E o a.realizationModel f.left).app
          (e.ringedObj l E a.ringedModels K) ≫ G.map q) r) ≫
      ((properProjection l E o f.left).app
        (e.systemObj l E o ((inputReduction l E X).obj K))).app
        (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (S.map ((ordinaryPushReduction l E o a.realizationModel f.left).app
        (e.ringedObj l E a.ringedModels K))).app
        ((calculus l E V.left).reduction.obj (t.ringedObj l E a.ringedModels K)) ≫
      ((properProjection l E o f.left).app
        ((calculus l E U.left).reduction.obj (e.ringedObj l E a.ringedModels K))).app
        ((calculus l E V.left).reduction.obj (t.ringedObj l E a.ringedModels K)) ≫
      G.map ((T.obj ((calculus l E U.left).reduction.obj
        (e.ringedObj l E a.ringedModels K))).map
        ((a.realizationModel.reductionPull f.left).inv.app
          (t.ringedObj l E a.ringedModels K))) ≫ G.map z
    have hz' := congrArg (fun m ↦ G.map m) hz
    simp only [Functor.map_comp] at hz'
    conv_rhs => rw [hz']
    have hn := projectionNaturality P G
      (calculus l E U.left).systemClosed.tensor
      (calculus l E V.left).systemClosed.tensor (properProjection l E o f.left) q r
    have hs : (calculus l E V.left).systemClosed.tensor.map
        (Prod.mkHom
          ((ordinaryPushReduction l E o a.realizationModel f.left).app
            (e.ringedObj l E a.ringedModels K) ≫ G.map q) r) =
        (S.map ((ordinaryPushReduction l E o a.realizationModel f.left).app
          (e.ringedObj l E a.ringedModels K))).app
          ((calculus l E V.left).reduction.obj (t.ringedObj l E a.ringedModels K)) ≫
        (calculus l E V.left).systemClosed.tensor.map (Prod.mkHom (G.map q) r) := by
      dsimp only [S, Functor.curryObj]
      rw [← Functor.map_comp]
      congr 1
      ext <;> simp
    exact (congrArg (fun m ↦ m ≫
      ((properProjection l E o f.left).app
        (e.systemObj l E o ((inputReduction l E X).obj K))).app
        (t.systemObj l E o ((inputReduction l E X).obj K))) hs).trans
      ((Category.assoc _ _ _).trans (congrArg (fun m ↦
      (S.map ((ordinaryPushReduction l E o a.realizationModel f.left).app
        (e.ringedObj l E a.ringedModels K))).app
        ((calculus l E V.left).reduction.obj (t.ringedObj l E a.ringedModels K)) ≫ m) hn))
  · dsimp only [G, P, z, Tρ, Expression.ringedObj]
    simp only [Functor.map_comp]
    rfl

end WeilConjectures.IntegralSystemRealization
