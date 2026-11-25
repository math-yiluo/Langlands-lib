/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

/-- Counit naturality for a coordinate map followed by reconstruction. -/
private theorem reduce_coordinate
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D) (L : D ⥤ C)
    (ε : L ⋙ R ⟶ 𝟭 D) {K : C} {A B : D}
    (b : K ⟶ L.obj A) (a : A ⟶ B) :
    R.map (b ≫ L.map a) ≫ ε.app B = R.map b ≫ ε.app A ≫ a := by
  rw [R.map_comp, Category.assoc]
  exact congrArg (R.map b ≫ ·) (ε.naturality a)

/-- A normalized tensor square remains commutative in counit coordinates. -/
private theorem coordinate_square
    {CY CX DY DX : Type*}
    [Category CY] [Category CX] [Category DY] [Category DX]
    (RY : CY ⥤ DY) (LY : DY ⥤ CY) (RX : CX ⥤ DX) (LX : DX ⥤ CX)
    (εY : LY ⋙ RY ⟶ 𝟭 DY) (εX : LX ⋙ RX ⟶ 𝟭 DX)
    (TY : DY × DY ⥤ DY) (TX : DX × DX ⥤ DX) (F : DY ⥤ DX)
    (tY : CY × CY ⥤ CY) (tX : CX × CX ⥤ CX) (p : CY ⥤ CX)
    (etY : tY ≅ RY.prod RY ⋙ TY ⋙ LY)
    (etX : tX ≅ RX.prod RX ⋙ TX ⋙ LX)
    (ep : p ≅ RY ⋙ F ⋙ LX)
    (c : TY ⋙ F ≅ F.prod F ⋙ TX)
    (M N : CY) (A B : DY) (U : DY) (V A' B' : DX)
    (dA : RY.obj M ⟶ A) (dB : RY.obj N ⟶ B)
    (mY : U ≅ TY.obj (A, B)) (mX : V ≅ TX.obj (A', B'))
    (qA : F.obj A ⟶ A') (qB : F.obj B ⟶ B')
    (v : F.obj U ⟶ V)
    (hv : F.map mY.hom ≫ c.hom.app (A, B) ≫ TX.map (Prod.mkHom qA qB) = v ≫ mX.hom)
    [IsIso (εY.app (TY.obj (RY.obj M, RY.obj N)))]
    [IsIso (εX.app (F.obj (RY.obj M)))]
    [IsIso (εX.app (F.obj (RY.obj N)))] :
    let bT := etY.hom.app (M, N) ≫ LY.map (TY.map (Prod.mkHom dA dB) ≫ mY.inv)
    let bA := ep.hom.app M ≫ LX.map (F.map dA ≫ qA)
    let bB := ep.hom.app N ≫ LX.map (F.map dB ≫ qB)
    let can := ep.hom.app (tY.obj (M, N)) ≫
      LX.map (F.map (RY.map (etY.hom.app (M, N)))) ≫
      LX.map (F.map (εY.app (TY.obj (RY.obj M, RY.obj N)))) ≫
      LX.map (c.hom.app (RY.obj M, RY.obj N)) ≫
      LX.map (TX.map (Prod.mkHom (inv (εX.app (F.obj (RY.obj M))))
        (inv (εX.app (F.obj (RY.obj N)))))) ≫
      LX.map (TX.map (Prod.mkHom (RX.map (ep.inv.app M)) (RX.map (ep.inv.app N)))) ≫
      etX.inv.app (p.obj M, p.obj N)
    (ep.hom.app (tY.obj (M, N)) ≫
      LX.map (F.map (RY.map bT ≫ εY.app U))) ≫ LX.map v =
    can ≫ (etX.hom.app (p.obj M, p.obj N) ≫
      LX.map (TX.map (Prod.mkHom (RX.map bA ≫ εX.app A')
        (RX.map bB ≫ εX.app B')))) ≫ LX.map mX.inv := by
  dsimp only
  rw [reduce_coordinate RY LY εY, reduce_coordinate RX LX εX,
    reduce_coordinate RX LX εX]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← LX.map_comp]
  apply congrArg (ep.hom.app (tY.obj (M, N)) ≫ ·)
  apply congrArg LX.map
  simp only [← TX.map_comp_assoc, prod_comp]
  dsimp only [Prod.mkHom]
  simp only [← RX.map_comp_assoc, Iso.inv_hom_id_app]
  erw [RX.map_id, RX.map_id]
  simp only [Category.id_comp, IsIso.inv_hom_id_assoc]
  have hc := c.hom.naturality (Prod.mkHom dA dB)
  dsimp only [Functor.comp_map, Functor.prod_map] at hc
  have hp : TX.map (Prod.mkHom (F.map dA ≫ qA) (F.map dB ≫ qB)) =
      TX.map (Prod.mkHom (F.map dA) (F.map dB)) ≫ TX.map (Prod.mkHom qA qB) := by
    rw [← TX.map_comp]
    rfl
  rw [hp]
  simp only [Category.assoc]
  rw [← Category.assoc (c.hom.app _) (TX.map _) (TX.map _ ≫ mX.inv), ← hc]
  have hm : F.map mY.inv ≫ v =
      c.hom.app (A, B) ≫ TX.map (Prod.mkHom qA qB) ≫ mX.inv := by
    rw [← cancel_epi (F.map mY.hom)]
    simpa only [Iso.hom_inv_id_map_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using (congrArg (· ≫ mX.inv) hv).symm
  simp only [Category.assoc]
  rw [hm]
  rfl

/-- Paste a normalized tensor square with a change of representatives. -/
private theorem transport_tensor_square
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D) (T : D × D ⥤ D)
    {P P' R S : C} {K H A B A' B' V W : D}
    (a : K ⟶ H) (b : H ⟶ T.obj (A, B))
    (p : K ⟶ Q.obj P) (e : P ≅ P') (c : P ⟶ R) (d : R ⟶ S)
    (m : Q.obj R ⟶ T.obj (A', B')) (n : Q.obj S ⟶ T.obj (V, W))
    (x : A ⟶ A') (y : B ⟶ B') (q : A' ⟶ V) (r : B' ⟶ W)
    (hs : a ≫ b ≫ T.map (Prod.mkHom x y) = p ≫ Q.map c ≫ m)
    (hn : Q.map d ≫ n = m ≫ T.map (Prod.mkHom q r)) :
    a ≫ b ≫ T.map (Prod.mkHom (x ≫ q) (y ≫ r)) =
      (p ≫ Q.map e.hom) ≫ Q.map (e.inv ≫ c ≫ d) ≫ n := by
  have hp : Prod.mkHom (x ≫ q) (y ≫ r) = Prod.mkHom x y ≫ Prod.mkHom q r := rfl
  rw [hp, T.map_comp, ← Category.assoc b, ← Category.assoc a, hs]
  simp only [Category.assoc]
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

attribute [local irreducible] pullbackTensorCalculus pullbackTensorIntegralTensorModel
  pullbackTensorIntegralPullbackModel pullbackTensorSystemComparison
  pullbackTensorSystemModel
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.leftAdjoint
  coefficientSequenceLimit integralDerivedPullback integralCompletedTensor
attribute [local implicit_reducible] pullbackTensorReferenceTensor pullbackTensorReferencePullback
  substituteInputs sourceExpression targetExpression coefficientSequenceInternalHom
  StrictQuotient.SystemGood sfIntegralConstructible constructibleIntegralPullback
  pullbackTensorSequenceDerived coefficientKFlatInclusion

private theorem strict_comparison_square
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : StrictQuotient.Complex l E Y)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (hfA : StrictQuotient.SystemGood l E (StrictQuotient.pull l E f A))
    (hfB : StrictQuotient.SystemGood l E (StrictQuotient.pull l E f B)) :
    (pullbackTensorSequenceDerived l E f).map
        (pullbackTensorSystemModel l E Y A B hA.1 hB.1).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A ≫
            DerivedCategory.Q.map ((pullBridge l E f).hom.app A))
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app B ≫
            DerivedCategory.Q.map ((pullBridge l E f).hom.app B))) =
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((pullBridge l E f).hom.app (StrictQuotient.total l E A B))) ≫
      DerivedCategory.Q.map (comparison l E f A B).hom ≫
      (pullbackTensorSystemModel l E X _ _ hfA.1 hfB.1).hom := by
  let F := pullbackTensorSequenceDerived l E f
  let T := (pullbackTensorCalculus l E X).systemClosed.tensor
  let G := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  have hs := (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec
    A B hA.1 hB.1
  have hn := (pullbackTensorCalculus l E X).systemTensorModel.comparison.hom.naturality
    (Prod.mkHom
      (show (⟨G.obj A, pullbackTensorSequenceGood l E f A hA.1⟩ :
        ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E X))) ⟶
        ⟨StrictQuotient.pull l E f A, hfA.1⟩ from ⟨(pullBridge l E f).hom.app A⟩)
      (show (⟨G.obj B, pullbackTensorSequenceGood l E f B hB.1⟩ :
        ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E X))) ⟶
        ⟨StrictQuotient.pull l E f B, hfB.1⟩ from ⟨(pullBridge l E f).hom.app B⟩))
  have hs' : F.map (pullbackTensorSystemModel l E Y A B hA.1 hB.1).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
      T.map (Prod.mkHom
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A)
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app B)) =
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (A, B)) ≫
      (pullbackTensorSystemModel l E X (G.obj A) (G.obj B)
        (pullbackTensorSequenceGood l E f A hA.1)
        (pullbackTensorSequenceGood l E f B hB.1)).hom := by
    simpa only [pullbackTensorSystemComparison, pullbackTensorUniqueChoice] using hs
  have hn' : DerivedCategory.Q.map
        ((coefficientTotalTensor.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)).map
            (Prod.mkHom ((pullBridge l E f).hom.app A) ((pullBridge l E f).hom.app B))) ≫
      (pullbackTensorSystemModel l E X _ _ hfA.1 hfB.1).hom =
    (pullbackTensorSystemModel l E X (G.obj A) (G.obj B)
      (pullbackTensorSequenceGood l E f A hA.1)
      (pullbackTensorSequenceGood l E f B hB.1)).hom ≫
      T.map (Prod.mkHom (DerivedCategory.Q.map ((pullBridge l E f).hom.app A))
        (DerivedCategory.Q.map ((pullBridge l E f).hom.app B))) := by
    simpa only [pullbackTensorSystemModel, CoefficientTensorModels.iso,
      Functor.comp_map, Functor.prod_map, coefficientKFlatInclusion,
      ObjectProperty.ι_map, ObjectProperty.ι_obj, Functor.comp_obj,
      Functor.prod_obj, Iso.app_hom, T] using hn
  unfold comparison
  exact transport_tensor_square DerivedCategory.Q T
    (F.map (pullbackTensorSystemModel l E Y A B hA.1 hB.1).hom)
    ((pullbackTensorSystemComparison l E f).hom.app
      (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B))
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _)
    ((pullBridge l E f).app (StrictQuotient.total l E A B))
    ((pullbackTensorSequenceCochain l E f).hom.app (A, B))
    ((coefficientTotalTensor.{u, u+1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)).map
        (Prod.mkHom ((pullBridge l E f).hom.app A) ((pullBridge l E f).hom.app B)))
    (pullbackTensorSystemModel l E X (G.obj A) (G.obj B)
      (pullbackTensorSequenceGood l E f A hA.1)
      (pullbackTensorSequenceGood l E f B hB.1)).hom
    (pullbackTensorSystemModel l E X _ _ hfA.1 hfB.1).hom
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A)
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app B)
    (DerivedCategory.Q.map ((pullBridge l E f).hom.app A))
    (DerivedCategory.Q.map ((pullBridge l E f).hom.app B)) hs' hn'

/-- The canonical comparison intertwines substitution for arbitrary leaf maps. -/
private theorem substitution_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y)
    (A B : StrictQuotient.Complex l E Y)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (hfA : StrictQuotient.SystemGood l E (StrictQuotient.pull l E f A))
    (hfB : StrictQuotient.SystemGood l E (StrictQuotient.pull l E f B))
    (βA : M.obj ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A))
    (βB : N.obj ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj B)) :
    pullSubstitution l E f (StrictQuotient.total l E A B)
        (tensorSubstitution l E A B hA hB βA βB) ≫
      (coefficientSequenceLimit l E X).map (DerivedCategory.Q.map (comparison l E f A B).hom) =
    (canonicalIntegralPullbackTensor l E f M N).hom.hom ≫
      tensorSubstitution l E _ _ hfA hfB
        (pullSubstitution l E f A βA) (pullSubstitution l E f B βB) := by
  have hc := pullbackTensorComparisonCounits l E f M N
  let := hc.1
  let := hc.2.1
  let := hc.2.2
  have H := coordinate_square
    (pullbackTensorCalculus l E Y).reduction (coefficientSequenceLimit l E Y)
    (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
    (pullbackTensorCalculus l E Y).adjunction.counit
    (pullbackTensorCalculus l E X).adjunction.counit
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorSequenceDerived l E f)
    (integralCompletedTensor l E Y) (integralCompletedTensor l E X)
    (integralDerivedPullback l E f)
    (pullbackTensorIntegralTensorModel l E Y) (pullbackTensorIntegralTensorModel l E X)
    (pullbackTensorIntegralPullbackModel l E f) (pullbackTensorSystemComparison l E f)
    M.obj N.obj (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
    (DerivedCategory.Q.obj (StrictQuotient.total l E A B))
    (DerivedCategory.Q.obj (StrictQuotient.total l E
      (StrictQuotient.pull l E f A) (StrictQuotient.pull l E f B)))
    (DerivedCategory.Q.obj (StrictQuotient.pull l E f A))
    (DerivedCategory.Q.obj (StrictQuotient.pull l E f B))
    (reduction l E βA) (reduction l E βB)
    (pullbackTensorSystemModel l E Y A B hA.1 hB.1)
    (pullbackTensorSystemModel l E X _ _ hfA.1 hfB.1)
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A ≫
      DerivedCategory.Q.map ((pullBridge l E f).hom.app A))
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app B ≫
      DerivedCategory.Q.map ((pullBridge l E f).hom.app B))
    (((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((pullBridge l E f).hom.app (StrictQuotient.total l E A B))) ≫
      DerivedCategory.Q.map (comparison l E f A B).hom)
    (by simpa only [Category.assoc] using strict_comparison_square l E f A B hA hB hfA hfB)
  unfold tensorSubstitution pullSubstitution reduction
  unfold canonicalIntegralPullbackTensor pullbackTensorReferenceComparison
  unfold pullbackTensorReferencePullback pullbackTensorReferenceTensor
  unfold reduction at H
  dsimp only [ObjectProperty.isoMk, ObjectProperty.homMk, Iso.trans, Iso.symm,
    Iso.app, Functor.mapIso, Iso.prod, asIso]
  simp only [Functor.comp_map, Functor.prod_map, Functor.map_comp,
    Category.assoc, constructibleIntegralPullback, ObjectProperty.lift_obj_obj,
    ObjectProperty.ι_obj, Functor.comp_obj] at H ⊢
  repeat' erw [Category.assoc]
  exact H

/-- The recursive L substitution intertwines the strict comparison with the canonical one.
Source: Stacks 07A4 and 0941; quotient-realization proof steps 2, 3 and 6
(blueprint: lem-pur-completed-scalar-beta-comparison).

Proof: use the coherent scalar quotients of the prescribed representatives as the
three leaves. Their scalar substitution is the scalar realization followed by
scalar change of the E coherent reduction and the fixed K-flat scalar counit.
Expand the recursion at pullF(tensor(input 0,input 1)) and at the tensor of the
two pullF inputs. The defining normalization square of the descended system
pullback/tensor comparison identifies its cochain model with comparison at L.
Naturality moves the two leaf reduction maps through that square. Insert the
primitive tensor and pullback realizations in canonicalIntegralPullbackTensor.
Counit naturality and the adjunction triangle identities cancel their intermediate
reconstruction factors. The remaining factors are exactly the two displayed
recursive substitutions. Work in whole coefficient systems before total limit,
so every horizontal transition and arbitrary choice of representative is retained.
No invertibility of these recursive substitutions is used in this equation;
zero inputs, identity coefficients and ramified extensions obey the same formulas. -/
theorem completedScalarBetaComparison
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    {ρY : IntegralComparisonRoosModel l L Y}
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A)) :
    scalarBeta l E L ι M P φ good SY goodL (sourceExpression h f) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map
        (comparison l L f ((scalarQuotients l E L ι P) 0)
          ((scalarQuotients l E L ι P) 1)).hom) =
    (canonicalIntegralPullbackTensor l L f
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M 0))
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M 1))).hom.hom ≫
      scalarBeta l E L ι M P φ good SY goodL (targetExpression h f)  := by
  let ML : Fin 3 → sfIntegralConstructibleCategory l L Y := fun i ↦
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M i)
  let β := fun i : Fin 3 ↦ scalarSubstitution l E L ι SY (quotient l E (P i).obj)
    (substitution l E P (fun j ↦ (M j).obj) φ good (.input i))
  unfold scalarBeta
  change pullSubstitution l L f _ (tensorSubstitution l L _ _
      (goodL (.input 0)) (goodL (.input 1)) (β 0) (β 1)) ≫ _ =
    (canonicalIntegralPullbackTensor l L f (ML 0) (ML 1)).hom.hom ≫
      tensorSubstitution l L _ _ (goodL (.pullF (.input 0)))
        (goodL (.pullF (.input 1)))
        (pullSubstitution l L f _ (β 0)) (pullSubstitution l L f _ (β 1))
  exact substitution_comparison l L f (ML 0) (ML 1) _ _
    (goodL (.input 0)) (goodL (.input 1))
    (goodL (.pullF (.input 0))) (goodL (.pullF (.input 1))) (β 0) (β 1)

end WeilConjectures.CompletedQuotient
