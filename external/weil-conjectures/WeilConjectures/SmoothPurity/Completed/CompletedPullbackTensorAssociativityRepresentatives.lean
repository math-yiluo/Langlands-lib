/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCochainAssociativity
import WeilConjectures.SmoothPurity.Ringed.RingedDerivedTensorComparisonAssociativity

/-! # Associativity for coherent pullback tensor representatives

Source: Stacks 07A4, `lemma-pullback-tensor-product`, and 07A2,
`lemma-tensor-product-K-flat`.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] pullbackTensorCalculus
attribute [local implicit_reducible] pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorSystemModel
  coefficientSequenceInternalHom coefficientSequenceHasDerived CoefficientClosedStructure.tensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CochainComplex.IsKFlatIndependentCoefficients
  pullbackTensorSequenceInverse derivedInternalHomOfUniverses coefficientTotalTensor
  Functor.mapHomologicalComplex pullbackTensorSequenceCochain
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The selected calculus retains the system normalization from its resolution model.
Source: Stacks 07A4 and 0941
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem pullbackTensor_systemTensorCoherence (W : Scheme.{u}) :
    ∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _
      (pullbackTensorCalculus l E W).systemClosed.monoidal,
      Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel β) := by
  unfold pullbackTensorCalculus
  exact (coefficientDerivedSystemEvaluationCalculus l E W).choose_spec.some.systemTensorCoherence

/-- A natural localization comparison transports a pasted chain-map square.
Source: naturality and functoriality in Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem localization_comparison_paste
    {C B D A : Type*} [Category C] [Category B] [Category D] [Category A]
    (F : C ⥤ B) (G : D ⥤ A) (U : B ⥤ A) (V : C ⥤ D)
    (e : F ⋙ U ≅ V ⋙ G) {P Q : C} {R S R' S' : D}
    (a : P ⟶ Q) (b : V.obj Q ⟶ R) (c : R ⟶ S)
    (d : V.obj P ⟶ R') (j : R' ⟶ S') (a' : S' ⟶ S)
    (h : V.map a ≫ b ≫ c = d ≫ j ≫ a') :
    U.map (F.map a) ≫ (e.hom.app Q ≫ G.map b ≫ G.map c) =
      (e.hom.app P ≫ G.map d ≫ G.map j) ≫ G.map a' := by
  have he := e.hom.naturality a
  dsimp only [Functor.comp_map] at he
  simp only [← Category.assoc]
  rw [he]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ e.hom.app P ≫ G.map f) h

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem left_square {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ X' ⊗ Y') (j' : W' ⟶ V' ⊗ Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ j') :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      eW ≫ j' ≫ (i' ▷ Z') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (V, Z)) (Y := (X ⊗ Y, Z)) (i, 𝟙 Z)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, tensorHom_id] at hn
  calc
    _ = F.map j ≫ μ.hom.app (V, Z) ≫
        ((F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY)) ⊗ₘ eZ) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (V, Z) ≫ ((eV ≫ i') ⊗ₘ eZ) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ)) ≫ (i' ▷ Z') := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem right_square {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ Y' ⊗ Z') (j' : W' ⟶ X' ⊗ V')
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ j') :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      eW ≫ j' ≫ (X' ◁ i') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (X, V)) (Y := (X, Y ⊗ Z)) (𝟙 X, i)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, id_tensorHom] at hn
  calc
    _ = F.map j ≫ μ.hom.app (X, V) ≫
        (eX ⊗ₘ (F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ))) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← id_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ (eV ≫ i')) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV)) ≫ (X' ◁ i') := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem associativity_transport
    {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (l : V ≅ (X ⊗ Y) ⊗ Z) (r : W ≅ X ⊗ (Y ⊗ Z)) (a : V ⟶ W)
    (l' : V' ⟶ (X' ⊗ Y') ⊗ Z') (r' : W' ⟶ X' ⊗ (Y' ⊗ Z')) (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hB : l.hom ≫ (α_ X Y Z).hom = a ≫ r.hom)
    (hA : l' ≫ (α_ X' Y' Z').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
      (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a') :
    F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  apply (cancel_epi (F.map l.hom)).1
  apply (cancel_mono (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom))).1
  calc
    _ = F.map a ≫ F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) := by
      rw [← F.map_comp_assoc, hB, F.map_comp]
      simp only [Category.assoc]
    _ = F.map a ≫ eW ≫ r' := by rw [hR]
    _ = eV ≫ a' ≫ r' := by rw [reassoc_of% hC]
    _ = eV ≫ l' ≫ (α_ X' Y' Z').hom := by rw [hA]
    _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) ≫
          (α_ X' Y' Z').hom := by rw [reassoc_of% hL]
    _ = _ := by
      erw [associator_naturality]
      simp only [Category.assoc]
      rfl

/-- Associativity on three localized coherent K-flat representatives.
Source: Stacks 07A4, total tensor construction; 07A2, K-flat tensor products.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
Proof: total tensors of K-flat complexes are K-flat: reassociate an acyclic
test tensor and apply the two K-flat criteria. Apply the normalization of the
coherent comparison to (A,B), (B,C), (A tensor B,C) and (A,B tensor C), and
use preservation of K-flatness by the sequence inverse image. In every triple
degree both ordinary paths send the adjunction-unit image of (x tensor y)
tensor z to the tensor of the unit images of x, y and z, with parentheses on
the right. Naturality of the unit and the two normalized pure-tensor formulas
identify these sections. Reassociation introduces no permutation or extra sign
and commutes with all three signed differential terms. Tensor sheafification
and the total coproduct injections detect equality, so the chain maps agree.
Apply the derived quotient and insert the fixed tensor-model and exact-pullback
factorization isomorphisms. Their naturality cancels the intermediate maps;
the model associators identify the remaining reassociation maps with the
specified derived associators. This proves the equation on the displayed
representatives; extension to arbitrary derived objects is a separate step. -/
theorem completedPullbackTensor_associativity_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A B C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) B)
    (hC : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) C) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.associator M N P).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (M,(pullbackTensorCalculus l E Y).systemClosed.tensor.obj (N,P)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((pullbackTensorSystemComparison l E f).hom.app (N,P))) =
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N),P) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorSystemComparison l E f).hom.app (M,N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l E X).systemClosed.monoidal.associator
        ((pullbackTensorSequenceDerived l E f).obj M)
        ((pullbackTensorSequenceDerived l E f).obj N)
        ((pullbackTensorSequenceDerived l E f).obj P)).hom := by
  let J := coefficientSequenceTopology (ProEt.topology Y)
  let R := coefficientSequenceCommRingSheaf l E Y
  let J' := coefficientSequenceTopology (ProEt.topology X)
  let R' := coefficientSequenceCommRingSheaf l E X
  let U := pullbackTensorSequenceInverse l E f
  let F := pullbackTensorSequenceDerived l E f
  let SB := (pullbackTensorCalculus l E Y).systemClosed
  let TB := (pullbackTensorCalculus l E Y).systemTensorModel
  let SA := (pullbackTensorCalculus l E X).systemClosed
  let TA := (pullbackTensorCalculus l E X).systemTensorModel
  let μ := pullbackTensorSystemComparison l E f
  let ρ := fun M N ↦ μ.app (M, N)
  let T := coefficientTotalTensor.{u, u + 1, u} J R
  obtain ⟨βB, ⟨cB⟩⟩ := pullbackTensor_systemTensorCoherence l E Y
  obtain ⟨βA, ⟨cA⟩⟩ := pullbackTensor_systemTensorCoherence l E X
  have hρ : ∀ (M N M' N' : coefficientSequenceDerived l E Y)
      (g : M ⟶ M') (h : N ⟶ N'),
      F.map (SB.tensor.map (X := (M, N)) (Y := (M', N')) (g, h)) ≫ (ρ M' N').hom =
        (ρ M N).hom ≫ SA.tensor.map
          (X := (F.obj M, F.obj N)) (Y := (F.obj M', F.obj N')) (F.map g, F.map h) := by
    intro M N M' N' g h
    have hμ := μ.hom.naturality (X := (M, N)) (Y := (M', N')) (Prod.mkHom g h)
    dsimp only [Functor.comp_map, Functor.prod_map] at hμ
    exact hμ
  have hc : CategoryTheory.RingedForgetTensorTransposition.RingedTensorComparisonCoherence.{
      u + 1, u, u, u + 1, u, u}
      J R J' R' U (pullbackTensorSequenceCochain l E f) :=
    ⟨completedPullbackTensor_cochain_associativity l E f⟩
  have hAB := coefficientTotalTensor_isKFlat.{u, u + 1, u} J R A B hA hB
  have hBC := coefficientTotalTensor_isKFlat.{u, u + 1, u} J R B C hB hC
  refine ringedDerivedTensorComparison_associativity.{u + 1, u, u, u + 2, u + 1, u, u, u + 2}
    J R SB TB J' R' SA TA U F U.mapDerivedCategoryFactors ρ hρ
    (pullbackTensorSequenceCochain l E f) hc cB cA ?_ A B C hA hB hC
    (pullbackTensorSequenceGood l E f A hA)
    (pullbackTensorSequenceGood l E f B hB)
    (pullbackTensorSequenceGood l E f C hC)
    (pullbackTensorSequenceGood l E f (T.obj (A, B)) hAB)
    (pullbackTensorSequenceGood l E f (T.obj (B, C)) hBC)
  intro P Q hP hQ hUP hUQ
  exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ

end WeilConjectures
