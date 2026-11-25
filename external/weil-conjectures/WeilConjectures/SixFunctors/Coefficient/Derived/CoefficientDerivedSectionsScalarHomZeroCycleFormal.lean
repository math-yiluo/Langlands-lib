/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus

/-! # Global elements of the enriched adjunction map

A formal computation: the image of a global element `τ : U ⟶ Hom(P, G M)` under the
enriched adjunction map followed by a sections comparison is the transpose of an explicit
map out of a tensor product, once the scalar unit is known on the global unit class.

Source: Stacks Project, Tags 08J9 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
universe a b c d v w r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

/-- Applying the images of two composable morphisms under an additive-group valued functor.
Source: functoriality (auxiliary; not a blueprint node). -/
theorem _root_.CategoryTheory.Functor.map_comp_apply_addCommGrp {C : Type*} [Category* C]
    (H : C ⥤ AddCommGrpCat.{c}) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (y : H.obj X) :
    H.map g (H.map f y) = H.map (f ≫ g) y := by
  rw [Functor.map_comp, ConcreteCategory.comp_apply]

/-- The inverse transpose is natural in the target.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
theorem CoefficientClosedStructure.transpose_symm_comp_map {T P Q Q' : A}
    (τ : T ⟶ HA.obj (op P, Q)) (e : Q ⟶ Q') :
    (SA.transpose T P Q').symm (τ ≫ HA.map (Prod.mkHom (𝟙 (op P)) e)) =
      (SA.transpose T P Q).symm τ ≫ e :=
  (SA.adjunction P).homEquiv_naturality_right_symm τ e

/-- The base-change map applied to a global element is the transpose of the scalar
extension of its inverse transpose.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
theorem coefficientBaseChangeHom_comp {UA P Q : A} {UB Q' : B}
    (m : UB ⟶ F.obj UA) (τ : UA ⟶ HA.obj (op P, Q)) (g : F.obj Q ⟶ Q') :
    m ≫ F.map τ ≫ coefficientBaseChangeHom SA SB F μ P Q ≫
        HB.map (Prod.mkHom (𝟙 (op (F.obj P))) g) =
      SB.transpose UB (F.obj P) Q'
        (SB.tensor.map (Prod.mkHom m (𝟙 (F.obj P))) ≫ μ.inv.app (UA, P) ≫
          F.map ((SA.transpose UA P Q).symm τ) ≫ g) := by
  rw [coefficientBaseChangeHom, ← Category.assoc, SB.comp_transpose_comp]
  congr 1
  have h1 : SB.tensor.map (Prod.mkHom (m ≫ F.map τ) (𝟙 (F.obj P))) =
      SB.tensor.map (Prod.mkHom m (𝟙 (F.obj P))) ≫
        SB.tensor.map (Prod.mkHom (F.map τ) (F.map (𝟙 P))) := by
    rw [← Functor.map_comp, F.map_id]
    congr 1
    ext <;> simp
  have h2 := μ.inv.naturality (Prod.mkHom τ (𝟙 P))
  dsimp only [Functor.comp_map, Functor.prod_map] at h2
  rw [h1]
  simp only [Category.assoc]
  rw [reassoc_of% h2, SA.transpose_symm_apply, F.map_comp, Category.assoc]

/-- The image of a global element under the enriched adjunction map followed by a sections
comparison, given the image of the global unit class under the adjunction unit.
Source: Stacks 08J9, 07A6 (auxiliary; not a blueprint node). -/
theorem coefficientEnrichedAdjunctionMap_globalElement {D : Type d} [Category.{r} D]
    (ΓA : A ⥤ D) (ΓB : B ⥤ D) (K : D ⥤ AddCommGrpCat.{c}) (ss : G ⋙ ΓA ⟶ ΓB)
    {UA : A} {UB : B} (uA : K.obj (ΓA.obj UA)) (uB : K.obj (ΓB.obj UB)) (m : UB ⟶ F.obj UA)
    (hU : K.map (ΓA.map (adj.unit.app UA) ≫ ss.app (F.obj UA)) uA = K.map (ΓB.map m) uB)
    (P : A) (M : B) (τ : UA ⟶ HA.obj (op P, G.obj M)) :
    K.map (ΓA.map (coefficientEnrichedAdjunctionMap SA SB F adj μ P M) ≫
        ss.app (HB.obj (op (F.obj P), M))) (K.map (ΓA.map τ) uA) =
      K.map (ΓB.map (SB.transpose UB (F.obj P) M
        (SB.tensor.map (Prod.mkHom m (𝟙 (F.obj P))) ≫ μ.inv.app (UA, P) ≫
          F.map ((SA.transpose UA P (G.obj M)).symm τ) ≫ adj.counit.app M))) uB := by
  have h1 : τ ≫ coefficientEnrichedAdjunctionMap SA SB F adj μ P M = adj.unit.app UA ≫
      G.map (F.map τ ≫ coefficientBaseChangeHom SA SB F μ P (G.obj M) ≫
        HB.map (Prod.mkHom (𝟙 (op (F.obj P))) (adj.counit.app M))) := by
    rw [coefficientEnrichedAdjunctionMap, ← adj.homEquiv_naturality_left, adj.homEquiv_unit]
  have h2 : ΓA.map (G.map (F.map τ ≫ coefficientBaseChangeHom SA SB F μ P (G.obj M) ≫
        HB.map (Prod.mkHom (𝟙 (op (F.obj P))) (adj.counit.app M)))) ≫
      ss.app (HB.obj (op (F.obj P), M)) = ss.app (F.obj UA) ≫
        ΓB.map (F.map τ ≫ coefficientBaseChangeHom SA SB F μ P (G.obj M) ≫
          HB.map (Prod.mkHom (𝟙 (op (F.obj P))) (adj.counit.app M))) :=
    ss.naturality _
  rw [Functor.map_comp_apply_addCommGrp, ← Category.assoc, ← ΓA.map_comp, h1, ΓA.map_comp,
    Category.assoc, h2, ← Category.assoc, ← Functor.map_comp_apply_addCommGrp]
  erw [hU]
  rw [Functor.map_comp_apply_addCommGrp, ← ΓB.map_comp, coefficientBaseChangeHom_comp]
  rfl

/-- The scalar transpose formula for global elements, from its representative inputs:
the unit-class equation, the transport of the evaluation of transposes along a model of
the scalar extension, and the compatibility of the left unitors.
Source: Stacks 08J9, 07A6, 08JA (auxiliary; not a blueprint node). -/
theorem coefficientEnrichedAdjunctionMap_homZero {D : Type d} [Category.{r} D]
    (ΓA : A ⥤ D) (ΓB : B ⥤ D) (K : D ⥤ AddCommGrpCat.{c}) (ss : G ⋙ ΓA ⟶ ΓB)
    (eB : ∀ X Y : B, K.obj (ΓB.obj (HB.obj (op X, Y))) → (X ⟶ Y))
    {UA P N : A} {UB P' M : B} (uA : K.obj (ΓA.obj UA)) (uB : K.obj (ΓB.obj UB))
    (m : UB ⟶ F.obj UA)
    (hU : K.map (ΓA.map (adj.unit.app UA) ≫ ss.app (F.obj UA)) uA = K.map (ΓB.map m) uB)
    (pP : F.obj P ≅ P')
    (hnat : ∀ y, eB P' M (K.map (ΓB.map (HB.map (Prod.mkHom pP.inv.op (𝟙 M)))) y) =
      pP.inv ≫ eB (F.obj P) M y ≫ 𝟙 M)
    (lB : P' ⟶ SB.tensor.obj (UB, P'))
    (h4 : ∀ X : SB.tensor.obj (UB, P') ⟶ M,
      eB P' M (K.map (ΓB.map (SB.transpose UB P' M X)) uB) = lB ≫ X)
    (lA : P ⟶ SA.tensor.obj (UA, P))
    (hW : pP.hom ≫ lB ≫ SB.tensor.map (Prod.mkHom m pP.inv) ≫ μ.inv.app (UA, P) = F.map lA)
    (τ : UA ⟶ HA.obj (op P, N)) (e : N ⟶ G.obj M)
    (x : K.obj (ΓA.obj (HA.obj (op P, G.obj M))))
    (hx : x = K.map (ΓA.map (τ ≫ HA.map (Prod.mkHom (𝟙 (op P)) e))) uA)
    (y : P ⟶ G.obj M) (hy : y = lA ≫ (SA.transpose UA P N).symm τ ≫ e) :
    eB (F.obj P) M (K.map (ΓA.map (coefficientEnrichedAdjunctionMap SA SB F adj μ P M) ≫
        ss.app (HB.obj (op (F.obj P), M))) x) = (adj.homEquiv P M).symm y := by
  subst hx hy
  rw [coefficientEnrichedAdjunctionMap_globalElement SA SB F adj μ ΓA ΓB K ss uA uB m hU]
  have h1 := hnat (K.map (ΓB.map (SB.transpose UB (F.obj P) M
    (SB.tensor.map (Prod.mkHom m (𝟙 (F.obj P))) ≫ μ.inv.app (UA, P) ≫
      F.map ((SA.transpose UA P (G.obj M)).symm (τ ≫ HA.map (Prod.mkHom (𝟙 (op P)) e))) ≫
        adj.counit.app M))) uB)
  rw [Functor.map_comp_apply_addCommGrp, ← ΓB.map_comp, SB.transpose_comp_map_op, h4,
    Category.comp_id] at h1
  rw [← cancel_epi pP.inv, ← h1, Adjunction.homEquiv_counit,
    SA.transpose_symm_comp_map]
  have hT : SB.tensor.map (Prod.mkHom (𝟙 UB) pP.inv) ≫ SB.tensor.map (Prod.mkHom m (𝟙 (F.obj P))) =
      SB.tensor.map (Prod.mkHom m pP.inv) := by
    rw [← Functor.map_comp]
    congr 1
    ext <;> simp
  have hW' : lB ≫ SB.tensor.map (Prod.mkHom m pP.inv) ≫ μ.inv.app (UA, P) = pP.inv ≫ F.map lA := by
    rw [← hW, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hT, reassoc_of% hW']
  simp only [Functor.map_comp, Category.assoc]

end WeilConjectures
