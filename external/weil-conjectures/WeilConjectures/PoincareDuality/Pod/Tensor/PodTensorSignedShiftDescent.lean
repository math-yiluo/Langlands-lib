/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorSignedShiftTowers
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorShiftFamilyModel

/-! # Descent of strict signed tensor shifts to the completed tensor

The strict tower maps and their generator rules are already fixed. The remaining
step extends their Roos-normalized localizations to the completed derived tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] podTensorRepresentativeOnGoodShiftIso

attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos
  podTensorStrictShiftLeftIso podTensorStrictShiftRightIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev pairOf {C : Type*} [Category C] (S : C ⥤ C) (right : Bool) :
    C × C ⥤ C × C :=
  if right then (𝟭 C).prod S else S.prod (𝟭 C)

private abbrev pairShift (C : Type*) [Category C] [HasShift C ℤ] (r : ℤ) (right : Bool) :
    C × C ⥤ C × C :=
  pairOf (shiftFunctor C r) right

private theorem descendShiftIso
    {C D B : Type*} [Category C] [Category D] [Category B]
    (L : C ⥤ D) (T : D ⥤ B) (K : C ⥤ B) (α : L ⋙ T ≅ K)
    (s : C ⥤ C) (S : D ⥤ D) (H : B ⥤ B) (e : s ⋙ L ≅ L ⋙ S)
    (β : s ⋙ K ≅ K ⋙ H)
    (ff : ((Functor.whiskeringLeft C D B).obj L).FullyFaithful) :
    ∃ i : S ⋙ T ≅ T ⋙ H, ∀ X : C,
      T.map (e.hom.app X) ≫ i.hom.app (L.obj X) =
        α.hom.app (s.obj X) ≫ β.hom.app X ≫ H.map (α.inv.app X) := by
  let j : L ⋙ S ⋙ T ≅ L ⋙ T ⋙ H :=
    isoWhiskerRight e.symm T ≪≫ isoWhiskerLeft s α ≪≫ β ≪≫
      isoWhiskerRight α.symm H
  let i : S ⋙ T ≅ T ⋙ H := ff.preimageIso j
  refine ⟨i, fun X ↦ ?_⟩
  have hi := NatTrans.congr_app (ff.map_preimage j.hom) X
  change i.hom.app (L.obj X) = _ at hi
  rw [hi]
  dsimp only [j, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Iso.symm_hom]
  rw [← T.map_comp_assoc, e.hom_inv_id_app, T.map_id, Category.id_comp]

private abbrev goodShift (W : Scheme.{u}) (r : ℤ) :
    (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      (integralOperationsGoodComplex l E W).FullSubcategory :=
  podTensorGoodShiftFunctor l E W r

private def goodShiftQ (W : Scheme.{u}) (r : ℤ) :
    goodShift l E W r ⋙ integralOperationsGoodLocalization l E W ≅
      integralOperationsGoodLocalization l E W ⋙ shiftFunctor _ r :=
  NatIso.ofComponents (fun P ↦ (DerivedCategory.Q.commShiftIso r).app P.obj)
    (fun f ↦ (DerivedCategory.Q.commShiftIso r).hom.naturality f.hom)

private def pairComparison {C D : Type*} [Category C] [Category D]
    (s : C ⥤ C) (S : D ⥤ D) (F : C ⥤ D) (e : s ⋙ F ≅ F ⋙ S) (right : Bool) :
    pairOf s right ⋙ F.prod F ≅ F.prod F ⋙ pairOf S right := by
  cases right
  · exact NatIso.ofComponents
      (fun P ↦ Iso.prod (e.app P.1) (Iso.refl _)) (by
        intro P Q f
        ext
        · exact e.hom.naturality f.1
        · change F.map f.2 ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.2
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
  · exact NatIso.ofComponents
      (fun P ↦ Iso.prod (Iso.refl _) (e.app P.2)) (by
        intro P Q f
        ext
        · change F.map f.1 ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.1
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        · exact e.hom.naturality f.2)

/-- Descend the two already fixed strict tensor shift maps to the completed derived
tensor, retaining the normalization on every good representative.

Source: Stacks 07A4 (descent on K-flat representatives), 011G (signed shifts),
and 0941 (the Roos model); blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: lem-pod-tensor-signed-shift-descent).

Proof: good complexes are stable under shifts by podTensorGoodShift. For each
integer r, form the natural isomorphisms on pairs of good complexes by composing
the representative comparison, the explicit strict tower shift, the given signed
Roos shift, the localization shift, and the inverse shifted representative
comparison. Naturality of the tower maps follows from their finite summand
formulas. Naturality of the signed Roos map follows by composing with the two
cone projections: its two defining laws give the same maps on both coordinates,
and these coordinates jointly determine a map of the underlying graded objects.
The product of good-representative localizations is a localization. Its fully
faithful precomposition therefore uniquely extends these natural isomorphisms
to the completed derived tensor. For arbitrary identifications a and b of shifted
inputs, precompose the extended maps with the tensor of a or b and the identity.
Naturality with respect to eP, eQ, eP', eQ' and the two given equations identifying
a and b with the localization shifts gives exactly both equations of Model.
The construction works for all integer shifts and requires no boundedness of the
good representatives. It uses the specified Roos comparison, not an independently
chosen shift. -/
theorem podTensorSignedShiftDescent (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws) :
    ∃ L : PodTensorDerivedShiftLeft l E W, ∃ R : PodTensorDerivedShiftRight l E W,
      (podTensorSignedShiftOfDerived l E W L R).Model l E ρ := by
  classical
  let G := integralOperationsGoodComplex l E W
  let Q := integralOperationsGoodLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage G.ι
  have : Q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  let T := integralCompletedTensor l E W
  let K := integralOperationsTensorOnGood l E W
  let α := integralCompletedTensorComparison l E W
  let D := DerivedCategory (integralTowerModules l E W)
  have d (r : ℤ) (right : Bool) :
      ∃ i : pairShift D r right ⋙ T ≅ T ⋙ shiftFunctor _ r,
        ∀ X : G.FullSubcategory × G.FullSubcategory,
          T.map ((pairComparison (goodShift l E W r) (shiftFunctor D r) Q
            (goodShiftQ l E W r) right).hom.app X) ≫ i.hom.app ((Q.prod Q).obj X) =
          α.hom.app ((pairOf (goodShift l E W r) right).obj X) ≫
            (podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r right).hom.app X ≫
              (α.inv.app X)⟦r⟧' := by
    exact descendShiftIso (Q.prod Q) T K α (pairOf (goodShift l E W r) right)
      (pairShift D r right) (shiftFunctor D r)
      (pairComparison (goodShift l E W r) (shiftFunctor D r) Q (goodShiftQ l E W r) right)
      (podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r right)
      (Localization.fullyFaithfulWhiskeringLeft (Q.prod Q) (V.prod V) D)
  choose i hi using d
  apply podTensorDerivedShiftFamily_model l E W ρ hρ i
  intro r P Q
  exact ⟨hi r false (P, Q), hi r true (P, Q)⟩

end WeilConjectures
