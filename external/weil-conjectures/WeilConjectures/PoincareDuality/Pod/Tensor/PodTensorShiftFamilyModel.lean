/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorSignedShiftTowers
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRepresentativeShiftIsos
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

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

private theorem transportShiftIso
    {D B : Type*} [Category D] [Category B]
    (S : D ⥤ D) (H : B ⥤ B) (T : D ⥤ B) (i : S ⋙ T ≅ T ⋙ H)
    {X X' M M' : D} (e : X' ⟶ S.obj X) (f : X ⟶ M)
    (f' : X' ⟶ M') (a : M' ⟶ S.obj M)
    (h : f' ≫ a = e ≫ S.map f) :
    T.map f' ≫ T.map a ≫ i.hom.app M =
      (T.map e ≫ i.hom.app X) ≫ H.map (T.map f) := by
  rw [← T.map_comp_assoc, h, T.map_comp, Category.assoc]
  have hn := i.hom.naturality f
  change T.map (S.map f) ≫ i.hom.app M = i.hom.app X ≫ H.map (T.map f) at hn
  rw [hn, ← Category.assoc]

private theorem transportShiftIso_hom
    {D B : Type*} [Category D] [Category B]
    (S : D ⥤ D) (H : B ⥤ B) (T : D ⥤ B) (i : S ⋙ T ≅ T ⋙ H)
    {X X' M M' : D} (e : X' ⟶ S.obj X) (f : X ⟶ M)
    (f' : X' ⟶ M') (a : M' ≅ S.obj M)
    (h : f' ≫ a.hom = e ≫ S.map f) :
    T.map f' ≫ (T.mapIso a ≪≫ i.app M).hom =
      (T.map e ≫ i.hom.app X) ≫ H.map (T.map f) := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    transportShiftIso S H T i e f f' a.hom h

/-- Shift either derived input of the completed tensor.
Source: construction (blueprint: lem-pod-tensor-shift-family-model). -/
abbrev podTensorDerivedShiftFamily (W : Scheme.{u}) :=
  ∀ (r : ℤ) (right : Bool),
    podTensorRepresentativePairOf
        (shiftFunctor (DerivedCategory (integralTowerModules l E W)) r) right ⋙
        integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor _ r

/-- Representative normalization of a derived tensor shift family.
Source: blueprint dual-Tate Steps 1 and 5
(blueprint: lem-pod-tensor-shift-family-model). -/
def podTensorDerivedShiftFamilyNormalization (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws)
    (i : podTensorDerivedShiftFamily l E W) : Prop :=
  let T := integralCompletedTensor l E W
  let α := integralCompletedTensorComparison l E W
  ∀ (r : ℤ) (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
    (T.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso r).hom.app P.obj)
        (𝟙 (DerivedCategory.Q.obj Q.obj))) ≫
        (i r false).hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      α.hom.app ((podTensorGoodShiftFunctor l E W r).obj P, Q) ≫
        (podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r false).hom.app (P, Q) ≫
          (α.inv.app (P, Q))⟦r⟧') ∧
    (T.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj))
        ((DerivedCategory.Q.commShiftIso r).hom.app Q.obj)) ≫
        (i r true).hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      α.hom.app (P, (podTensorGoodShiftFunctor l E W r).obj Q) ≫
        (podTensorRepresentativeOnGoodShiftIso l E W ρ hρ r true).hom.app (P, Q) ≫
          (α.inv.app (P, Q))⟦r⟧')

private abbrev pairShift (C : Type*) [Category C] [HasShift C ℤ] (r : ℤ) (right : Bool) :
    C × C ⥤ C × C :=
  podTensorRepresentativePairOf (shiftFunctor C r) right

private def leftInputIso (W : Scheme.{u})
    (M N M' : sfIntegralConstructibleCategory l E W) (r : ℤ)
    (a : M'.obj ≅ M.obj⟦r⟧) :
    (M'.obj, N.obj) ≅
      (pairShift (DerivedCategory (integralTowerModules l E W)) r false).obj (M.obj, N.obj) :=
  a.prod (Iso.refl N.obj)

private def rightInputIso (W : Scheme.{u})
    (M N N' : sfIntegralConstructibleCategory l E W) (r : ℤ)
    (b : N'.obj ≅ N.obj⟦r⟧) :
    (M.obj, N'.obj) ≅
      (pairShift (DerivedCategory (integralTowerModules l E W)) r true).obj (M.obj, N.obj) :=
  (Iso.refl M.obj).prod b

private theorem leftInputIso_hom (W : Scheme.{u})
    (M N M' : sfIntegralConstructibleCategory l E W) (r : ℤ)
    (a : M'.obj ≅ M.obj⟦r⟧) :
    (leftInputIso l E W M N M' r a).hom = Prod.mkHom a.hom (𝟙 N.obj) := by rfl

private theorem rightInputIso_hom (W : Scheme.{u})
    (M N N' : sfIntegralConstructibleCategory l E W) (r : ℤ)
    (b : N'.obj ≅ N.obj⟦r⟧) :
    (rightInputIso l E W M N N' r b).hom = Prod.mkHom (𝟙 M.obj) b.hom := by rfl

private def leftOfShiftFamily (W : Scheme.{u}) (i : podTensorDerivedShiftFamily l E W) :
    PodTensorDerivedShiftLeft l E W := fun M N M' r a ↦
  (integralCompletedTensor l E W).mapIso (leftInputIso l E W M N M' r a) ≪≫
    (i r false).app (M.obj, N.obj)

private def rightOfShiftFamily (W : Scheme.{u}) (i : podTensorDerivedShiftFamily l E W) :
    PodTensorDerivedShiftRight l E W := fun M N N' r b ↦
  (integralCompletedTensor l E W).mapIso (rightInputIso l E W M N N' r b) ≪≫
    (i r true).app (M.obj, N.obj)

private theorem normalization_comp {C : Type*} [Category C]
    {A B B₁ B₂ D F G : C}
    {t : A ⟶ F} {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ F}
    {b₁ : B ⟶ B₁} {b₂ : B₁ ⟶ B₂} {b₃ : B₂ ⟶ D}
    (ht : t = a ≫ b ≫ c) (hb : b = b₁ ≫ b₂ ≫ b₃)
    (d : F ⟶ G) :
    t ≫ d = a ≫ b₁ ≫ b₂ ≫ b₃ ≫ c ≫ d := by
  rw [ht, hb]
  simp only [Category.assoc]

/-- A normalized natural shift family determines both fields of the signed model.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4 and 011G
(blueprint: lem-pod-tensor-shift-family-model).

Proof: precompose each natural comparison with the tensor image of the given
input identification and the identity. The presentation equation replaces that
composite by the canonical localization shift followed by the shifted unprimed
presentation. Apply naturality of the family and its representative normalization.
The representative component formula yields exactly the two Model equations. -/
theorem podTensorDerivedShiftFamily_model (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws)
    (i : podTensorDerivedShiftFamily l E W)
    (hi : podTensorDerivedShiftFamilyNormalization l E W ρ hρ i) :
    ∃ L : PodTensorDerivedShiftLeft l E W, ∃ R : PodTensorDerivedShiftRight l E W,
      (podTensorSignedShiftOfDerived l E W L R).Model l E ρ := by
  refine ⟨leftOfShiftFamily l E W i, rightOfShiftFamily l E W i, ?_⟩
  let T := integralCompletedTensor l E W
  let D := DerivedCategory (integralTowerModules l E W)
  intro P S r M N M' N' eP eS eP' eS' a b ha hb
  constructor
  · have h := transportShiftIso_hom (pairShift D r false) (shiftFunctor D r) T (i r false)
      (Prod.mkHom ((DerivedCategory.Q.commShiftIso r).hom.app P.obj)
        (𝟙 (DerivedCategory.Q.obj S.obj)))
      (Prod.mkHom eP.hom eS.hom) (Prod.mkHom eP'.hom eS.hom)
      (leftInputIso l E W M N M' r a) (by
        rw [leftInputIso_hom]
        apply CategoryTheory.Prod.hom_ext
        · exact ha
        · change eS.hom ≫ 𝟙 _ = 𝟙 _ ≫ eS.hom
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have hx := (hi r P S).1
    change T.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso r).hom.app P.obj)
      (𝟙 (DerivedCategory.Q.obj S.obj))) ≫
      (i r false).hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj S.obj) = _ at hx
    have hn := (podTensorRepresentativeShift_isos l E W ρ hρ r P S).1
    exact h.trans (normalization_comp hx hn _)
  · have h := transportShiftIso_hom (pairShift D r true) (shiftFunctor D r) T (i r true)
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj))
        ((DerivedCategory.Q.commShiftIso r).hom.app S.obj))
      (Prod.mkHom eP.hom eS.hom) (Prod.mkHom eP.hom eS'.hom)
      (rightInputIso l E W M N N' r b) (by
        rw [rightInputIso_hom]
        apply CategoryTheory.Prod.hom_ext
        · change eP.hom ≫ 𝟙 _ = 𝟙 _ ≫ eP.hom
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        · exact hb)
    have hx := (hi r P S).2
    change T.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj))
      ((DerivedCategory.Q.commShiftIso r).hom.app S.obj)) ≫
      (i r true).hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj S.obj) = _ at hx
    have hn := (podTensorRepresentativeShift_isos l E W ρ hρ r P S).2
    exact h.trans (normalization_comp hx hn _)

end WeilConjectures
