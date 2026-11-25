/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteSignedShifts
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Equations for the fixed finite tensor shift maps

The generator and quotient equations concern the explicit maps of
`PodTensorFiniteSignedShifts`; no tensor shift data is chosen here.
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] integralOperationsFiniteHasMap

private theorem shiftSection_heq (W : Scheme.{u}) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E W n) ℤ)
    (r i j : ℤ) (h : j = i + r) (U : W.ProEtᵒᵖ) (z : (K.X j).val.obj U) :
    HEq (((CochainComplex.shiftFunctorObjXIso K r i j h).inv).val.app U z) z := by
  subst j
  rfl

private theorem finiteShiftLeft_generators (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q r : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X (p + r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    HEq (((podTensorFiniteShiftLeft l E W n P Q r).hom.f (p + q)).val.app U
      (integralOperationsTotalTensorSection l E W n (P⟦r⟧) Q p q U x y))
      (integralOperationsTotalTensorSection l E W n P Q (p + r) q U x y) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let := integralCoefficientAbSheafify.{u, u} W
  let := integralCoefficientAbLocallyBijective.{u, u} W
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)
  let : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  let : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf l E W n)
  let F := unrestrictedIntegralFiniteComplex l E W n
  let T := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)
  let B := Functor.uncurry.obj T.map₂CochainComplex
  let e := (F.commShiftIso r).app P
  have hm :
      CochainComplex.ιMapBifunctor (F.obj (P⟦r⟧)) (F.obj Q) T p q (p + q) rfl ≫
        (B.map (Prod.mkHom e.hom (𝟙 (F.obj Q)))).f (p + q) =
      CochainComplex.ιMapBifunctor ((F.obj P)⟦r⟧) (F.obj Q) T p q (p + q) rfl := by
    dsimp only [B]
    rw [TensorTotalProof.totalTensor_map]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    change (T.map (𝟙 _)).app _ ≫ (T.obj _).map (𝟙 _) ≫ _ = _
    rw [T.map_id, NatTrans.id_app, (T.obj _).map_id, Category.id_comp, Category.id_comp]
    rfl
  let σ := CochainComplex.mapBifunctorShift₁Iso (F.obj P) (F.obj Q) T r
  have hc :
      CochainComplex.ιMapBifunctor (F.obj (P⟦r⟧)) (F.obj Q) T p q (p + q) rfl ≫
        (B.map (Prod.mkHom e.hom (𝟙 (F.obj Q))) ≫ σ.hom).f (p + q) =
      CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q) T (p + r) q ((p + r) + q) rfl ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mapBifunctor (F.obj P) (F.obj Q) T)
          r (p + q) ((p + r) + q) (by omega)).inv := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, hm]
    have hh := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f
      (F.obj P) (F.obj Q) T r p q (p + q) rfl (p + r) ((p + r) + q) rfl (by omega)
    change _ = (T.map (𝟙 _)).app _ ≫ _ ≫ _ at hh
    rw [T.map_id, NatTrans.id_app, Category.id_comp] at hh
    exact hh
  have hv := congrArg (fun f ↦ f.val.app U
    (integralOperationsTensorSection l E W n _ _ U x y)) hc
  change HEq _ _
  exact (heq_of_eq hv).trans (shiftSection_heq l E W n _ r (p + q) ((p + r) + q)
    (by omega) U (integralOperationsTotalTensorSection l E W n P Q (p + r) q U x y))

private theorem shiftSection_hom_heq (W : Scheme.{u}) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E W n) ℤ)
    (r i j : ℤ) (h : j = i + r) (U : W.ProEtᵒᵖ)
    {A : integralOperationsFiniteModules l E W n} (f : A ⟶ K.X j)
    (s : ℤˣ) (z : A.val.obj U) :
    HEq (((s • f ≫ (CochainComplex.shiftFunctorObjXIso K r i j h).inv).val.app U) z)
      (s • f.val.app U z) := by
  subst j
  rcases Int.units_eq_one_or s with (rfl | rfl)
  · simp only [one_smul, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, Category.comp_id]
    rfl
  · simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso_refl,
      Iso.refl_inv, Category.comp_id]
    apply heq_of_eq
    rw [show (-f).val = -f.val from (SheafOfModules.forget _).map_neg (f := f)]
    rfl

private theorem rightShift_ι {A : Type a} [Category.{b} A] [Preadditive A]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ P Q : CochainComplex A ℤ, CochainComplex.HasMapBifunctor P Q T]
    (P Q : CochainComplex A ℤ) (p q r : ℤ) :
    CochainComplex.ιMapBifunctor P (Q⟦r⟧) T p q (p + q) rfl ≫
      (CochainComplex.mapBifunctorShift₂Iso P Q T r).hom.f (p + q) =
    (p * r).negOnePow •
      CochainComplex.ιMapBifunctor P Q T p (q + r) (p + (q + r)) rfl ≫
      (CochainComplex.shiftFunctorObjXIso (CochainComplex.mapBifunctor P Q T)
        r (p + q) (p + (q + r)) (by omega)).inv := by
  have h := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    P Q T r p q (p + q) rfl (q + r) (p + (q + r)) rfl (by omega)
  change _ = (p * r).negOnePow • (T.obj (P.X p)).map (𝟙 _) ≫ _ ≫ _ at h
  rw [(T.obj (P.X p)).map_id] at h
  change _ = (p * r).negOnePow •
    ((𝟙 ((T.obj (P.X p)).obj (Q.X (q + r)))) ≫
      CochainComplex.ιMapBifunctor P Q T p (q + r) (p + (q + r)) rfl ≫
      (CochainComplex.shiftFunctorObjXIso (CochainComplex.mapBifunctor P Q T)
        r (p + q) (p + (q + r)) (by omega)).inv) at h
  rw [Category.id_comp] at h
  exact h

private theorem finiteShiftRight_generators (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q r : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X (q + r)).val.obj U) :
    HEq (((podTensorFiniteShiftRight l E W n P Q r).hom.f (p + q)).val.app U
      (integralOperationsTotalTensorSection l E W n P (Q⟦r⟧) p q U x y))
      ((p * r).negOnePow • integralOperationsTotalTensorSection l E W n P Q p (q + r) U x y) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let := integralCoefficientAbSheafify.{u, u} W
  let := integralCoefficientAbLocallyBijective.{u, u} W
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)
  let : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  let : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf l E W n)
  let F := unrestrictedIntegralFiniteComplex l E W n
  let T := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)
  let B := Functor.uncurry.obj T.map₂CochainComplex
  let e := (F.commShiftIso r).app Q
  have hm :
      CochainComplex.ιMapBifunctor (F.obj P) (F.obj (Q⟦r⟧)) T p q (p + q) rfl ≫
        (B.map (Prod.mkHom (𝟙 (F.obj P)) e.hom)).f (p + q) =
      CochainComplex.ιMapBifunctor (F.obj P) ((F.obj Q)⟦r⟧) T p q (p + q) rfl := by
    dsimp only [B]
    rw [TensorTotalProof.totalTensor_map]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    change (T.map (𝟙 _)).app _ ≫ (T.obj _).map (𝟙 _) ≫ _ = _
    rw [T.map_id, NatTrans.id_app, (T.obj _).map_id, Category.id_comp, Category.id_comp]
    rfl
  let σ := CochainComplex.mapBifunctorShift₂Iso (F.obj P) (F.obj Q) T r
  have hc :
      CochainComplex.ιMapBifunctor (F.obj P) (F.obj (Q⟦r⟧)) T p q (p + q) rfl ≫
        (B.map (Prod.mkHom (𝟙 (F.obj P)) e.hom) ≫ σ.hom).f (p + q) =
      (p * r).negOnePow •
        CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q) T p (q + r) (p + (q + r)) rfl ≫
        (CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mapBifunctor (F.obj P) (F.obj Q) T)
          r (p + q) (p + (q + r)) (by omega)).inv := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, hm]
    exact rightShift_ι T (F.obj P) (F.obj Q) p q r
  have hv := congrArg (fun f ↦ f.val.app U
    (integralOperationsTensorSection l E W n _ _ U x y)) hc
  change HEq _ _
  exact (heq_of_eq hv).trans (shiftSection_hom_heq l E W n _ r (p + q) (p + (q + r))
    (by omega) U _ (p * r).negOnePow (integralOperationsTensorSection l E W n _ _ U x y))

/-- The two explicit finite tensor shifts have their prescribed homogeneous
section formulas for every integer shift.

Source: Stacks 011G, 07A4; more-algebra.tex, item-shift-tensor
(blueprint: lem-pod-tensor-finite-signed-shift-laws).

Proof: apply the two Mathlib total-tensor summand formulas after the ordinary
reduction shift comparison, whose components are identities. Restriction of
scalars leaves the section maps unchanged. The first formula has no sign;
the second retains (-1)^(p * r). Transport along the equality of total-degree
indices yields the stated heterogeneous equalities. -/
theorem podTensorFiniteSignedShiftGenerators (W : Scheme.{u}) :
    PodTensorFiniteShiftGenerators l E W := by
  constructor
  · intro P Q n p q r U x y
    exact finiteShiftLeft_generators l E W n P Q p q r U x y
  · intro P Q n p q r U x y
    exact finiteShiftRight_generators l E W n P Q p q r U x y

end WeilConjectures
