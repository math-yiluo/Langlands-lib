/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! Abstract rational scalar associator compatibility with normalized shifts.

Source: the tensor-generator and localization step of the intrinsic associator-shift
argument (blueprint: lem-pur-intrinsic-associator-shift-square).
The abstract coefficient-field statement isolates the only component calculation
that is expensive when specialized to finite `Shrink` models; the specialization in
the owning module only transports this statement across the coefficient-inclusion
equality. The generic localization square below is the one proved privately in
`IntrinsicAssociatorShiftSquare`, which cannot be imported here (it imports the
general-stage specialization, which imports the owning module).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace WeilConjectures

attribute [local irreducible] sfIntegralScalarComp
  sfRationalTriangulationDatum sfRationalScalarExtension

private theorem commShiftCore_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (n : ℤ) (h : NatTrans.CommShiftCore τ n) :
    NatTrans.CommShiftCore τ (-n) := by
  constructor
  ext X
  apply (shiftFunctor D n).map_injective
  have hz : NatTrans.CommShiftCore τ (-n + n) := by
    simpa only [neg_add_cancel] using NatTrans.CommShiftCore.zero (τ := τ) ℤ
  have hs := hz.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Category.assoc] at hs
  rw [← NatTrans.naturality_assoc] at hs
  have hD := (shiftFunctorAdd D (-n) n).inv.naturality (τ.app X)
  dsimp only [Functor.comp_map] at hD
  rw [← hD] at hs
  apply (cancel_epi (F.map ((shiftFunctorAdd C (-n) n).hom.app X) ≫
    (F.commShiftIso n).hom.app (X⟦-n⟧))).mp
  apply (cancel_mono ((shiftFunctorAdd D (-n) n).inv.app (G.obj X))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, h.shift_app_comm_assoc τ] using hs

private theorem commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (h : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn := commShiftCore_neg τ 1 h
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero (τ := τ) ℤ
  | @succ n ih => exact ih.add h
  | @pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem map_app_heq {C D A : Type*}
    [Category C] [Category D] [Category A]
    (Q : D ⥤ A) {F G : C ⥤ D} (τ : F ⟶ G)
    {X Y : C} (h : X = Y) : HEq (Q.map (τ.app X)) (Q.map (τ.app Y)) := by
  cases h
  rfl

section LocalizationSquare

variable {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
  {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Preadditive C₀] [Preadditive C₁] [Preadditive C₂]
  [Linear R₀ C₀] [Linear R₁ C₁] [Linear R₂ C₂]
  [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [(shiftFunctor C₀ (1 : ℤ)).Additive] [(shiftFunctor C₁ (1 : ℤ)).Additive]
  [(shiftFunctor C₂ (1 : ℤ)).Additive]
  [(shiftFunctor C₀ (1 : ℤ)).Linear R₀] [(shiftFunctor C₁ (1 : ℤ)).Linear R₁]
  [(shiftFunctor C₂ (1 : ℤ)).Linear R₂]
  (p₀ : R₀) (p₁ : R₁) (p₂ : R₂)

local notation "D₀" => ScalarLocalization R₀ C₀ p₀
local notation "D₁" => ScalarLocalization R₁ C₁ p₁
local notation "D₂" => ScalarLocalization R₂ C₂ p₂
local notation "Q₀" => ScalarLocalization.localization R₀ C₀ p₀
local notation "Q₁" => ScalarLocalization.localization R₁ C₁ p₁
local notation "Q₂" => ScalarLocalization.localization R₂ C₂ p₂

variable [s₀ : HasShift (ScalarLocalization R₀ C₀ p₀) ℤ]
  [s₁ : HasShift (ScalarLocalization R₁ C₁ p₁) ℤ]
  [s₂ : HasShift (ScalarLocalization R₂ C₂ p₂) ℤ]

private theorem localized_comp_core
    (IE : C₀ ⥤ C₁) (IL : C₁ ⥤ C₂) (IM : C₀ ⥤ C₂)
    [IE.CommShift ℤ] [IL.CommShift ℤ] [IM.CommShift ℤ]
    (RE : D₀ ⥤ D₁) (RL : D₁ ⥤ D₂) (RM : D₀ ⥤ D₂)
    [cRE : RE.CommShift ℤ] [cRL : RL.CommShift ℤ] [cRM : RM.CommShift ℤ]
    (α : IE ⋙ IL ≅ IM) [NatTrans.CommShift α.hom ℤ] (β : RE ⋙ RL ≅ RM)
    (hsE : shiftFunctor D₀ (1 : ℤ) = ScalarLocalization.map R₀ C₀ p₀
      (shiftFunctor C₀ (1 : ℤ)))
    (hsL : shiftFunctor D₁ (1 : ℤ) = ScalarLocalization.map R₁ C₁ p₁
      (shiftFunctor C₁ (1 : ℤ)))
    (hsM : shiftFunctor D₂ (1 : ℤ) = ScalarLocalization.map R₂ C₂ p₂
      (shiftFunctor C₂ (1 : ℤ)))
    (hRE : ∀ X, RE.obj X = (Q₁).obj (IE.obj X.obj))
    (hRL : ∀ X, RL.obj X = (Q₂).obj (IL.obj X.obj))
    (hRM : ∀ X, RM.obj X = (Q₂).obj (IM.obj X.obj))
    (hFs : ∀ X, HEq ((RE.commShiftIso (1 : ℤ)).hom.app X)
      ((Q₁).map ((IE.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hGs : ∀ X, HEq ((RL.commShiftIso (1 : ℤ)).hom.app X)
      ((Q₂).map ((IL.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hHs : ∀ X, HEq ((RM.commShiftIso (1 : ℤ)).hom.app X)
      ((Q₂).map ((IM.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hmapR : ∀ (X Y : C₁) (f : X ⟶ Y),
      HEq (RL.map (show (Q₁).obj X ⟶ (Q₁).obj Y from
        (1 : Localization.Away p₁) ⊗ₜ[R₁] f))
        ((1 : Localization.Away p₂) ⊗ₜ[R₂] IL.map f :
          (Q₂).obj (IL.obj X) ⟶ (Q₂).obj (IL.obj Y)))
    (hAs : ∀ X, HEq (β.hom.app X) ((Q₂).map (α.hom.app X.obj))) :
    NatTrans.CommShiftCore β.hom (1 : ℤ) := by
  constructor
  apply NatTrans.ext
  funext K
  let QE := Q₀
  let QL := Q₁
  let QM := Q₂
  have hc (X : D₀) : X⟦(1 : ℤ)⟧ = QE.obj (X.obj⟦(1 : ℤ)⟧) :=
    Functor.congr_obj hsE X
  have hd (X : D₁) : X⟦(1 : ℤ)⟧ = QL.obj (X.obj⟦(1 : ℤ)⟧) :=
    Functor.congr_obj hsL X
  have he (X : D₂) : X⟦(1 : ℤ)⟧ = QM.obj (X.obj⟦(1 : ℤ)⟧) :=
    Functor.congr_obj hsM X
  have hobj : (RE.obj K).obj = IE.obj K.obj :=
    congrArg ScalarLocalization.obj (hRE K)
  have hcomp (X : D₀) :
      (RE ⋙ RL).obj X = QM.obj ((IE ⋙ IL).obj X.obj) := by
    dsimp only [Functor.comp_obj]
    rw [hRL, hRE]
    rfl
  have hF := hFs K
  have hG := (hGs (RE.obj K)).trans
    (map_app_heq QM (IL.commShiftIso (1 : ℤ)).hom hobj)
  have hH := hHs K
  have hA := hAs K
  have hm : HEq ((shiftFunctor D₂ (1 : ℤ)).map (β.hom.app K))
      (QM.map ((shiftFunctor C₂ (1 : ℤ)).map (α.hom.app K.obj))) := by
    refine (map_heq (shiftFunctor D₂ (1 : ℤ)) (hcomp K) (hRM K) hA).trans ?_
    have hh := Functor.hcongr_hom hsM (QM.map (α.hom.app K.obj))
    refine hh.trans (heq_of_eq ?_)
    change ScalarLocalization.mapHom _ _ _ (shiftFunctor C₂ (1 : ℤ)) _ _
      (1 ⊗ₜ α.hom.app K.obj) = _
    simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
    rfl
  have hn : HEq (β.hom.app (K⟦(1 : ℤ)⟧))
      (QM.map (α.hom.app (K.obj⟦(1 : ℤ)⟧))) := by
    exact (hAs (K⟦(1 : ℤ)⟧)).trans
      (map_app_heq QM α.hom (congrArg ScalarLocalization.obj (hc K)))
  have hmap : HEq (RL.map ((RE.commShiftIso (1 : ℤ)).hom.app K))
      (QM.map (IL.map ((IE.commShiftIso (1 : ℤ)).hom.app K.obj))) := by
    have hs : RE.obj (K⟦(1 : ℤ)⟧) = QL.obj (IE.obj (K.obj⟦(1 : ℤ)⟧)) := by
      rw [hRE, hc]
      rfl
    have ht : (RE.obj K)⟦(1 : ℤ)⟧ = QL.obj ((IE.obj K.obj)⟦(1 : ℤ)⟧) := by
      rw [hd, hobj]
    refine (map_heq RL hs ht hF).trans ?_
    dsimp only [QL, QM, ScalarLocalization.localization]
    exact hmapR _ _ ((IE.commShiftIso (1 : ℤ)).hom.app K.obj)
  have hs : (RE ⋙ RL).obj (K⟦(1 : ℤ)⟧) =
      QM.obj ((IE ⋙ IL).obj (K.obj⟦(1 : ℤ)⟧)) := by
    rw [hcomp, hc]
    rfl
  have hi : RL.obj ((RE.obj K)⟦(1 : ℤ)⟧) =
      QM.obj (IL.obj ((IE.obj K.obj)⟦(1 : ℤ)⟧)) := by
    rw [hRL, hd, hobj]
    rfl
  have ht : ((RE ⋙ RL).obj K)⟦(1 : ℤ)⟧ =
      QM.obj (((IE ⋙ IL).obj K.obj)⟦(1 : ℤ)⟧) := by
    rw [he, hcomp]
    rfl
  have hu : (RM.obj K)⟦(1 : ℤ)⟧ = QM.obj ((IM.obj K.obj)⟦(1 : ℤ)⟧) := by
    rw [he, hRM]
    rfl
  have hv : RM.obj (K⟦(1 : ℤ)⟧) = QM.obj (IM.obj (K.obj⟦(1 : ℤ)⟧)) := by
    rw [hRM, hc]
    rfl
  have hleft₁ := heq_comp hs hi ht hmap hG
  have hleft := heq_comp hs ht hu hleft₁ hm
  have hright := heq_comp hs hv hu hn hH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  apply eq_of_heq
  rw [Category.assoc] at hleft
  refine hleft.trans (HEq.trans ?_ hright.symm)
  apply heq_of_eq
  change (QM.map _ ≫ QM.map _) ≫ QM.map _ = QM.map _ ≫ QM.map _
  rw [← QM.map_comp, ← QM.map_comp, ← QM.map_comp]
  exact congrArg QM.map (by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α.hom (1 : ℤ) K.obj)

private theorem localized_comp_core_with_Q
    (A₀ : C₀ ⥤ D₀) (A₁ : C₁ ⥤ D₁) (A₂ : C₂ ⥤ D₂)
    (e₀ : A₀ = Q₀) (e₁ : A₁ = Q₁) (e₂ : A₂ = Q₂)
    (IE : C₀ ⥤ C₁) (IL : C₁ ⥤ C₂) (IM : C₀ ⥤ C₂)
    [IE.CommShift ℤ] [IL.CommShift ℤ] [IM.CommShift ℤ]
    (RE : D₀ ⥤ D₁) (RL : D₁ ⥤ D₂) (RM : D₀ ⥤ D₂)
    [cRE : RE.CommShift ℤ] [cRL : RL.CommShift ℤ] [cRM : RM.CommShift ℤ]
    (α : IE ⋙ IL ≅ IM) [NatTrans.CommShift α.hom ℤ] (β : RE ⋙ RL ≅ RM)
    (hsE : shiftFunctor D₀ (1 : ℤ) = ScalarLocalization.map R₀ C₀ p₀
      (shiftFunctor C₀ (1 : ℤ)))
    (hsL : shiftFunctor D₁ (1 : ℤ) = ScalarLocalization.map R₁ C₁ p₁
      (shiftFunctor C₁ (1 : ℤ)))
    (hsM : shiftFunctor D₂ (1 : ℤ) = ScalarLocalization.map R₂ C₂ p₂
      (shiftFunctor C₂ (1 : ℤ)))
    (hRE : ∀ X, RE.obj X = A₁.obj (IE.obj X.obj))
    (hRL : ∀ X, RL.obj X = A₂.obj (IL.obj X.obj))
    (hRM : ∀ X, RM.obj X = A₂.obj (IM.obj X.obj))
    (hFs : ∀ X, HEq ((RE.commShiftIso (1 : ℤ)).hom.app X)
      (A₁.map ((IE.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hGs : ∀ X, HEq ((RL.commShiftIso (1 : ℤ)).hom.app X)
      (A₂.map ((IL.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hHs : ∀ X, HEq ((RM.commShiftIso (1 : ℤ)).hom.app X)
      (A₂.map ((IM.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hmapR : ∀ (X Y : C₁) (f : X ⟶ Y),
      HEq (RL.map (show (Q₁).obj X ⟶ (Q₁).obj Y from
        (1 : Localization.Away p₁) ⊗ₜ[R₁] f))
        ((1 : Localization.Away p₂) ⊗ₜ[R₂] IL.map f :
          (Q₂).obj (IL.obj X) ⟶ (Q₂).obj (IL.obj Y)))
    (hAs : ∀ X : C₀, HEq (β.hom.app (A₀.obj X)) (A₂.map (α.hom.app X))) :
    NatTrans.CommShiftCore β.hom (1 : ℤ) := by
  subst A₀
  subst A₁
  subst A₂
  apply localized_comp_core p₀ p₁ p₂ IE IL IM RE RL RM α β
  · exact hsE
  · exact hsL
  · exact hsM
  · exact hRE
  · exact hRL
  · exact hRM
  · exact hFs
  · exact hGs
  · exact hHs
  · exact hmapR
  · intro X
    simpa only [ScalarLocalization.localization] using hAs X.obj

end LocalizationSquare

private theorem rational_map_one_tmul_general
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (K K' : sfIntegralConstructibleCategory l E Y) (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E Y p hl L i).map
      (show (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
          (sfIntegralConstructibleCategory l E Y)
          (Padic.coefficientExtensionUniformizer l E)).obj K ⟶
        (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
          (sfIntegralConstructibleCategory l E Y)
          (Padic.coefficientExtensionUniformizer l E)).obj K' from
        (1 : Localization.Away (Padic.coefficientExtensionUniformizer l E))
          ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
        ⊗ₜ[Padic.coefficientExtensionIntegers l L]
        (sfConstructibleIntegralScalarExtension p l hl E L i Y).map f :
        (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l L)
          (sfIntegralConstructibleCategory l L Y)
          (Padic.coefficientExtensionUniformizer l L)).obj
          ((sfConstructibleIntegralScalarExtension p l hl E L i Y).obj K) ⟶
        (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l L)
          (sfIntegralConstructibleCategory l L Y)
          (Padic.coefficientExtensionUniformizer l L)).obj
          ((sfConstructibleIntegralScalarExtension p l hl E L i Y).obj K')) := by
  have h := sfRationalScalarExtension_map_tmul l E Y p hl L i K K' f 1
  simp only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
    map_one] at h
  convert h using 1; rfl

/-- The abstract rational scalar associator commutes with normalized integer shifts.
Source: tensor-generator localization step of the associator shift square
(blueprint: lem-pur-intrinsic-rational-associator-shift-compat).
Proof: use the degree-one localization square on tensor generators. The normalized
integral compositor is compatible with shifts by ordinary derived tensor functoriality
and the fully faithful intrinsic inclusion. Every rational object is an integral
localization image, and the rational transition comparison is the localized integral
comparison. The formula for the map of `1 ⊗ f` identifies the rational compositor
component with the localized integral component. Localization therefore proves the
CommShiftCore equation in degree one; the zero, addition and negative-degree
coherence equations extend it to all integers. -/
theorem rational_corrected_comp_commShift
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : E →ₐ[Padic l] M)
    (h : j.comp i = k) (Y : AlgebraicGeometry.Scheme.{u})
    [sE : HasShift (sfRationalConstructibleCategory l E Y) ℤ]
    [sL : HasShift (sfRationalConstructibleCategory l L Y) ℤ]
    [sM : HasShift (sfRationalConstructibleCategory l M Y) ℤ]
    [tE : (sfConstructibleIntegralScalarExtension p l hl E L i Y).CommShift ℤ]
    [tL : (sfConstructibleIntegralScalarExtension p l hl L M j Y).CommShift ℤ]
    [tM : (sfConstructibleIntegralScalarExtension p l hl E M k Y).CommShift ℤ]
    [cE : (sfRationalScalarExtension l E Y p hl L i).CommShift ℤ]
    [cL : (sfRationalScalarExtension l L Y p hl M j).CommShift ℤ]
    [cM : (sfRationalScalarExtension l E Y p hl M k).CommShift ℤ]
    (hα : NatTrans.CommShift
      ((sfIntegralScalarComp l E L i Y p hl M j ≪≫ eqToIso (congrArg
        (fun f ↦ sfConstructibleIntegralScalarExtension p l hl E M f Y) h)).hom) ℤ)
    (hsE : shiftFunctor (sfRationalConstructibleCategory l E Y) (1 : ℤ) =
      ScalarLocalization.map (Padic.coefficientExtensionIntegers l E)
        (sfIntegralConstructibleCategory l E Y) (Padic.coefficientExtensionUniformizer l E)
        (shiftFunctor (sfIntegralConstructibleCategory l E Y) (1 : ℤ)))
    (hsL : shiftFunctor (sfRationalConstructibleCategory l L Y) (1 : ℤ) =
      ScalarLocalization.map (Padic.coefficientExtensionIntegers l L)
        (sfIntegralConstructibleCategory l L Y) (Padic.coefficientExtensionUniformizer l L)
        (shiftFunctor (sfIntegralConstructibleCategory l L Y) (1 : ℤ)))
    (hsM : shiftFunctor (sfRationalConstructibleCategory l M Y) (1 : ℤ) =
      ScalarLocalization.map (Padic.coefficientExtensionIntegers l M)
        (sfIntegralConstructibleCategory l M Y) (Padic.coefficientExtensionUniformizer l M)
        (shiftFunctor (sfIntegralConstructibleCategory l M Y) (1 : ℤ)))
    (hcE : ∀ X : sfRationalConstructibleCategory l E Y,
      HEq (((sfRationalScalarExtension l E Y p hl L i).commShiftIso (1 : ℤ)).hom.app X)
        ((sfRationalConstructibleLocalization l L Y).map
          (((sfConstructibleIntegralScalarExtension p l hl E L i Y).commShiftIso
            (1 : ℤ)).hom.app X.obj)))
    (hcL : ∀ X : sfRationalConstructibleCategory l L Y,
      HEq (((sfRationalScalarExtension l L Y p hl M j).commShiftIso (1 : ℤ)).hom.app X)
        ((sfRationalConstructibleLocalization l M Y).map
          (((sfConstructibleIntegralScalarExtension p l hl L M j Y).commShiftIso
            (1 : ℤ)).hom.app X.obj)))
    (hcM : ∀ X : sfRationalConstructibleCategory l E Y,
      HEq (((sfRationalScalarExtension l E Y p hl M k).commShiftIso (1 : ℤ)).hom.app X)
        ((sfRationalConstructibleLocalization l M Y).map
          (((sfConstructibleIntegralScalarExtension p l hl E M k Y).commShiftIso
            (1 : ℤ)).hom.app X.obj))) :
    NatTrans.CommShift
      ((sfRationalScalarComp l E L i Y p hl M j ≪≫ eqToIso
        (congrArg (sfRationalScalarExtension l E Y p hl M) h)).hom) ℤ := by
  subst h
  have hα' : NatTrans.CommShift (sfIntegralScalarComp l E L i Y p hl M j).hom ℤ := by
    simpa only [eqToIso_refl, Iso.trans_refl] using hα
  simp only [eqToIso_refl, Iso.trans_refl]
  apply commShift_of_one
  apply localized_comp_core_with_Q
    (s₀ := sE) (s₁ := sL) (s₂ := sM) (cRE := cE) (cRL := cL) (cRM := cM)
    (Padic.coefficientExtensionUniformizer l E)
    (Padic.coefficientExtensionUniformizer l L)
    (Padic.coefficientExtensionUniformizer l M)
    (sfRationalConstructibleLocalization l E Y)
    (sfRationalConstructibleLocalization l L Y)
    (sfRationalConstructibleLocalization l M Y) rfl rfl rfl
    (sfConstructibleIntegralScalarExtension p l hl E L i Y)
    (sfConstructibleIntegralScalarExtension p l hl L M j Y)
    (sfConstructibleIntegralScalarExtension p l hl E M (j.comp i) Y)
    (sfRationalScalarExtension l E Y p hl L i)
    (sfRationalScalarExtension l L Y p hl M j)
    (sfRationalScalarExtension l E Y p hl M (j.comp i))
    (sfIntegralScalarComp l E L i Y p hl M j) (sfRationalScalarComp l E L i Y p hl M j)
  · exact hsE
  · exact hsL
  · exact hsM
  · exact sfRationalScalarExtension_obj l E Y p hl L i
  · exact sfRationalScalarExtension_obj l L Y p hl M j
  · exact sfRationalScalarExtension_obj l E Y p hl M (j.comp i)
  · exact hcE
  · exact hcL
  · exact hcM
  · intro X Z f
    exact rational_map_one_tmul_general p l hl L M j Y X Z f
  · intro X
    exact (sfRationalScalarComp_existsUnique l E L i Y p hl M j).exists.choose_spec
      ((sfRationalConstructibleLocalization l E Y).obj X)

end WeilConjectures
