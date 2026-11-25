/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExactIntrinsic
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.CategoryTheory.IntegerShiftFromOne

/-! Normalized integer shifts on rational scalar extension.
This extracts the proved scalar-localization argument from the pair-category module
so both files compile separately within the time limit
(blueprint: lem-pur-intrinsic-rational-scalar-shift-normalization).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace WeilConjectures
attribute [local irreducible] sfRationalTriangulationDatum sfRationalScalarExtension

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have c_hom (K) : (c K).hom =
      eqToHom (hF K) ≫ (ScalarLocalization.localization S D v).map (e.hom.app K.obj) ≫
        eqToHom (hG K).symm := rfl
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    rw [c_hom]
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.inductionOn with
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      apply eq_of_heq
      exact (heq_comp (hF ⟨K⟩) (hF ⟨K'⟩) (hG ⟨K'⟩)
        (mF K K' f a) (hc ⟨K'⟩)).trans
          ((heq_of_eq he').trans
            (heq_comp (hF ⟨K⟩) (hG ⟨K⟩) (hG ⟨K'⟩)
              (hc ⟨K⟩) (mG K K' f a)).symm)
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

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

/-- Coherence extends the degree-one square to every integral shift. -/
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

private theorem integer_commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

private theorem commShift_one_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (s t : F.CommShift ℤ)
    (h : Functor.commShiftIso F (self := s) (1 : ℤ) =
      Functor.commShiftIso F (self := t) (1 : ℤ)) : s = t := by
  have hcore : @NatTrans.CommShiftCore C D _ _ F F (𝟙 F) ℤ _ _ _ s t 1 := by
    refine @NatTrans.CommShiftCore.mk C D _ _ F F (𝟙 F) ℤ _ _ _ s t 1 ?_
    apply NatTrans.ext
    funext X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.id_app, Functor.comp_obj]
    rw [(shiftFunctor D (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
    exact congrArg (fun a ↦ a.hom.app X) h
  have hc := @commShift_of_one C D _ _ _ _ F F s t (𝟙 F) hcore
  apply integer_commShift_ext
  intro n
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have hn := congrArg (fun a ↦ a.app X) (hc.shift_comm n)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app, Functor.comp_obj] at hn
  rw [(shiftFunctor D n).map_id, Category.comp_id, Category.id_comp] at hn
  exact hn

private theorem scalarShift_exists
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasShift C ℤ]
    {D : Type*} [Category D] [Preadditive D] [Linear S D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(shiftFunctor C (1 : ℤ)).Linear R]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(shiftFunctor D (1 : ℤ)).Linear S]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    [HasShift (ScalarLocalization R C t) ℤ] [HasShift (ScalarLocalization S D v) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D v) n).Additive]
    (hC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
      ScalarLocalization.map R C t (shiftFunctor C (1 : ℤ)))
    (hD : shiftFunctor (ScalarLocalization S D v) (1 : ℤ) =
      ScalarLocalization.map S D v (shiftFunctor D (1 : ℤ)))
    (T : C ⥤ D) [T.CommShift ℤ]
    (F : ScalarLocalization R C t ⥤ ScalarLocalization S D v) [F.Additive]
    (hF : ∀ K, F.obj K = ⟨T.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] T.map f : ScalarLocalization.mk (R := S) (p := v) (T.obj K) ⟶
          ⟨T.obj K'⟩)) :
    ∃ s : F.CommShift ℤ, ∀ K,
      HEq ((Functor.commShiftIso F (self := s) (1 : ℤ)).hom.app K)
        ((ScalarLocalization.localization S D v).map ((T.commShiftIso (1 : ℤ)).hom.app K.obj)) := by
  let A := shiftFunctor (ScalarLocalization R C t) (1 : ℤ) ⋙ F
  let B := F ⋙ shiftFunctor (ScalarLocalization S D v) (1 : ℤ)
  have hA (K) : A.obj K = ⟨T.obj ((shiftFunctor C (1 : ℤ)).obj K.obj)⟩ := by
    dsimp only [A, Functor.comp_obj]
    rw [hC]
    exact hF _
  have hB (K) : B.obj K = ⟨(shiftFunctor D (1 : ℤ)).obj (T.obj K.obj)⟩ := by
    dsimp only [B, Functor.comp_obj]
    rw [hD, hF]
    rfl
  have mA (K K' : C) (f : K ⟶ K') (a : Localization.Away t) :
      HEq (A.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] T.map ((shiftFunctor C (1 : ℤ)).map f) :
          ScalarLocalization.mk (R := S) (p := v)
            (T.obj ((shiftFunctor C (1 : ℤ)).obj K)) ⟶
              ⟨T.obj ((shiftFunctor C (1 : ℤ)).obj K')⟩) := by
    dsimp only [A, Functor.comp_map]
    rw [hC]
    simpa only [ScalarLocalization.map, ScalarLocalization.mapHom,
      LinearMap.baseChange_tmul, Functor.comp_obj,
      Functor.coe_mapLinearMap] using mF _ _ ((shiftFunctor C (1 : ℤ)).map f) a
  have mB (K K' : C) (f : K ⟶ K') (a : Localization.Away t) :
      HEq (B.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] (shiftFunctor D (1 : ℤ)).map (T.map f) :
          ScalarLocalization.mk (R := S) (p := v)
            ((shiftFunctor D (1 : ℤ)).obj (T.obj K)) ⟶
              ⟨(shiftFunctor D (1 : ℤ)).obj (T.obj K')⟩) := by
    have hm := map_heq (shiftFunctor (ScalarLocalization S D v) (1 : ℤ))
      (hF ⟨K⟩) (hF ⟨K'⟩) (mF K K' f a)
    rw [hD] at hm
    dsimp only [B, Functor.comp_map]
    rw [hD]
    simpa only [B, Functor.comp_map, ScalarLocalization.map, ScalarLocalization.mapHom,
      LinearMap.baseChange_tmul, Functor.comp_obj,
      Functor.coe_mapLinearMap] using hm
  obtain ⟨a, ha, _⟩ := localizedIso t v ψ
    (shiftFunctor C (1 : ℤ) ⋙ T) (T ⋙ shiftFunctor D (1 : ℤ))
    (T.commShiftIso (1 : ℤ)) A B hA hB mA mB
  obtain ⟨s, hs⟩ := Functor.exists_commShift_of_one F a
  refine ⟨s, ?_⟩
  intro K
  rw [hs]
  exact ha K

private theorem scalarShift_existsUnique
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasShift C ℤ]
    {D : Type*} [Category D] [Preadditive D] [Linear S D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(shiftFunctor C (1 : ℤ)).Linear R]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(shiftFunctor D (1 : ℤ)).Linear S]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    [HasShift (ScalarLocalization R C t) ℤ] [HasShift (ScalarLocalization S D v) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D v) n).Additive]
    (hC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
      ScalarLocalization.map R C t (shiftFunctor C (1 : ℤ)))
    (hD : shiftFunctor (ScalarLocalization S D v) (1 : ℤ) =
      ScalarLocalization.map S D v (shiftFunctor D (1 : ℤ)))
    (T : C ⥤ D) [T.CommShift ℤ]
    (F : ScalarLocalization R C t ⥤ ScalarLocalization S D v) [F.Additive]
    (hF : ∀ K, F.obj K = ⟨T.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] T.map f : ScalarLocalization.mk (R := S) (p := v) (T.obj K) ⟶
          ⟨T.obj K'⟩)) :
    ∃! s : F.CommShift ℤ, ∀ K,
      HEq ((Functor.commShiftIso F (self := s) (1 : ℤ)).hom.app K)
        ((ScalarLocalization.localization S D v).map ((T.commShiftIso (1 : ℤ)).hom.app K.obj)) := by
  obtain ⟨s, hs⟩ := scalarShift_exists t v ψ hC hD T F hF mF
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  apply commShift_one_ext
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hs' K).trans (hs K).symm)

/-- Rational scalar extension has a unique coherent integer-shift comparison with the
prescribed localized integral component at degree one.
Source: intrinsic scalar localization normalization in the common-stage shift argument
(blueprint: lem-pur-intrinsic-rational-scalar-shift-normalization).
Proof: construct the degree-one comparison by tensoring the integral comparison and
its inverse with one. Tensor induction proves naturality and the inverse equations.
Transport along the stated degree-one shift-functor equalities and extend to every
integer using the integer-shift construction. The zero and addition equations force
all other comparisons from degree one, which also proves uniqueness. -/
theorem sfRationalScalarCommShift_existsUnique
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    [(sfConstructibleIntegralScalarExtension p l hl E L i Y).CommShift ℤ] :
    ∃! c : (sfRationalScalarExtension l E Y p hl L i).CommShift ℤ,
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq ((Functor.commShiftIso (sfRationalScalarExtension l E Y p hl L i)
            (self := c) (1 : ℤ)).hom.app K)
          ((sfRationalConstructibleLocalization l L Y).map
            (((sfConstructibleIntegralScalarExtension p l hl E L i Y).commShiftIso
              (1 : ℤ)).hom.app K.obj)) := by
  let : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l E Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l L Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor (sfRationalConstructibleCategory l E Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l E Y n
  let : ∀ n : ℤ, (shiftFunctor (sfRationalConstructibleCategory l L Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l L Y n
  have hsE := (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.1
  have hsL := (sfRationalTriangulationDatum l L Y).choose_spec.choose_spec.1
  exact scalarShift_existsUnique
    (R := Padic.coefficientExtensionIntegers l E)
    (S := Padic.coefficientExtensionIntegers l L)
    (C := sfIntegralConstructibleCategory l E Y)
    (D := sfIntegralConstructibleCategory l L Y)
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
    (fun a ↦ (sfRationalCoefficientEquiv l L).symm (i (sfRationalCoefficientEquiv l E a)))
    hsE hsL (sfConstructibleIntegralScalarExtension p l hl E L i Y)
    (sfRationalScalarExtension l E Y p hl L i)
    (sfRationalScalarExtension_obj l E Y p hl L i)
    (sfRationalScalarExtension_map_tmul l E Y p hl L i)

end WeilConjectures
