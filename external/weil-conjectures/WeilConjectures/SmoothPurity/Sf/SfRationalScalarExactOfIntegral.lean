/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

/-! # Exactness of normalized rational scalar extension from an integral model

This is the rational descent step of the intrinsic transition exactness argument
(blueprint: lem-route-rational-transition-exact-of-integral).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Pretriangulated

namespace WeilConjectures

private theorem localized_comparison_core
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (Q : C ⥤ C') (Q' : D ⥤ D') (T : C ⥤ D) (F : C' ⥤ D')
    [Q.CommShift ℤ] [Q'.CommShift ℤ] [T.CommShift ℤ] [F.CommShift ℤ]
    (hF : ∀ X, F.obj (Q.obj X) = Q'.obj (T.obj X))
    (c : Q ⋙ F ≅ T ⋙ Q') (hc : ∀ X, c.hom.app X = eqToHom (hF X))
    (hQ : ∀ X, Q.obj (X⟦(1 : ℤ)⟧) = (Q.obj X)⟦(1 : ℤ)⟧)
    (hQ' : ∀ X, Q'.obj (X⟦(1 : ℤ)⟧) = (Q'.obj X)⟦(1 : ℤ)⟧)
    (nQ : ∀ X, HEq ((Q.commShiftIso (1 : ℤ)).hom.app X)
      (𝟙 (Q.obj (X⟦(1 : ℤ)⟧))))
    (nQ' : ∀ X, HEq ((Q'.commShiftIso (1 : ℤ)).hom.app X)
      (𝟙 (Q'.obj (X⟦(1 : ℤ)⟧))))
    (nF : ∀ X, HEq ((F.commShiftIso (1 : ℤ)).hom.app (Q.obj X))
      (Q'.map ((T.commShiftIso (1 : ℤ)).hom.app X))) :
    NatTrans.CommShiftCore c.hom (1 : ℤ) := by
  constructor
  ext X
  have q : (Q.commShiftIso (1 : ℤ)).hom.app X = eqToHom (hQ X) :=
    eq_of_heq ((nQ X).trans (eqToHom_heq_id_dom _ _ (hQ X)).symm)
  have q' : (Q'.commShiftIso (1 : ℤ)).hom.app (T.obj X) = eqToHom (hQ' (T.obj X)) :=
    eq_of_heq ((nQ' _).trans (eqToHom_heq_id_dom _ _ (hQ' (T.obj X))).symm)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, hc, q, q', eqToHom_map]
  apply eq_of_heq
  exact ((comp_eqToHom_heq _ _).trans (eqToHom_comp_heq _ _)).trans
    ((nF X).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

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

attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum
  sfRationalScalarExtension ScalarLocalization.composition

/-- An integral-exact scalar transition induces an exact rational transition for its
specified integral-image-normalized shift comparison.
Source: blueprint's intrinsic scalar exactness argument, integral-image triangle steps
(blueprint: lem-route-rational-transition-exact-of-integral).
Proof: compare rational extension after localization with integral extension followed
by localization. The pure-tensor formula gives the comparison. The localization
comparisons at one are identity transports, so the prescribed degree-one equation
makes this comparison commute with shift at one. Coherent integer shifts extend the
square to all integers. An integral distinguished triangle therefore has a
distinguished rational transition image. Every rational distinguished triangle is
isomorphic to such an integral image; apply the transition to that isomorphism and
use invariance of distinguished triangles under isomorphism. -/
theorem sfRationalScalarExactOfIntegral
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    [t : (sfConstructibleIntegralScalarExtension p l hl E L i Y).CommShift ℤ]
    [ht : (sfConstructibleIntegralScalarExtension p l hl E L i Y).IsTriangulated]
    [s : (sfRationalScalarExtension l E Y p hl L i).CommShift ℤ]
    (hs : ∀ K : sfRationalConstructibleCategory l E Y,
      HEq (((sfRationalScalarExtension l E Y p hl L i).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l L Y).map
          (((sfConstructibleIntegralScalarExtension p l hl E L i Y).commShiftIso
            (1 : ℤ)).hom.app K.obj))) :
    (sfRationalScalarExtension l E Y p hl L i).IsTriangulated := by
  let T := sfConstructibleIntegralScalarExtension p l hl E L i Y
  let Q := sfRationalConstructibleLocalization l E Y
  let Q' := sfRationalConstructibleLocalization l L Y
  let : Q.CommShift ℤ := sfRationalLocalizationCommShift l E Y
  let : Q'.CommShift ℤ := sfRationalLocalizationCommShift l L Y
  have : Q'.IsTriangulated := sfRationalLocalizationTriangulated l L Y
  let F := sfRationalScalarExtension l E Y p hl
    L i
  have hobj := sfRationalScalarExtension_obj l E Y p hl
    L i
  have hmap := sfRationalScalarExtension_map_tmul l E Y p hl
    L i
  let c : Q ⋙ F ≅ T ⋙ Q' := NatIso.ofComponents
    (fun X ↦ eqToIso (hobj (Q.obj X))) (by
      intro X X' f
      change F.map (Q.map f) ≫ eqToHom (hobj (Q.obj X')) =
        eqToHom (hobj (Q.obj X)) ≫ Q'.map (T.map f)
      have hm := hmap X X' f 1
      have hm' : HEq (F.map (Q.map f)) (Q'.map (T.map f)) := by
        simp only [map_one] at hm
        dsimp only [F, Q, Q', sfRationalConstructibleLocalization,
          ScalarLocalization.localization, T] at hm ⊢
        with_unfolding_all exact hm
      exact eq_of_heq ((comp_eqToHom_heq _ _).trans
        (hm'.trans (eqToHom_comp_heq _ _).symm)))
  have qobj (X) : Q.obj (X⟦(1 : ℤ)⟧) = (Q.obj X)⟦(1 : ℤ)⟧ := by
    rw [(sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.1]
    rfl
  have qobj' (X) : Q'.obj (X⟦(1 : ℤ)⟧) = (Q'.obj X)⟦(1 : ℤ)⟧ := by
    rw [(sfRationalTriangulationDatum l L Y).choose_spec.choose_spec.1]
    rfl
  have qdataE := ((sfRationalTriangulationDatum l
    E Y).choose_spec.choose_spec.2).choose_spec.choose_spec
  have qdataL := ((sfRationalTriangulationDatum l
    L Y).choose_spec.choose_spec.2).choose_spec.choose_spec
  have : NatTrans.CommShift c.hom ℤ := commShift_of_one c.hom
    (localized_comparison_core Q Q' T F (fun X ↦ hobj (Q.obj X)) c (fun _ ↦ rfl)
      qobj qobj'
      qdataE.1 qdataL.1
      (fun X ↦ hs (Q.obj X)))
  have : (Q ⋙ F).IsTriangulated := (Functor.isTriangulated_iff_of_iso c).2 inferInstance
  constructor
  intro Δ hΔ
  obtain ⟨Δ', hΔ', ⟨eΔ⟩⟩ :=
    (qdataE.2.choose_spec.2.2 Δ).mp hΔ
  exact isomorphic_distinguished _ ((Q ⋙ F).map_distinguished Δ' hΔ') _
    ((F.mapTriangle.mapIso eΔ) ≪≫ (Functor.mapTriangleCompIso Q F).symm.app Δ')

end WeilConjectures
