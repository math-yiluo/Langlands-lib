/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom

/-!
# Dual and Tate Weil data

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite MonoidalClosed

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor.LaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] (F : C ⥤ C)

section Lax

variable [F.LaxMonoidal]

/-- The transpose of the *contragredient* `F [K, 𝟙] ⟶ [F K, F 𝟙] ⟶ [F K, 𝟙] ⟶ [K, 𝟙]` of a
lax monoidal endofunctor `F`, an isomorphism `φ : F K ≅ K` and a map `u : F 𝟙 ⟶ 𝟙`: it is
`K ⊗ F [K, 𝟙] ⟶ F K ⊗ F [K, 𝟙] ⟶ F (K ⊗ [K, 𝟙]) ⟶ F 𝟙 ⟶ 𝟙`. -/
lemma whiskerLeft_ihomComparison_comp_pre_comp_ev {K : C} (φ : F.obj K ≅ K)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) :
    K ◁ ((ihomComparison F K).app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
        (pre φ.inv).app (𝟙_ C)) ≫ (ihom.ev K).app (𝟙_ C) =
      φ.inv ▷ _ ≫ μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u := by
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whisker_exchange_assoc,
    ihom.ev_naturality, ihomComparison_ev_assoc]
  rfl

/-- The transpose of the contragredient `F [K, M] ⟶ [F K, F M] ⟶ [F K, M] ⟶ [K, M]` of a lax
monoidal endofunctor `F`, an isomorphism `φ : F K ≅ K` and a map `u : F M ⟶ M`: it is
`K ⊗ F [K, M] ⟶ F K ⊗ F [K, M] ⟶ F (K ⊗ [K, M]) ⟶ F M ⟶ M`. -/
@[reassoc]
lemma whiskerLeft_ihomComparison_comp_map_comp_pre_comp_ev {K M : C} (φ : F.obj K ≅ K)
    (u : F.obj M ⟶ M) :
    K ◁ ((ihomComparison F K).app M ≫ (ihom (F.obj K)).map u ≫
        (pre φ.inv).app M) ≫ (ihom.ev K).app M =
      φ.inv ▷ _ ≫ μ F K _ ≫ F.map ((ihom.ev K).app M) ≫ u := by
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whisker_exchange_assoc,
    ihom.ev_naturality, ihomComparison_ev_assoc]
  rfl

end Lax

section Monoidal

variable [F.Monoidal]

/-- The evaluation `K ⊗ [K, 𝟙] ⟶ 𝟙` intertwines `φ ⊗ ψ` and `u`, for the contragredient
`ψ : F [K, 𝟙] ⟶ [F K, F 𝟙] ⟶ [F K, 𝟙] ⟶ [K, 𝟙]` of `φ : F K ≅ K` and `u : F 𝟙 ⟶ 𝟙`. -/
lemma map_ev_comp_eq_δ_comp_ihomComparison_comp_pre {K : C} (φ : F.obj K ≅ K)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) :
    F.map ((ihom.ev K).app (𝟙_ C)) ≫ u =
      (OplaxMonoidal.δ F K _ ≫ φ.hom ▷ _ ≫
        K ◁ ((ihomComparison F K).app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
          (pre φ.inv).app (𝟙_ C))) ≫ (ihom.ev K).app (𝟙_ C) := by
  rw [Category.assoc, Category.assoc, whiskerLeft_ihomComparison_comp_pre_comp_ev,
    hom_inv_whiskerRight_assoc, Monoidal.δ_μ_assoc]

/-- The contragredient `F [K, 𝟙] ⟶ [F K, F 𝟙] ⟶ [F K, 𝟙] ⟶ [K, 𝟙]` of an isomorphism
`φ : F K ≅ K` and an isomorphism `u : F 𝟙 ⟶ 𝟙` is an isomorphism when `K` has a left dual. -/
lemma isIso_ihomComparison_comp_pre {Y K : C} [ExactPairing Y K] (φ : F.obj K ≅ K)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) [IsIso u] :
    IsIso ((ihomComparison F K).app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
      (pre φ.inv).app (𝟙_ C)) := by
  have e : (ihomComparison F K).app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
      (pre φ.inv).app (𝟙_ C) =
        MonoidalClosed.curry (φ.inv ▷ _ ≫ μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u) := by
    rw [eq_comm, curry_eq_iff, uncurry_eq, whiskerLeft_ihomComparison_comp_pre_comp_ev]
  have := isIso_ihomUnitTensorToIhom Y K K
  let := exactPairingOfIsIso K
  let := ExactPairing.map F ((ihom K).obj (𝟙_ C)) K
  have hb : IsPerfectPairing (μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u) := by
    refine ⟨?_⟩
    have h : μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u =
        ε_ (F.obj ((ihom K).obj (𝟙_ C))) (F.obj K) ≫ (LaxMonoidal.ε F ≫ u) := by
      change _ = (μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ OplaxMonoidal.η F) ≫ _
      simp only [Category.assoc, Monoidal.η_ε_assoc]
    rw [h, curry_natural_right]
    infer_instance
  rw [e]
  exact (hb.whiskerRight_comp φ.inv).isIso

/-- For `K = 𝟙` and `φ : F 𝟙 ≅ 𝟙` compatible with the left unitor, the canonical
identification `𝟙 ≅ [𝟙, 𝟙]` intertwines `φ` and its contragredient. -/
lemma map_curry_leftUnitor_comp_ihomComparison_comp_pre (φ : F.obj (𝟙_ C) ≅ 𝟙_ C)
    (hφ : OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C) ≫ φ.hom ▷ F.obj (𝟙_ C) ≫ (λ_ (F.obj (𝟙_ C))).hom =
      F.map (λ_ (𝟙_ C)).hom) :
    F.map (MonoidalClosed.curry (λ_ (𝟙_ C)).hom) ≫ (ihomComparison F (𝟙_ C)).app (𝟙_ C) ≫
        (ihom (F.obj (𝟙_ C))).map φ.hom ≫ (pre φ.inv).app (𝟙_ C) =
      φ.hom ≫ MonoidalClosed.curry (λ_ (𝟙_ C)).hom := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_ihomComparison_comp_pre_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    ← uncurry_eq, uncurry_curry, whisker_exchange_assoc,
    μ_natural_right_assoc, ← F.map_comp_assoc, ← uncurry_eq, uncurry_curry, ← hφ,
    Category.assoc, Category.assoc, Monoidal.μ_δ_assoc, inv_hom_whiskerRight_assoc]
  exact (MonoidalCategory.leftUnitor_naturality φ.hom).symm

/-- **Contragredient data and twisted evaluations.** Let `φ : F K ≅ K`, `χ : F M ⟶ M` and
`τ : F T ⟶ T` be data, `γ : T ≅ M` an isomorphism intertwining `τ` and `χ`, and
`θ : [K, M] ≅ D` an isomorphism under which the evaluation `K ⊗ [K, M] ⟶ M ≅ T` becomes a
pairing `E : K ⊗ D ⟶ T`. If `ψ : F D ⟶ D` is a datum for which `E` intertwines `φ ⊗ ψ` and `τ`,
then `θ` intertwines the contragredient `F [K, M] ⟶ [F K, F M] ⟶ [F K, M] ⟶ [K, M]` of `φ` and
`χ` with `ψ`. -/
lemma map_hom_comp_eq_ihomComparison_comp_map_comp_pre_comp {K M T D : C} (φ : F.obj K ≅ K)
    (χ : F.obj M ⟶ M) (τ : F.obj T ⟶ T) (γ : T ≅ M) (hγ : F.map γ.hom ≫ χ = τ ≫ γ.hom)
    (θ : (ihom K).obj M ≅ D) (E : K ⊗ D ⟶ T)
    (hE : K ◁ θ.hom ≫ E = (ihom.ev K).app M ≫ γ.inv) (ψ : F.obj D ⟶ D)
    (hψ : F.map E ≫ τ = (OplaxMonoidal.δ F K D ≫ φ.hom ▷ F.obj D ≫ K ◁ ψ) ≫ E) :
    F.map θ.hom ≫ ψ = ((ihomComparison F K).app M ≫ (ihom (F.obj K)).map χ ≫
        (pre φ.inv).app M) ≫ θ.hom := by
  have hγ' : F.map γ.inv ≫ τ = χ ≫ γ.inv := by
    rw [← cancel_epi (F.map γ.hom), ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
      Category.id_comp, reassoc_of% hγ, Iso.hom_inv_id, Category.comp_id]
  have hψ' : K ◁ ψ ≫ E = φ.inv ▷ _ ≫ μ F K D ≫ F.map E ≫ τ := by
    rw [hψ, Category.assoc, Category.assoc, Monoidal.μ_δ_assoc, inv_hom_whiskerRight_assoc]
  have hE' {Z : C} (f : Z ⟶ D) :
      K ◁ f ≫ E = MonoidalClosed.uncurry (f ≫ θ.inv) ≫ γ.inv := by
    rw [uncurry_eq, Category.assoc, ← hE, MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc (f := θ.inv), Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hinj {Z : C} (f f' : Z ⟶ D) (h : K ◁ f ≫ E = K ◁ f' ≫ E) : f = f' := by
    rw [hE', hE', cancel_mono] at h
    rw [← cancel_mono θ.inv]
    exact uncurry_injective h
  refine hinj _ _ ?_
  rw [MonoidalCategory.whiskerLeft_comp_assoc (g := ψ), hψ', whisker_exchange_assoc,
    μ_natural_right_assoc, ← F.map_comp_assoc, hE, F.map_comp, Category.assoc, hγ',
    ← whiskerLeft_ihomComparison_comp_map_comp_pre_comp_ev_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc (g := θ.hom), hE]

end Monoidal

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Functor

open MonoidalCategory

/-- A pairing `P : K ⊗ D ⟶ 𝟙` compatible with data `φ`, `ψ`, `u` stays compatible after
twisting by `T` with a datum `τ`: `K ⊗ (D ⊗ T) ≅ (K ⊗ D) ⊗ T ⟶ 𝟙 ⊗ T ≅ T` intertwines
`φ ⊗ (ψ ⊗ τ)` and `τ`, provided `u` is compatible with the left unitor. -/
lemma OplaxMonoidal.map_twistedPairing_comp {C : Type*} [Category* C] [MonoidalCategory C]
    (F : C ⥤ C) [F.OplaxMonoidal] {K D T : C} (φ : F.obj K ⟶ K) (ψ : F.obj D ⟶ D)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) (τ : F.obj T ⟶ T) (P : K ⊗ D ⟶ 𝟙_ C)
    (hP : F.map P ≫ u = (OplaxMonoidal.δ F K D ≫ φ ▷ F.obj D ≫ K ◁ ψ) ≫ P)
    (hu : OplaxMonoidal.δ F (𝟙_ C) T ≫ u ▷ F.obj T ≫ (λ_ (F.obj T)).hom = F.map (λ_ T).hom) :
    F.map ((α_ K D T).inv ≫ P ▷ T ≫ (λ_ T).hom) ≫ τ =
      (OplaxMonoidal.δ F K (D ⊗ T) ≫ φ ▷ F.obj (D ⊗ T) ≫
        K ◁ (OplaxMonoidal.δ F D T ≫ ψ ▷ F.obj T ≫ D ◁ τ)) ≫
        (α_ K D T).inv ≫ P ▷ T ≫ (λ_ T).hom := by
  rw [F.map_comp, F.map_comp, ← hu, ← OplaxMonoidal.δ_natural_left_assoc,
    ← comp_whiskerRight_assoc, hP]
  simp only [Category.assoc, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  rw [← OplaxMonoidal.associativity_inv_assoc]
  congr 1
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality,
    associator_inv_naturality_middle_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Comparison

variable [UpperStarPreservesFlat A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The lax monoidal structure map `μ` of the monoidal functor `Lg^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`) is the inverse of the tensor
comparison `Lg^*(K ⊗ᴸ M) ≅ Lg^* K ⊗ᴸ Lg^* M`. -/
lemma leftDerivedUpperStarMonoidal_μ (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    Functor.LaxMonoidal.μ L((g)^*[A]) K M = (leftDerivedUpperStarTensorIso A g K M).inv := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← cancel_mono (leftDerivedUpperStarTensorIso A g K M).hom, Iso.inv_hom_id]
  exact Functor.Monoidal.μ_δ _ _ _

/-- The oplax monoidal structure map `δ` of the monoidal functor `Lg^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`) is the tensor comparison
`Lg^*(K ⊗ᴸ M) ≅ Lg^* K ⊗ᴸ Lg^* M`. -/
lemma leftDerivedUpperStarMonoidal_δ (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    Functor.OplaxMonoidal.δ L((g)^*[A]) K M = (leftDerivedUpperStarTensorIso A g K M).hom := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← cancel_epi (Functor.LaxMonoidal.μ L((g)^*[A]) K M), Functor.Monoidal.μ_δ,
    leftDerivedUpperStarMonoidal_μ, Iso.inv_hom_id]

/-- The comparison `Lg^* RHom(K, N) ⟶ RHom(Lg^* K, Lg^* N)` is compatible with the
evaluations. -/
lemma derivedTensor_map_leftDerivedUpperStarDerivedHomComparison_comp_counit
    (K N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A Z).obj (L((g)^*[A]).obj K)).map
        (leftDerivedUpperStarDerivedHomComparison A g K N) ≫
      (derivedTensorHomAdjunction A (L((g)^*[A]).obj K)).counit.app (L((g)^*[A]).obj N) =
    (leftDerivedUpperStarTensorIso A g K _).inv ≫
      L((g)^*[A]).map ((derivedTensorHomAdjunction A K).counit.app N) := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← leftDerivedUpperStarMonoidal_μ]
  exact Functor.LaxMonoidal.ihomComparison_ev _ _ _

end Comparison

section Datum

variable [UpperStarPreservesFlat A] {X : Scheme.{u}} (g : X ⟶ X)
  {K : DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- Blueprint `theorem-poincare-duality-frobenius--1`: Dual and Tate Weil data.

The *contragredient datum* `φ_{K^∨} : Lg^* K^∨ ⟶ K^∨` on the coefficient dual
`K^∨ = RHom(K, Λ_X)` of a complex `K` with a Weil datum `φ_K : Lg^* K ≅ K`, the typed composite
```
                      ≅                                 RHom(id, φ_Λ)
  Lg^* RHom(K, Λ_X) ────▶ RHom(Lg^* K, Lg^* Λ_X) ───────────────▶ RHom(Lg^* K, Λ_X)
                                     RHom(φ_K⁻¹, id)
                                   ───────────────▶ RHom(K, Λ_X)
```
of the comparison of `Lg^*` with the internal hom
(`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedHomComparison`), the canonical datum
`φ_Λ : Lg^* Λ_X ≅ Λ_X` (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`) and `φ_K⁻¹`. It
is an isomorphism for a dualizable (perfect) `K`
(`AlgebraicGeometry.Etale.isIso_contragredientWeilDatum`). -/
noncomputable def contragredientWeilDatum (φ : L((g)^*[A]).obj K ≅ K) :
    L((g)^*[A]).obj ((DerivedCategory.coefficientDual A X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual A X).obj (op K) :=
  leftDerivedUpperStarDerivedHomComparison A g K (𝟙_ _) ≫
    (RHom(X)[A].obj (op (L((g)^*[A]).obj K))).map (leftDerivedUpperStarUnitIso A g).hom ≫
      (RHom(X)[A].map φ.inv.op).app (𝟙_ _)

/-- The contragredient datum is characterised by the evaluation: `ev_K ∘ (K ⊗ᴸ φ_{K^∨})` is
```
                φ_K⁻¹ ⊗ᴸ id                        ≅                       Lg^* ev_K
  K ⊗ᴸ Lg^* K^∨ ──────────▶ Lg^* K ⊗ᴸ Lg^* K^∨ ────▶ Lg^*(K ⊗ᴸ K^∨) ──────────▶ Lg^* Λ_X
                   φ_Λ
                ──────▶ Λ_X.
``` -/
lemma derivedTensor_map_contragredientWeilDatum_comp_coefficientEvaluation
    (φ : L((g)^*[A]).obj K ≅ K) :
    ((derivedTensor A X).obj K).map (contragredientWeilDatum A g φ) ≫
        DerivedCategory.coefficientEvaluation K =
      ((derivedTensor A X).map φ.inv).app _ ≫ (leftDerivedUpperStarTensorIso A g K _).inv ≫
        L((g)^*[A]).map (DerivedCategory.coefficientEvaluation K) ≫
          (leftDerivedUpperStarUnitIso A g).hom := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← leftDerivedUpperStarMonoidal_μ]
  exact Functor.LaxMonoidal.whiskerLeft_ihomComparison_comp_pre_comp_ev _ φ _

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data
(Step 1).

The contragredient datum `φ_{K^∨} : Lg^* K^∨ ⟶ K^∨` of a Weil datum `φ_K : Lg^* K ≅ K` on a
perfect (dualizable) complex `K` is an isomorphism, so it is a genuine Weil datum on `K^∨`. Here
`g` is any endomorphism of `X`; for an automorphism it is an isomorphism for every `K`. -/
theorem isIso_contragredientWeilDatum (φ : L((g)^*[A]).obj K ≅ K) (hK : IsDualizable K) :
    IsIso (contragredientWeilDatum A g φ) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  let := leftDerivedUpperStarMonoidal A g
  exact Functor.LaxMonoidal.isIso_ihomComparison_comp_pre _ (Y := Kᘁ) φ _

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data
(Step 2).

The coefficient evaluation `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` intertwines the tensor product datum
`φ_K ⊗ φ_{K^∨}` with the canonical datum `φ_Λ` of `Λ_X`:
`φ_Λ ∘ Lg^* ev_K = ev_K ∘ (φ_K ⊗ φ_{K^∨}) ∘ (Lg^*(K ⊗ᴸ K^∨) ≅ Lg^* K ⊗ᴸ Lg^* K^∨)`. -/
theorem map_coefficientEvaluation_comp_leftDerivedUpperStarUnitIso_hom
    (φ : L((g)^*[A]).obj K ≅ K) :
    L((g)^*[A]).map (DerivedCategory.coefficientEvaluation K) ≫
        (leftDerivedUpperStarUnitIso A g).hom =
      ((leftDerivedUpperStarTensorIso A g K _).hom ≫ ((derivedTensor A X).map φ.hom).app _ ≫
        ((derivedTensor A X).obj K).map (contragredientWeilDatum A g φ)) ≫
        DerivedCategory.coefficientEvaluation K := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← leftDerivedUpperStarMonoidal_δ]
  exact Functor.LaxMonoidal.map_ev_comp_eq_δ_comp_ihomComparison_comp_pre _ φ _

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data
(Step 3).

For a Weil datum `τ : Lg^* T ⟶ T` on an object `T` (for `T = Λ_X(r)`, the Tate datum `τ_r`),
the twisted evaluation `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` (`AlgebraicGeometry.Etale.twistedEvaluation`)
intertwines the datum `φ_K ⊗ (φ_{K^∨} ⊗ τ)` with `τ`: the twisted dual `K^∨(r) = K^∨ ⊗ᴸ Λ_X(r)`
with the datum `φ_{K^∨(r)} = φ_{K^∨} ⊗ τ_r` pairs equivariantly with `K` into `Λ_X(r)`. -/
theorem map_twistedEvaluation_comp (φ : L((g)^*[A]).obj K ≅ K)
    {T : DerivedCategory (Sheaf X.smallEtaleTopology A)} (τ : L((g)^*[A]).obj T ⟶ T) :
    L((g)^*[A]).map (twistedEvaluation T K) ≫ τ =
      ((leftDerivedUpperStarTensorIso A g K _).hom ≫ ((derivedTensor A X).map φ.hom).app _ ≫
        ((derivedTensor A X).obj K).map ((leftDerivedUpperStarTensorIso A g _ T).hom ≫
          ((derivedTensor A X).map (contragredientWeilDatum A g φ)).app _ ≫
            ((derivedTensor A X).obj _).map τ)) ≫ twistedEvaluation T K := by
  let := leftDerivedUpperStarMonoidal A g
  have hu := leftDerivedUpperStarTensorComparison_leftUnitor_hom A g T
  rw [← leftDerivedUpperStarTensorIso_hom, ← leftDerivedUpperStarMonoidal_δ] at hu
  rw [← leftDerivedUpperStarMonoidal_δ, ← leftDerivedUpperStarMonoidal_δ]
  exact Functor.OplaxMonoidal.map_twistedPairing_comp _ φ.hom (contragredientWeilDatum A g φ)
    (leftDerivedUpperStarUnitIso A g).hom τ (DerivedCategory.coefficientEvaluation K)
    (by
      rw [map_coefficientEvaluation_comp_leftDerivedUpperStarUnitIso_hom A g φ,
        leftDerivedUpperStarMonoidal_δ]
      rfl)
    hu

/-- Blueprint `theorem-poincare-duality-frobenius--1`: Dual and Tate Weil data (the datum on an
internal hom).

The datum `Lg^* RHom(K, M) ⟶ RHom(K, M)` on the internal hom of a complex `K` with a Weil datum
`φ_K : Lg^* K ≅ K` into a complex `M` with a datum `χ : Lg^* M ⟶ M`, the typed composite
```
                     ≅                             RHom(id, χ)                RHom(φ_K⁻¹, id)
  Lg^* RHom(K, M) ────▶ RHom(Lg^* K, Lg^* M) ───────────▶ RHom(Lg^* K, M) ───────────────▶
  RHom(K, M).
```
For `M = Λ_X` with its canonical datum it is the contragredient datum
(`AlgebraicGeometry.Etale.contragredientWeilDatum_eq_derivedHomWeilDatum`); for `M = ω_X` it is
the datum on the Verdier dual `𝔻_X K`. -/
noncomputable def derivedHomWeilDatum {M : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (φ : L((g)^*[A]).obj K ≅ K) (χ : L((g)^*[A]).obj M ⟶ M) :
    L((g)^*[A]).obj ((RHom(X)[A].obj (op K)).obj M) ⟶ (RHom(X)[A].obj (op K)).obj M :=
  leftDerivedUpperStarDerivedHomComparison A g K M ≫
    (RHom(X)[A].obj (op (L((g)^*[A]).obj K))).map χ ≫ (RHom(X)[A].map φ.inv.op).app M

lemma contragredientWeilDatum_eq_derivedHomWeilDatum (φ : L((g)^*[A]).obj K ≅ K) :
    contragredientWeilDatum A g φ =
      derivedHomWeilDatum A g φ (leftDerivedUpperStarUnitIso A g).hom :=
  rfl

/-- Blueprint `theorem-poincare-duality-frobenius--2`: the contragredient datum of a perfect
complex as an isomorphism `φ_{K^∨} : Lg^* K^∨ ≅ K^∨`
(`AlgebraicGeometry.Etale.isIso_contragredientWeilDatum`). -/
noncomputable def contragredientWeilDatumIso (φ : L((g)^*[A]).obj K ≅ K) (hK : IsDualizable K) :
    L((g)^*[A]).obj ((DerivedCategory.coefficientDual A X).obj (op K)) ≅
      (DerivedCategory.coefficientDual A X).obj (op K) :=
  haveI := isIso_contragredientWeilDatum A g φ hK
  asIso (contragredientWeilDatum A g φ)

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data
(Step 4).

Let `γ : T ≅ ω_X` be an isomorphism from an invertible complex `T` (for an orientation,
`T = Λ_X(d)[2d]`) to an object `ω_X` (the dualizing complex; the statement holds for any
object `ω_X`), which is a morphism of Weil objects for data
`τ : Lg^* T ⟶ T` and `χ : Lg^* ω_X ⟶ ω_X` (for the purity isomorphism and the
geometric-Frobenius data this is the Weil equivariance of purity,
`proposition-purity-trace-commute-frobenius`). Then the identification
`θ_K : 𝔻_X K ≅ K^∨ ⊗ᴸ T` of `theorem-poincare-duality--2`
(`AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor`) is an isomorphism of Weil
objects, for the datum on `𝔻_X K = RHom(K, ω_X)` induced by `φ_K` and `χ`
(`AlgebraicGeometry.Etale.derivedHomWeilDatum`) and the twisted contragredient datum
`φ_{K^∨} ⊗ τ` on `K^∨ ⊗ᴸ T`. -/
theorem leftDerivedUpperStar_map_verdierDualIsoCoefficientDualTensor_comp
    {ω T : DerivedCategory (Sheaf X.smallEtaleTopology A)} (γ : T ≅ ω)
    (hT : IsInvertible T) (φ : L((g)^*[A]).obj K ≅ K) (τ : L((g)^*[A]).obj T ⟶ T)
    (χ : L((g)^*[A]).obj ω ⟶ ω)
    (hγ : L((g)^*[A]).map γ.hom ≫ χ = τ ≫ γ.hom) :
    L((g)^*[A]).map ((verdierDualIsoCoefficientDualTensor γ hT).hom.app (op K)) ≫
        ((leftDerivedUpperStarTensorIso A g _ T).hom ≫
          ((derivedTensor A X).map (contragredientWeilDatum A g φ)).app _ ≫
            ((derivedTensor A X).obj _).map τ) =
      derivedHomWeilDatum A g φ χ ≫ (verdierDualIsoCoefficientDualTensor γ hT).hom.app (op K) := by
  let := leftDerivedUpperStarMonoidal A g
  refine Functor.LaxMonoidal.map_hom_comp_eq_ihomComparison_comp_map_comp_pre_comp _ φ χ τ γ hγ
    ((verdierDualIsoCoefficientDualTensor γ hT).app (op K)) (twistedEvaluation T K)
    (whiskerLeft_verdierDualIsoCoefficientDualTensor_hom_app_comp γ hT K) _ ?_
  rw [leftDerivedUpperStarMonoidal_δ]
  exact map_twistedEvaluation_comp A g φ τ

end Datum

end Etale

end AlgebraicGeometry
