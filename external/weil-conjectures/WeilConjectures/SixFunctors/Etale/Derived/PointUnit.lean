/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.CategoryTheory.Monoidal.UnitIsoBijective
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.Point

/-!
# Morphisms out of the unit in the point category

Let `k` be a separably closed field and `s = Spec k`. In the point category `D(s_ét, Λ)`, the
unit `Λ_s` is the constant sheaf `Λ` placed in degree `0`, and it detects cohomology sheaves
(`AlgebraicGeometry.Etale.exists_ne_zero_of_not_isZero_homology_of_isSepClosed`). This file
shows that a morphism `u : Λ_s ⟶ P` to an object `P ∈ D^{≥ 0}` inducing a bijection
`Hom(Λ_s, Λ_s) ≃ Hom(Λ_s, P)` has its cone in `D^{≥ 1}`.

## Main statements

- `AlgebraicGeometry.Etale.unitIsoSingleFunctorConstantSheaf`: `Λ_X ≅ (constant sheaf Λ)[0]`.
- `AlgebraicGeometry.Etale.isGE_one_of_bijective_comp_of_isSepClosed`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

variable (Λ) in
/-- The unit `Λ_X` of `D(X_ét, Λ)` is the constant sheaf `Λ` placed in degree `0`. -/
noncomputable def unitIsoSingleFunctorConstantSheaf (X : Scheme.{u}) :
    𝟙_ (DerivedCategoryModule Λ X) ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) :=
  constantComplexIsoSingleFunctor Λ X ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

instance (X : Scheme.{u}) : (𝟙_ (DerivedCategoryModule Λ X)).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (unitIsoSingleFunctorConstantSheaf Λ X).symm 0

instance (X : Scheme.{u}) : (𝟙_ (DerivedCategoryModule Λ X)).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (unitIsoSingleFunctorConstantSheaf Λ X).symm 0

variable (Λ) in
/-- For a connected scheme `X`, `r ↦ r • 𝟙` is a bijection from `Λ` onto the endomorphisms of
the unit `Λ_X` of `D(X_ét, Λ)`: `Λ_X` is the constant sheaf `Λ` placed in degree `0`, the
single functor is fully faithful and `Λ`-linear, and the endomorphisms of the constant sheaf
`Λ` are its global sections, which are `Λ` since `X` is connected
(`AlgebraicGeometry.Scheme.bijective_constantSheafAdj_unit_app`). -/
theorem bijective_smul_id_unit (X : Scheme.{u}) [ConnectedSpace X] :
    Function.Bijective (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X))) := by
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  have hU := Scheme.bijective_constantSheafAdj_unit_app X (ModuleCat.of Λ Λ) hT
  let ev : (C ⟶ C) → _ := fun φ ↦ (adj.homEquiv _ _ φ).hom (1 : Λ)
  have hev : Function.Injective ev := by
    intro φ ψ h
    apply (adj.homEquiv _ _).injective
    ext
    exact h
  have hcomp (r : Λ) : ev (r • 𝟙 C) = adj.unit.app (ModuleCat.of Λ Λ) r := by
    have hG : ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (Opposite.op (Scheme.Etale.mk (𝟙 X)))).map (r • 𝟙 C) = r • 𝟙 _ := rfl
    simp only [ev, Adjunction.homEquiv_unit, hG, Linear.comp_smul,
      ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
    rfl
  have hC : Function.Bijective (fun r : Λ ↦ r • 𝟙 C) := by
    refine ⟨fun r s h ↦ hU.1 ?_, fun φ ↦ ?_⟩
    · rw [← hcomp, ← hcomp]
      exact congrArg ev h
    · obtain ⟨r, hr⟩ := hU.2 (ev φ)
      exact ⟨r, hev (by rw [hcomp, hr])⟩
  let E := unitIsoSingleFunctorConstantSheaf Λ X
  have : (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X))) =
      (fun z ↦ E.hom ≫ z ≫ E.symm.hom) ∘ (DerivedCategory.singleFunctor _ 0).map ∘
        (fun r : Λ ↦ r • 𝟙 C) := by
    funext r
    simp [E, C, Functor.map_smul]
  rw [this]
  exact (bijective_conj E E.symm).comp
    (((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _).comp hC)

variable {k : Type u} [Field k] [IsSepClosed k]

/-- Let `k` be separably closed and `u : Λ_s ⟶ P` a morphism of the point category with
`P ∈ D^{≥ 0}`, such that `g ↦ g ≫ u` is a bijection `Hom(Λ_s, Λ_s) ≃ Hom(Λ_s, P)`. Then the
third object `Z` of any distinguished triangle `Λ_s ⟶ P ⟶ Z ⟶ Λ_s[1]` on `u` lies in
`D^{≥ 1}`: a nonzero cohomology sheaf `Hⁿ(Z)`, `n ≤ 0`, would give a nonzero morphism
`Λ_s[-n] ⟶ Z`, which the long exact sequence, the vanishing of `Hom(Λ_s, Λ_s[1])` and the
t-structure rule out. -/
theorem isGE_one_of_bijective_comp_of_isSepClosed
    (T : Triangle (DerivedCategoryModule Λ (Spec (.of k)))) (hT : T ∈ distTriang _)
    (e : T.obj₁ ≅ 𝟙_ _) [T.obj₂.IsGE 0]
    (h : Function.Bijective (fun g : T.obj₁ ⟶ T.obj₁ ↦ g ≫ T.mor₁)) :
    T.obj₃.IsGE 1 := by
  have h₁ : T.obj₁.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have h₁' : T.obj₁.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  rw [DerivedCategory.isGE_iff]
  intro n hn
  by_contra hZ
  obtain ⟨g, hg⟩ := exists_ne_zero_of_not_isZero_homology_of_isSepClosed T.obj₃ n hZ
  apply hg
  let E : (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≅ T.obj₁ :=
    (unitIsoSingleFunctorConstantSheaf Λ _).symm ≪≫ e.symm
  rw [← cancel_epi ((shiftFunctor _ (-n)).map E.inv), comp_zero]
  set g' := (shiftFunctor _ (-n)).map E.inv ≫ g
  have hle : (T.obj₁⟦-n⟧).IsLE n := DerivedCategory.TStructure.t.isLE_shift _ 0 (-n) n (by omega)
  -- the composite `T.obj₁[-n] ⟶ T.obj₃ ⟶ T.obj₁[1]` vanishes
  have h₃ : g' ≫ T.mor₃ = 0 := by
    rcases (show n = 0 ∨ n = -1 ∨ n < -1 by omega) with rfl | rfl | hn'
    · let ι : T.obj₁ ≅ T.obj₁⟦-(0 : ℤ)⟧ := ((shiftFunctorZero' _ (-(0 : ℤ)) (by simp)).app _).symm
      have := DerivedCategory.unit_hom_shift_one_eq_zero_of_iso Λ (Iso.refl (Spec (.of k)))
        (e.inv ≫ ι.hom ≫ g' ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom)
      rw [← cancel_epi ι.hom, comp_zero, ← cancel_epi e.inv, comp_zero,
        ← cancel_mono ((shiftFunctor _ (1 : ℤ)).map e.hom), zero_comp]
      simpa only [Category.assoc] using this
    · have hs : T.obj₁⟦-(-1 : ℤ)⟧ = T.obj₁⟦(1 : ℤ)⟧ := by rw [neg_neg]
      obtain ⟨ψ, hψ⟩ := (shiftFunctor _ (1 : ℤ)).map_surjective (eqToHom hs.symm ≫ g' ≫ T.mor₃)
      have hψ' : ψ ≫ T.mor₁ = 0 := by
        apply (shiftFunctor _ (1 : ℤ)).map_injective
        rw [Functor.map_comp, hψ, Functor.map_zero, Category.assoc, Category.assoc,
          comp_distTriang_mor_zero₃₁ _ hT, comp_zero, comp_zero]
      have hψ0 : ψ = 0 := h.1 (hψ'.trans zero_comp.symm)
      rw [hψ0, Functor.map_zero] at hψ
      rw [← cancel_epi (eqToHom hs.symm), comp_zero]
      exact hψ.symm
    · have : (T.obj₁⟦(1 : ℤ)⟧).IsGE (-1) :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by omega)
      exact DerivedCategory.TStructure.t.zero _ n (-1) hn'
  obtain ⟨g'', hg''⟩ := Triangle.coyoneda_exact₃ _ hT g' h₃
  rw [hg'']
  rcases (show n = 0 ∨ n < 0 by omega) with rfl | hn'
  · let ι : T.obj₁ ≅ T.obj₁⟦-(0 : ℤ)⟧ := ((shiftFunctorZero' _ (-(0 : ℤ)) (by simp)).app _).symm
    obtain ⟨ψ, hψ⟩ := h.2 (ι.hom ≫ g'')
    have : g'' = ι.inv ≫ ψ ≫ T.mor₁ := by
      have hψ' : ψ ≫ T.mor₁ = ι.hom ≫ g'' := hψ
      rw [hψ', Iso.inv_hom_id_assoc]
    rw [this, Category.assoc, Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero,
      comp_zero]
  · rw [DerivedCategory.TStructure.t.zero g'' n 0 hn', zero_comp]

end AlgebraicGeometry.Etale
