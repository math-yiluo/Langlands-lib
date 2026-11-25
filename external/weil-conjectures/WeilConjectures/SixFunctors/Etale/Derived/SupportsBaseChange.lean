/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Restriction of cup products with supports

The cup product with supports (`AlgebraicGeometry.Etale.cupWithSupports`) commutes with the
restriction of supports (`AlgebraicGeometry.Etale.restrictSupportedClass`) along any morphism
`e : U' ⟶ U`: restricting `α ∪ β` is the cup product of the restrictions of `α` and `β`, provided
the diagonals used to multiply the classes are compatible with the pullback.

Both sides are classes `K' ⟶ Ri'_! Ri'^! (M' ⊗ N')` built out of lifts through counits, and the
comparison reduces to the base change of the product of supports
(`AlgebraicGeometry.Etale.supportedProduct`): two maps out of an object supported on `Z'` into
`Ri'_! Ri'^! L'` agree as soon as their composites with the counit agree.

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_derivedTensor_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.supportedProduct_baseChange`
- `AlgebraicGeometry.Etale.restrictSupportedClass_cupWithSupports`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {U U' W Z₁ Z₂ Z Z₁' Z₂' Z' : Scheme.{u}}

/-- A tensor product `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N` restricts to zero along every `w : W ⟶ U`
missing `Z = Z₁ ∩ Z₂`: on the open complement of `Z`, its restrictions to the complements of
`Z₁` and of `Z₂` vanish, and these two opens cover it. -/
lemma isZero_leftDerivedUpperStar_derivedTensor_rightDerivedLowerShriek (i₁ : Z₁ ⟶ U)
    (i₂ : Z₂ ⟶ U) (i : Z ⟶ U) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (w : W ⟶ U)
    (hw : Set.range w.base ⊆ Set.range i.openComplement.ι.base) :
    IsZero ((L((w)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))).obj ((R(i₂)_![ModuleCat.{u + 1}
          Λ]).obj ((R(i₂)^![Λ]).obj N)))) := by
  set j := i.openComplement.ι
  have hj : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
      U).obj
      ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))).obj
        ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N)))) := by
    have hcd : Disjoint (Set.range (pullback.snd i₁ j)) (Set.range (pullback.snd i₂ j)) := by
      rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
      intro x hx₁ hx₂
      apply x.2
      rw [h]
      exact ⟨hx₁, hx₂⟩
    refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint Λ (pullback.snd i₁ j)
      (pullback.snd i₂ j) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
      (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_left
        (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
          (ModuleCat.{u + 1} Λ) i₁ j _)
          _).of_iso (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_right _
        (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
          (ModuleCat.{u + 1} Λ) i₂ j _)).of_iso
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
  rw [← IsOpenImmersion.lift_fac j w hw]
  exact ((L((IsOpenImmersion.lift j w hw)^*[ModuleCat.{u + 1} Λ])).map_isZero hj).of_iso
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _)

variable (e : U' ⟶ U) [(e)^*[A].PreservesFlat] [(e)^*[ModuleCat.{u + 1} Λ].PreservesFlat]

/-- The comparison `Le^*(K ⊗ M) ≅ Le^* K ⊗ Le^* M` is natural in both variables:
```
  Le^*(K ⊗ M) ----------> Le^*(K₁ ⊗ M₁)
       |                        |
       v                        v
  Le^*K ⊗ Le^*M -------> Le^*K₁ ⊗ Le^*M₁
```
-/
@[reassoc]
lemma leftDerivedUpperStarTensorIso_hom_naturality
    {K K₁ M M₁ : DerivedCategory (Sheaf U.smallEtaleTopology A)} (f : K ⟶ K₁) (g : M ⟶ M₁) :
    (L((e)^*[A])).map (derivedTensorHom A f g) ≫ (leftDerivedUpperStarTensorIso A e K₁ M₁).hom =
      (leftDerivedUpperStarTensorIso A e K M).hom ≫
        derivedTensorHom A ((L((e)^*[A])).map f) ((L((e)^*[A])).map g) := by
  have h₁ := congr_app ((leftDerivedUpperStarTensorNatIso A e).hom.naturality f) M
  have h₂ := ((leftDerivedUpperStarTensorNatIso A e).hom.app K₁).naturality g
  simp only [NatTrans.comp_app] at h₁ h₂
  simp only [leftDerivedUpperStarTensorIso, Iso.app_hom, Functor.map_comp, Category.assoc,
    derivedTensorHom]
  erw [h₂]
  rw [← Category.assoc, ← Category.assoc]
  erw [h₁]
  rfl

/-- **Base change of the product of supports.** For closed immersions `i₁, i₂, i` into `U` with
`Z = Z₁ ∩ Z₂`, their base changes `i₁', i₂', i'` along `e : U' ⟶ U`, and identifications
`τ_M : Le^* M ≅ M'`, `τ_N : Le^* N ≅ N'`, the product of supports
(`AlgebraicGeometry.Etale.supportedProduct`) commutes with the restrictions of supports `ψ`:

```
Le^*(R₁ ⊗ R₂) ──Le^* P──▶ Le^* Ri_! Ri^! (M ⊗ N) ──ψ──▶ Ri'_! Ri'^! (M' ⊗ N')
      │ ≅                                                        ‖
      ▼                                                          ‖
Le^* R₁ ⊗ Le^* R₂ ────ψ₁ ⊗ ψ₂────▶ R₁' ⊗ R₂' ─────P'──────▶ Ri'_! Ri'^! (M' ⊗ N')
```

Both composites lift `Le^*(ε₁ ⊗ ε₂)` through the counit, and their source is supported on `Z'`.
-/
theorem supportedProduct_baseChange (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    (i₁' : Z₁' ⟶ U') (i₂' : Z₂' ⟶ U') (i' : Z' ⟶ U')
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂'] [IsClosedImmersion i']
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range i'.base = Set.range i₁'.base ∩ Set.range i₂'.base)
    (g₁ : Z₁' ⟶ Z₁) (g₂ : Z₂' ⟶ Z₂) (g : Z' ⟶ Z) (hg₁ : IsPullback g₁ i₁' i₁ e)
    (hg₂ : IsPullback g₂ i₂' i₂ e) (hg : IsPullback g i' i e)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M' N' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τM : (L((e)^*[ModuleCat.{u + 1} Λ])).obj M ≅ M') (τN : (L((e)^*[ModuleCat.{u + 1} Λ])).obj N ≅
        N') :
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e _ _).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedProduct Λ i₁ i₂ i h M N) ≫
          supportedRestriction Λ e i i' g hg _ _
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e M N ≪≫
              ((derivedTensor (ModuleCat.{u + 1} Λ) U').mapIso τM).app _ ≪≫ ((derivedTensor
                  (ModuleCat.{u + 1} Λ) U').obj M').mapIso τN) =
      derivedTensorHom (ModuleCat.{u + 1} Λ) (supportedRestriction Λ e i₁ i₁' g₁ hg₁ M M' τM)
          (supportedRestriction Λ e i₂ i₂' g₂ hg₂ N N' τN) ≫
        supportedProduct Λ i₁' i₂' i' h' M' N' := by
  set j' := i'.openComplement.ι
  have hP := (existsUnique_supportedProduct Λ i₁ i₂ i h M N).exists.choose_spec
  have hP' := (existsUnique_supportedProduct Λ i₁' i₂' i' h' M' N').exists.choose_spec
  have hψ := (existsUnique_supportedRestriction Λ e i i' g hg _ _
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e M N ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U').mapIso τM).app _ ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U').obj M').mapIso τN)).exists.choose_spec
  have hψ₁ := (existsUnique_supportedRestriction Λ e i₁ i₁' g₁ hg₁ M M' τM).exists.choose_spec
  have hψ₂ := (existsUnique_supportedRestriction Λ e i₂ i₂' g₂ hg₂ N N' τN).exists.choose_spec
  -- the source is supported on `Z'`
  have hj' : Set.range (j' ≫ e).base ⊆ Set.range i.openComplement.ι.base := by
    rw [← compl_compl (Set.range i.openComplement.ι.base),
      ← i.range_eq_compl_range_openComplement_ι, Set.subset_compl_iff_disjoint_left,
      Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
    apply x.2
    rw [Scheme.range_snd_of_isPullback hg]
    exact ⟨z, hx.symm⟩
  have hS := (isZero_leftDerivedUpperStar_derivedTensor_rightDerivedLowerShriek Λ i₁ i₂ i h M N
    (j' ≫ e) hj').of_iso ((L((j')^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTensorIso
        (ModuleCat.{u + 1} Λ) e _ _).symm ≪≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j' e).app _).symm)
  refine (existsUnique_comp_counit_of_isZero Λ i' j' i'.range_eq_compl_range_openComplement_ι hS
    _).unique ?_ rfl
  have hP₁ : supportedProduct Λ i₁ i₂ i h M N ≫
      (rightDerivedUpperShriekAdjunction Λ i).counit.app (((derivedTensor (ModuleCat.{u + 1} Λ)
          U).obj M).obj N) =
        derivedTensorHom (ModuleCat.{u + 1} Λ) ((rightDerivedUpperShriekAdjunction Λ i₁).counit.app
            M)
          ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) := hP
  have hP₁' : supportedProduct Λ i₁' i₂' i' h' M' N' ≫
      (rightDerivedUpperShriekAdjunction Λ i').counit.app (((derivedTensor (ModuleCat.{u + 1} Λ)
          U').obj M').obj N') =
        derivedTensorHom (ModuleCat.{u + 1} Λ) ((rightDerivedUpperShriekAdjunction Λ i₁').counit.app
            M')
          ((rightDerivedUpperShriekAdjunction Λ i₂').counit.app N') := hP'
  have hτ : (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e M N ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U').mapIso τM).app _ ≪≫ ((derivedTensor (ModuleCat.{u +
          1} Λ) U').obj M').mapIso τN).hom =
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e M N).hom ≫ derivedTensorHom
            (ModuleCat.{u + 1} Λ) τM.hom τN.hom := by
    simp [derivedTensorHom]
  simp only [Category.assoc]
  erw [hψ]
  rw [hP₁', derivedTensorHom_comp]
  erw [hψ₁, hψ₂]
  rw [← Functor.map_comp_assoc, hP₁, hτ]
  rw [Iso.inv_comp_eq, ← derivedTensorHom_comp]
  exact leftDerivedUpperStarTensorIso_hom_naturality_assoc (ModuleCat.{u + 1} Λ) e _ _ _

/-- **Base change of the cup product with supports.** Restricting a cup product with supports
`α ∪ β` (`AlgebraicGeometry.Etale.cupWithSupports`) along `e : U' ⟶ U` gives the cup product of
the restrictions of `α` and `β` (`AlgebraicGeometry.Etale.restrictSupportedClass`), for diagonals
`Δ : K ⟶ K ⊗ K` and `Δ' : K' ⟶ K' ⊗ K'` compatible with the pullback along `σ : K' ⟶ Le^* K`. -/
theorem restrictSupportedClass_cupWithSupports (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    (i₁' : Z₁' ⟶ U') (i₂' : Z₂' ⟶ U') (i' : Z' ⟶ U')
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂'] [IsClosedImmersion i']
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range i'.base = Set.range i₁'.base ∩ Set.range i₂'.base)
    (g₁ : Z₁' ⟶ Z₁) (g₂ : Z₂' ⟶ Z₂) (g : Z' ⟶ Z) (hg₁ : IsPullback g₁ i₁' i₁ e)
    (hg₂ : IsPullback g₂ i₂' i₂ e) (hg : IsPullback g i' i e)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' M' N' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
    (τM : (L((e)^*[ModuleCat.{u + 1} Λ])).obj M ≅ M') (τN : (L((e)^*[ModuleCat.{u + 1} Λ])).obj N ≅
        N')
    (Δ : K ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj K) (Δ' : K' ⟶ ((derivedTensor
        (ModuleCat.{u + 1} Λ) U').obj K').obj K')
    (hΔ : Δ' ≫ derivedTensorHom (ModuleCat.{u + 1} Λ) σ σ =
      σ ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map Δ ≫ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1}
          Λ) e K K).hom)
    (α : K ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))
    (β : K ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N)) :
    restrictSupportedClass Λ e i i' g hg σ
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e M N ≪≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) U').mapIso τM).app _ ≪≫ ((derivedTensor
              (ModuleCat.{u + 1} Λ) U').obj M').mapIso τN)
        (cupWithSupports Λ i₁ i₂ i h Δ α β) =
      cupWithSupports Λ i₁' i₂' i' h' Δ' (restrictSupportedClass Λ e i₁ i₁' g₁ hg₁ σ τM α)
        (restrictSupportedClass Λ e i₂ i₂' g₂ hg₂ σ τN β) := by
  have hc : ∀ {X : Scheme.{u}} {Y₁ Y₂ Y : Scheme.{u}} (j₁ : Y₁ ⟶ X) (j₂ : Y₂ ⟶ X) (j : Y ⟶ X)
      [IsClosedImmersion j₁] [IsClosedImmersion j₂] [IsClosedImmersion j]
      (hj : Set.range j.base = Set.range j₁.base ∩ Set.range j₂.base)
      {K M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (Δ : K ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj K)
      (α : K ⟶ (R(j₁)_![ModuleCat.{u + 1} Λ]).obj ((R(j₁)^![Λ]).obj M))
      (β : K ⟶ (R(j₂)_![ModuleCat.{u + 1} Λ]).obj ((R(j₂)^![Λ]).obj N)),
      cupWithSupports Λ j₁ j₂ j hj Δ α β =
        Δ ≫ derivedTensorHom (ModuleCat.{u + 1} Λ) α β ≫ supportedProduct Λ j₁ j₂ j hj M N := by
    intros
    simp [cupWithSupports, derivedTensorHom]
  have key : (L((e)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorHom (ModuleCat.{u + 1} Λ) α β) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e K K).hom ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) ((L((e)^*[ModuleCat.{u + 1} Λ])).map α)
            ((L((e)^*[ModuleCat.{u + 1} Λ])).map β) ≫
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e _ _).inv := by
    rw [← cancel_mono (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e _ _).hom,
        Category.assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id,
      leftDerivedUpperStarTensorIso_hom_naturality]
  have hP := supportedProduct_baseChange Λ e i₁ i₂ i i₁' i₂' i' h h' g₁ g₂ g hg₁ hg₂ hg M N M' N'
    τM τN
  rw [hc, hc]
  simp only [restrictSupportedClass, Functor.map_comp, Category.assoc]
  rw [key]
  simp only [Category.assoc]
  rw [hP, ← reassoc_of% hΔ, derivedTensorHom_comp_assoc, derivedTensorHom_comp_assoc]
  simp only [Category.assoc]

omit [(e)^*[ModuleCat.{u + 1} Λ].PreservesFlat] in
/-- **Naturality of the restriction of supports in the coefficients.** For `φ : L₁ ⟶ L₂` on `U`
and `φ' : L₁' ⟶ L₂'` on `U'` compatible with identifications `τ₁ : Le^* L₁ ≅ L₁'` and
`τ₂ : Le^* L₂ ≅ L₂'`, restricting `γ ≫ Ri_! Ri^! φ` gives the restriction of `γ` followed by
`Ri'_! Ri'^! φ'`:
```
  K' --- restriction of γ ---> Ri'_! Ri'^! L₁'
     \                               |
      \                              | Ri'_! Ri'^! φ'
       \                             v
        ------------------->  Ri'_! Ri'^! L₂'
       restriction of γ ≫ Ri_! Ri^! φ
```
-/
theorem restrictSupportedClass_map (i : Z ⟶ U) (i' : Z' ⟶ U') [IsClosedImmersion i]
 [IsClosedImmersion i']
    (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {K L₁ L₂ : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L₁' L₂' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K) (τ₁ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L₁ ≅
        L₁')
    (τ₂ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L₂ ≅ L₂') (φ : L₁ ⟶ L₂) (φ' : L₁' ⟶ L₂')
    (hφ : (L((e)^*[ModuleCat.{u + 1} Λ])).map φ ≫ τ₂.hom = τ₁.hom ≫ φ')
    (γ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L₁)) :
    restrictSupportedClass Λ e i i' g hg σ τ₂ (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map
        ((R(i)^![Λ]).map φ)) =
      restrictSupportedClass Λ e i i' g hg σ τ₁ γ ≫ (R(i')_![ModuleCat.{u + 1} Λ]).map
          ((R(i')^![Λ]).map φ') := by
  have hψ₁ := (existsUnique_supportedRestriction Λ e i i' g hg L₁ L₁' τ₁).exists.choose_spec
  have hψ₂ := (existsUnique_supportedRestriction Λ e i i' g hg L₂ L₂' τ₂).exists.choose_spec
  have hS : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj
          L₁)))) := by
    have hk : Set.range (i'.openComplement.ι ≫ e).base ⊆ Set.range i.openComplement.ι.base := by
      rw [← compl_compl (Set.range i.openComplement.ι.base),
        ← i.range_eq_compl_range_openComplement_ι, Set.subset_compl_iff_disjoint_left,
        Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
      apply x.2
      rw [Scheme.range_snd_of_isPullback hg]
      exact ⟨z, hx.symm⟩
    have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
      rw [i.range_eq_compl_range_openComplement_ι]
      exact disjoint_compl_left
    exact (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ)
        i
      i.openComplement.ι hdisj _ hk _).of_iso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i'.openComplement.ι e).app _).symm
  have key : (L((e)^*[ModuleCat.{u + 1} Λ])).map ((R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map
      φ)) ≫
      supportedRestriction Λ e i i' g hg L₂ L₂' τ₂ =
        supportedRestriction Λ e i i' g hg L₁ L₁' τ₁ ≫
          (R(i')_![ModuleCat.{u + 1} Λ]).map ((R(i')^![Λ]).map φ') := by
    refine (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
      i'.range_eq_compl_range_openComplement_ι hS _).unique rfl ?_
    simp only [Category.assoc]
    erw [(rightDerivedUpperShriekAdjunction Λ i').counit.naturality φ', reassoc_of% hψ₁, hψ₂]
    rw [← Functor.map_comp_assoc]
    erw [(rightDerivedUpperShriekAdjunction Λ i).counit.naturality φ]
    rw [Functor.map_comp_assoc]
    erw [hφ]
    rfl
  simp only [restrictSupportedClass, Functor.map_comp, Category.assoc, key]

omit [(e)^*[ModuleCat.{u + 1} Λ].PreservesFlat] in
/-- Restricting a class supported everywhere (`AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`)
gives the class supported everywhere lifting the restricted morphism. -/
theorem restrictSupportedClass_liftCounitOfRangeEqUniv (i : Z ⟶ U) (i' : Z' ⟶ U')
    [IsClosedImmersion i] [IsClosedImmersion i']
 (hi : Set.range i.base = Set.univ)
    (hi' : Set.range i'.base = Set.univ) (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K) (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅
        L') (φ : K ⟶ L) (φ' : K' ⟶ L')
    (hφ : σ ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map φ ≫ τ.hom = φ') :
    restrictSupportedClass Λ e i i' g hg σ τ (liftCounitOfRangeEqUniv Λ i hi φ) =
      liftCounitOfRangeEqUniv Λ i' hi' φ' := by
  have h₁ := (existsUnique_comp_counit_of_range_eq_univ Λ i hi φ).exists.choose_spec
  have hψ := (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec
  refine (existsUnique_comp_counit_of_range_eq_univ Λ i' hi' φ').unique ?_
    (existsUnique_comp_counit_of_range_eq_univ Λ i' hi' φ').exists.choose_spec
  simp only [restrictSupportedClass, Category.assoc]
  erw [hψ]
  rw [← Functor.map_comp_assoc]
  erw [h₁]
  exact hφ

omit [(e)^*[ModuleCat.{u + 1} Λ].PreservesFlat] in
/-- **Transitivity of the restriction of supports** along a composite `e' = e₁ ≫ e`:
```
  Le'^* Ri_! Ri^! L ------------------------------> Ri₂_! Ri₂^! L₂
          |                                                ^
          v                                                |
  Le₁^* Le^* Ri_! Ri^! L ---> Le₁^* Ri'_! Ri'^! L' --------+
```
-/
theorem supportedRestriction_trans {U₂ Z₂ : Scheme.{u}} (e₁ : U₂ ⟶ U') (e' : U₂ ⟶ U)
    (he : e' = e₁ ≫ e) (i : Z ⟶ U) (i' : Z' ⟶ U') (i₂ : Z₂ ⟶ U₂) [IsClosedImmersion i]
 [IsClosedImmersion i']
    [IsClosedImmersion i₂] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (g₂ : Z₂ ⟶ Z') (hg₂ : IsPullback g₂ i₂ i' e₁) (g' : Z₂ ⟶ Z) (hg' : IsPullback g' i₂ i e')
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L₂ : DerivedCategory (Sheaf U₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') (τ₂ : (L((e₁)^*[ModuleCat.{u + 1} Λ])).obj L' ≅
        L₂) :
    supportedRestriction Λ e' i i₂ g' hg' L L₂
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e e' he).app L ≪≫ (L((e₁)^*[ModuleCat.{u
            + 1} Λ])).mapIso τ ≪≫ τ₂) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e e' he).hom.app _ ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map (supportedRestriction Λ e i i' g hg L L' τ) ≫
          supportedRestriction Λ e₁ i' i₂ g₂ hg₂ L' L₂ τ₂ := by
  have hψ := (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec
  have hψ₂ := (existsUnique_supportedRestriction Λ e₁ i' i₂ g₂ hg₂ L' L₂ τ₂).exists.choose_spec
  refine (existsUnique_supportedRestriction Λ e' i i₂ g' hg' L L₂ _).unique
    (existsUnique_supportedRestriction Λ e' i i₂ g' hg' L L₂ _).exists.choose_spec ?_
  simp only [Category.assoc]
  erw [hψ₂]
  rw [← Functor.map_comp_assoc]
  erw [hψ]
  simp only [Functor.map_comp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  erw [(leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e e' he).hom.naturality_assoc]
  rfl

omit [(e)^*[ModuleCat.{u + 1} Λ].PreservesFlat] in
/-- **Transitivity of the restriction of classes with supports** along a composite. -/
theorem restrictSupportedClass_restrictSupportedClass {U₂ Z₂ : Scheme.{u}} (e₁ : U₂ ⟶ U')
    (e' : U₂ ⟶ U)
    (he : e' = e₁ ≫ e) (i : Z ⟶ U) (i' : Z' ⟶ U') (i₂ : Z₂ ⟶ U₂) [IsClosedImmersion i]
 [IsClosedImmersion i']
    [IsClosedImmersion i₂] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (g₂ : Z₂ ⟶ Z') (hg₂ : IsPullback g₂ i₂ i' e₁) (g' : Z₂ ⟶ Z) (hg' : IsPullback g' i₂ i e')
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K₂ L₂ : DerivedCategory (Sheaf U₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K) (σ₂ : K₂ ⟶ (L((e₁)^*[ModuleCat.{u + 1} Λ])).obj
        K')
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') (τ₂ : (L((e₁)^*[ModuleCat.{u + 1} Λ])).obj L' ≅
        L₂)
    (γ : K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    restrictSupportedClass Λ e' i i₂ g' hg'
        (σ₂ ≫ (L((e₁)^*[ModuleCat.{u + 1} Λ])).map σ ≫ (leftDerivedUpperStarComp (ModuleCat.{u + 1}
            Λ) e₁ e e' he).inv.app K)
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e e' he).app L ≪≫ (L((e₁)^*[ModuleCat.{u
            + 1} Λ])).mapIso τ ≪≫ τ₂) γ =
      restrictSupportedClass Λ e₁ i' i₂ g₂ hg₂ σ₂ τ₂
        (restrictSupportedClass Λ e i i' g hg σ τ γ) := by
  simp only [restrictSupportedClass, supportedRestriction_trans Λ e e₁ e' he i i' i₂ g hg g₂ hg₂ g'
    hg', Functor.map_comp, Category.assoc]
  erw [(leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e e' he).hom.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
  rfl

end Etale

end AlgebraicGeometry
