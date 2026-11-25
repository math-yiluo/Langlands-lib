/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Restriction of supports along an open immersion

Let `i : Z ⟶ X` be a closed immersion, `e : U ⟶ X` an open immersion and `i' : Z' ⟶ U` the base
change of `i`. The restriction of supports
`ψ : Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'` (`AlgebraicGeometry.Etale.supportedRestriction`) is an
isomorphism: classes with supports in `Z` restrict to classes with supports in `Z'` without loss
of information about `Z'`.

The source of `ψ` is supported on `Z'`, and it satisfies the universal property of the target:
for an object `T` of `D(U_ét)` supported on `Z'`, maps `T ⟶ Le^* (Ri_! Ri^! L)` are, by the
adjunction `e_! ⊣ e^*`, maps `e_! T ⟶ Ri_! Ri^! L`, and these factor uniquely through the counit
because the extension by zero `e_! T` is supported on `Z`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_openComplement_obj_openImmersionLowerShriek`
- `AlgebraicGeometry.Etale.isIso_supportedRestriction_of_isOpenImmersion`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {U X Z Z' : Scheme.{u}}

/-- The extension by zero along an open immersion `e : U ⟶ X` of an object supported on the
base change `Z'` of a closed immersion `i : Z ⟶ X` is supported on `Z`: its restriction to the
open complement `V` of `Z` is the extension by zero along `U ×_X V ⟶ V` of the restriction of
`T` to `U ×_X V`, the open complement of `Z'` in `U`
(`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`). -/
lemma isZero_leftDerivedUpperStar_openComplement_obj_openImmersionLowerShriek (e : U ⟶ X)
    [IsOpenImmersion e] (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i] [IsClosedImmersion i']
    (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {T : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (hT : IsZero ((L((i'.openComplement.ι)^*[A])).obj T)) :
    IsZero ((L((i.openComplement.ι)^*[A])).obj (D((e)_!open[A]).obj T)) := by
  set jV := i.openComplement.ι
  have hsq := IsPullback.of_hasPullback e jV
  -- `U ×_X V ⟶ U` is the open complement of `Z'`
  have hrange : Set.range (pullback.fst e jV).base ⊆ Set.range i'.openComplement.ι.base := by
    rintro _ ⟨p, rfl⟩
    have hp : (pullback.fst e jV).base p ∉ Set.range i'.base := by
      rintro ⟨z', hz'⟩
      have h₁ : i (g z') = jV ((pullback.snd e jV) p) := by
        rw [← Scheme.Hom.comp_apply, hg.w, Scheme.Hom.comp_apply, hz', ← Scheme.Hom.comp_apply,
          pullback.condition, Scheme.Hom.comp_apply]
      have h₂ : jV ((pullback.snd e jV) p) ∈ (Set.range i.base)ᶜ := by
        rw [i.range_eq_compl_range_openComplement_ι, compl_compl]
        exact ⟨_, rfl⟩
      exact h₂ ⟨g z', h₁⟩
    rwa [i'.range_eq_compl_range_openComplement_ι, Set.notMem_compl_iff] at hp
  let ℓ := IsOpenImmersion.lift i'.openComplement.ι (pullback.fst e jV) hrange
  have hℓ : ℓ ≫ i'.openComplement.ι = pullback.fst e jV := IsOpenImmersion.lift_fac _ _ _
  have h₁ : IsZero (D((pullback.fst e jV)^*[A]).obj T) :=
    ((L((ℓ)^*[A])).map_isZero hT).of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory A _).symm.app T ≪≫
        (leftDerivedUpperStarComp A ℓ i'.openComplement.ι _ hℓ.symm).app T)
  have := isIso_openImmersionLowerShriekBaseChangeMap A hsq
  exact ((D((pullback.snd e jV)_!open[A])).map_isZero h₁).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory A jV).app _ ≪≫
      ((e)_!open[A].mapDerivedCategoryCompIso (jV)^*[A]).app T ≪≫
      (Functor.mapDerivedCategoryNatIso
        (asIso (openImmersionLowerShriekBaseChangeMap A hsq.toCommSq)).symm).app T ≪≫
      (((pullback.fst e jV)^*[A]).mapDerivedCategoryCompIso
        (pullback.snd e jV)_!open[A]).symm.app T)

/-- The restriction of supports along an open immersion `e : U ⟶ X`,
`ψ : Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'` (`AlgebraicGeometry.Etale.supportedRestriction`), is an
isomorphism. Both sides are supported on `Z'`, and the source has the universal property of the
target: a map `T ⟶ L'` out of an object `T` supported on `Z'` lifts uniquely to
`T ⟶ Le^* (Ri_! Ri^! L)`. Under `e_! ⊣ e^*` such lifts are lifts of `e_! T ⟶ L` through the
counit of `Ri_! ⊣ Ri^!`, which exist uniquely since `e_! T` is supported on `Z`
(`AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_openComplement_obj_openImmersionLowerShriek`).
-/
theorem isIso_supportedRestriction_of_isOpenImmersion (e : U ⟶ X) [IsOpenImmersion e]
    (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    IsIso (supportedRestriction Λ e i i' g hg L L' τ) := by
  set ψ := supportedRestriction Λ e i i' g hg L L' τ
  set ε := (rightDerivedUpperShriekAdjunction Λ i).counit.app L
  set ε' := (rightDerivedUpperShriekAdjunction Λ i').counit.app L'
  have hψ : ψ ≫ ε' = (L((e)^*[ModuleCat.{u + 1} Λ])).map ε ≫ τ.hom :=
    (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec
  let adj : D((e)_!open[ModuleCat.{u + 1} Λ]) ⊣ L((e)^*[ModuleCat.{u + 1} Λ]) :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) e).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) e).symm
  -- lifts of maps out of objects supported on `Z'` through `Le^* ε ≫ τ`
  have key : ∀ (T : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_ : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj T)) (β : T ⟶ L'),
      ∃! φ : T ⟶ (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj L)),
        φ ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map ε ≫ τ.hom = β := by
    intro T hT β
    have hT' := isZero_leftDerivedUpperStar_openComplement_obj_openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) e i i'
      g hg hT
    obtain ⟨b, hb, hb'⟩ := existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι hT' ((adj.homEquiv _ _).symm (β ≫ τ.inv))
    refine ⟨adj.homEquiv _ _ b, ?_, fun φ hφ ↦ ?_⟩
    · dsimp only
      rw [← Category.assoc, ← adj.homEquiv_naturality_right, hb]
      erw [Equiv.apply_symm_apply]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← Equiv.symm_apply_eq]
      refine hb' _ ?_
      dsimp only at hφ ⊢
      rw [← adj.homEquiv_naturality_right_symm]
      congr 1
      rw [← hφ, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- the source of `ψ` and its target are supported on `Z'`
  have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  have hS : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))))
          := by
    let k := i'.openComplement.ι ≫ e
    have hk : Set.range k.base ⊆ Set.range i.openComplement.ι.base := by
      rw [← compl_compl (Set.range i.openComplement.ι.base),
        ← i.range_eq_compl_range_openComplement_ι, Set.subset_compl_iff_disjoint_left,
        Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
      apply x.2
      rw [Scheme.range_snd_of_isPullback hg]
      exact ⟨z, hx.symm⟩
    exact (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ)
        i
      i.openComplement.ι hdisj k hk _).of_iso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i'.openComplement.ι e).app _).symm
  have hdisj' : Disjoint (Set.range i'.base) (Set.range i'.openComplement.ι.base) := by
    rw [i'.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  have hB : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![Λ]).obj L'))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i'
      i'.openComplement.ι hdisj' i'.openComplement.ι subset_rfl _
  obtain ⟨χ, hχ, -⟩ := key _ hB ε'
  refine ⟨χ, ?_, ?_⟩
  · refine (key _ hS _).unique ?_ (Category.id_comp _)
    rw [Category.assoc, hχ, hψ]
  · refine (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
      i'.range_eq_compl_range_openComplement_ι hB ε').unique ?_ (Category.id_comp _)
    erw [Category.assoc, hψ]
    exact hχ

end Etale

end AlgebraicGeometry
