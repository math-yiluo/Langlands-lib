/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Charts
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDuality
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# The exceptional inverse image and finite constant coefficients

Let `k` be a field, `Λ` a finite ring whose exponent is invertible on `k` and `N` a finitely
generated `Λ`-module. For a separated morphism `a : X ⟶ Spec k` of finite type, the canonical
map `θ_{a, N} : ω_X ⊗ᴸ La^* N_k ⟶ Ra^! N_k`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_constantSingle_of_field`). In other
words `Ra^!` commutes with tensoring by a constant finitely generated coefficient.

Following the blueprint (`lemma-change-coefficients-exceptional-inverse-image--1`), the statement is
local on `X` (`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_jointlySurjective`); on an
affine open, `a` factors as a closed immersion `i` into an affine space `𝔸ⁿ_k` followed by the
smooth projection `p`. The map `θ_p` is invertible by smooth duality
(`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`), and the tensor map of the
closed immersion at a constant coefficient is invertible by the closed-support triangle and the
projection formula for the complementary open immersion with a finitely generated constant
coefficient (`lemma-change-coefficients-exceptional-inverse-image--1`,
`isIso_rightDerivedUpperShriekTensorMap_constantSingle_of_isClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

instance smoothOfRelativeDimension_polyAffine_hom (k : Type u) [Field k] (n : ℕ) :
    SmoothOfRelativeDimension n (polyAffine k n).hom := by
  change SmoothOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n), CommRingCat.hom_ofHom]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
      (isStandardSmoothOfRelativeDimension_mvPolynomial k n))

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image--1`: for a closed immersion
`i : Z ⟶ Y` into a scheme of finite type over a field, `M ∈ D(Y_ét, Λ)` bounded above and a finitely
generated `Λ`-module `N`, the tensor map `Ri^! M ⊗ᴸ Li^* N_Y ⟶ Ri^!(M ⊗ᴸ N_Y)` is an isomorphism.

By the closed-support triangle it suffices that `Rj_* Lj^* M ⊗ᴸ N_Y` receives no maps from
objects supported on `Z`, `j` the open complement
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion`); by the
projection formula with a finitely generated constant coefficient
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`) it is
of the form `Rj_*(-)`. -/
theorem isIso_rightDerivedUpperShriekTensorMap_constantSingle_of_isClosedImmersion
    {Y Z : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (i : Z ⟶ Y) [IsClosedImmersion i] [HasCompactification i]
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ)
    [M.IsLE b] (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N] :
    IsIso (rightDerivedUpperShriekTensorMap i M (constantSingle (ModuleCat.{u + 1} Λ) Y N)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have := isIso_projectionMap_of_finite Λ i
  let j := (complOpens i).ι
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    change _ = (Set.range ⇑(complOpens i).ι)ᶜ
    rw [Scheme.Opens.range_ι]
    simp
  have : TopologicalSpace.NoetherianSpace (complOpens i).toScheme :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (j ≫ aY)
  have := ((j)^*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj M b
  have : ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M).IsLE b :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app M).symm b
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle Λ (j ≫ aY) aY j rfl d
    hd ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M) b N
  refine isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion i j hij M _ fun D n ↦ ?_
  exact subsingleton_hom_shift_of_iso_rightDerivedLowerStar i j
    (by rw [hij]; exact disjoint_compl_left)
    (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) j).app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)).app (constantSingle (ModuleCat.{u + 1} Λ) Y N)))
    D n

/-- For a closed immersion `i : Z ⟶ Y` into a scheme of finite type over a field and a finitely
generated `Λ`-module `N`, the canonical map `θ_{i, N} : ω_i ⊗ᴸ Li^* N_Y ⟶ Ri^! N_Y` is an
isomorphism. -/
theorem isIso_dualizingComplexTensorMap_constantSingle_of_isClosedImmersion {Y Z : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (i : Z ⟶ Y)
    [IsClosedImmersion i] [HasCompactification i] (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N] :
    IsIso (dualizingComplexTensorMap Λ i (constantSingle (ModuleCat.{u + 1} Λ) Y N)) := by
  rw [dualizingComplexTensorMap, isIso_lowerShriekRightAdjointUnitTensorMap_iff]
  exact isIso_rightDerivedUpperShriekTensorMap_constantSingle_of_isClosedImmersion Λ aY i
    (𝟙_ _) 0 N

/-- **Composition of the canonical maps at one object.** For `h = f ≫ g`, if `ω_g` is
invertible and `θ_{g, K}` and `θ_{f, Lg^* K}` are isomorphisms, then so is `θ_{h, K}`. -/
theorem isIso_dualizingComplexTensorMap_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h]
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : IsIso (dualizingComplexTensorMap Λ f ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)))
    (hω : DerivedCategory.isInvertible Λ Y (dualizingComplex Λ g))
    (hg : IsIso (dualizingComplexTensorMap Λ g K)) :
    IsIso (dualizingComplexTensorMap Λ h K) := by
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  exact isIso_lowerShriekRightAdjointUnitTensorMap_comp w (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ g) (rightDerivedUpperShriekAdjunction Λ h)
    (E f g h w) (hPF f g h w) (projectionMapAssociativity Λ f) K hf hg
    ((isInvertible_iff_exists_derivedTensor _).2 hω)

variable [HasInvertibleExponent Λ (Spec (.of k))]

/-- For an affine scheme `V` of finite type over a field `k` and a finitely generated
`Λ`-module `N`, the canonical map `θ_{a, N} : ω_V ⊗ᴸ La^* N_k ⟶ Ra^! N_k` is an isomorphism:
`a` is a closed immersion into some `𝔸ⁿ_k` followed by the smooth projection. -/
theorem isIso_dualizingComplexTensorMap_constantSingle_of_isAffine {V : Scheme.{u}} [IsAffine V]
    (a : V ⟶ Spec (.of k)) [LocallyOfFiniteType a] [HasCompactification a]
    (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N] :
    IsIso (dualizingComplexTensorMap Λ a
      (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) N)) := by
  have : IsAffine (Over.mk a).left := ‹IsAffine V›
  have : LocallyOfFiniteType (Over.mk a).hom := ‹LocallyOfFiniteType a›
  obtain ⟨n, ι, hι⟩ := exists_isClosedImmersion_polyAffine (Over.mk a)
  let p := (polyAffine k n).hom
  have w : ι.left ≫ p = a := Over.w ι
  have : IsProper ι.left := inferInstance
  have : HasCompactification ι.left := HasCompactification.of_isProper _
  have : HasCompactification p := inferInstance
  have : HasInvertibleExponent Λ (polyAffine k n).left := .of_hom p
  obtain ⟨L, hL₁, hL, ⟨e⟩, hθp⟩ := exists_dualizingComplex_iso_and_tensor Λ p n
  have hω : DerivedCategory.isInvertible Λ (polyAffine k n).left (dualizingComplex Λ p) := by
    have := hL₁
    exact DerivedCategory.isInvertible.of_iso e.symm
      (isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf L hL _)
  refine isIso_dualizingComplexTensorMap_comp_of_isIso Λ ι.left p a w _ ?_ hω (hθp _)
  have := isIso_rightDerivedUpperShriekTensorMap_constantSingle_of_isClosedImmersion Λ p ι.left
    (𝟙_ _) 0 N
  rw [dualizingComplexTensorMap, isIso_lowerShriekRightAdjointUnitTensorMap_iff]
  exact isIso_lowerShriekRightAdjointTensorMap_of_iso_right _
    (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) p N).symm

/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image--1`, in the form of the
coefficient comparison: for a morphism `a : X ⟶ Spec k` of finite type admitting a compactification,
`Λ` finite with exponent invertible on `k`, and a finitely generated `Λ`-module `N`, the canonical
map `θ_{a, N} : ω_X ⊗ᴸ La^* N_k ⟶ Ra^! N_k` is an isomorphism.

The statement is local on `X`
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_jointlySurjective`), and holds on
the affine opens of `X`
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_constantSingle_of_isAffine`). -/
theorem isIso_dualizingComplexTensorMap_constantSingle_of_field {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] [HasCompactification a]
    (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N] :
    IsIso (dualizingComplexTensorMap Λ a
      (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) N)) := by
  have hV (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hV
  have (x : X) : HasCompactification (V x).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have (x : X) : HasCompactification ((V x).ι ≫ a) :=
    ((HasCompactification.compactification a).precomp (V x).ι).hasCompactification
  refine isIso_dualizingComplexTensorMap_of_jointlySurjective Λ (fun x ↦ (V x).ι)
    (fun x ↦ ⟨x, ⟨x, hxV x⟩, rfl⟩) a
    (fun x ↦ isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ _)
    (fun x ↦ DerivedCategory.isInvertible.of_iso (dualizingComplexIsoOfEtale Λ _).symm
      (DerivedCategory.isInvertible_unit Λ _)) _ fun x ↦ ?_
  have : IsAffine (V x).toScheme := hV x
  exact isIso_dualizingComplexTensorMap_constantSingle_of_isAffine Λ ((V x).ι ≫ a) N

end Etale

end AlgebraicGeometry
