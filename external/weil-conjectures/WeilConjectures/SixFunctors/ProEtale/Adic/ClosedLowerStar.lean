/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# The direct image along a closed immersion on `Dᵇc(-, ℚ̄_ℓ)`

Let `i : Z ⟶ X` be a closed immersion into a locally noetherian scheme. We show, without the
finiteness theorem for `ℓ`-adic direct images, that `Ri_*` carries `Dᵇc(Z, ℚ̄_ℓ)` into
`Dᵇc(X, ℚ̄_ℓ)`:

* the open complement `j` of `i` is quasi-compact, `X` being locally noetherian, so `i_*` is exact
  (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isClosedImmersion`) and
  `Ri_*` is `i_*` applied termwise;
* `i_*` of a constructible `ℓ`-adic sheaf is constructible
  (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.adicLowerStar_of_isClosedImmersion`): near a
  point, on an affine open `V`, the sheaf `i_* F` restricts to `F` on `Z ∩ V` (the counit
  `i^* i_* ⟶ 𝟭` being invertible) and to `0` on the complement `U ∩ V`.

This gives the functor `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedLowerStar`), and we prove the
stage `ℚ̄_ℓ` of blueprint `lemma-local-cohomology-right-adjoint--1` for it: it is fully faithful
(`AlgebraicGeometry.ProEtale.fullyFaithfulBoundedConstructibleAdicClosedLowerStar`), and for any
right adjoint the unit is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_unit_boundedConstructibleAdicClosedLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The open complement of the range of a closed immersion. -/
noncomputable abbrev closedImmersionComplement : X.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

lemma isCompl_range_closedImmersionComplement :
    IsCompl (Set.range i.base) (Set.range (closedImmersionComplement i).ι.base) := by
  rw [Scheme.Opens.range_ι]
  exact isCompl_compl

variable [IsLocallyNoetherian X]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--4` for `ℓ`-adic sheaves over
a locally noetherian scheme: the pushforward along a closed immersion is exact, its open complement
being quasi-compact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isCompl`). -/
theorem preservesFiniteColimits_adicLowerStar_of_isClosedImmersion :
    PreservesFiniteColimits (i)_*ᵃ[l] :=
  preservesFiniteColimits_adicLowerStar_of_isCompl i (closedImmersionComplement i).ι
    (isCompl_range_closedImmersionComplement i)

/-- **The pushforward of a constructible `ℓ`-adic sheaf along a closed immersion is
constructible** (over a locally noetherian target). Let `V` be an affine open neighbourhood of a
point of `X`. On `Z ∩ V` the restriction of `i_* F` is the restriction of `F`, the counit
`i^* i_* ⟶ 𝟭` being an isomorphism, and `F` is stratified lisse there, `Z ∩ V` being affine. On
the quasi-compact open complement `U ∩ V` it vanishes. -/
theorem IsAdicConstructibleSheaf.adicLowerStar_of_isClosedImmersion {F : AdicSheaf l Z}
    (hF : IsAdicConstructibleSheaf F) : IsAdicConstructibleSheaf ((i)_*ᵃ[l].obj F) := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ : ∃ V : X.Opens, V ∈ X.affineOpens ∧ x ∈ V ∧ V ≤ ⊤ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨V, V.ι, inferInstance, by simpa using hxV, ?_⟩
  set G := (i)_*ᵃ[l].obj F
  have : IsAffine V := hV
  have : CompactSpace ↥(pullback i V.ι) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd i V.ι)
  have : QuasiSeparatedSpace ↥(pullback i V.ι) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd i V.ι)
  let j := (closedImmersionComplement i).ι
  have hij := isCompl_range_closedImmersionComplement i
  refine IsAdicStratifiedLisseSheaf.of_isCompl (pullback.snd j V.ι) (pullback.snd i V.ι) ?_ ?_ ?_
  · rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← hij.compl_eq,
      Set.preimage_compl]
    exact isCompl_compl.symm
  · -- On `U ∩ V` the sheaf `i_* F` vanishes.
    refine (IsAdicLisseSheaf.of_isZero ?_).isAdicStratifiedLisseSheaf
    refine (isZero_adicUpperStar_obj_adicLowerStar_obj i (pullback.snd j V.ι ≫ V.ι) ?_ F).of_iso
      ((adicUpperStarComp l _ _).app G).symm
    rw [← pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact hij.disjoint.mono_right (Set.image_subset_range _ _)
  · -- On `Z ∩ V` the sheaf `i_* F` restricts to `F`.
    exact (hF.upperStar (pullback.fst i V.ι)).isAdicStratifiedLisseSheaf.of_iso
      (((pullback.fst i V.ι)^*ᵃ[l].mapIso
          (asIso ((adicUpperStarLowerStarAdjunction l i).counit.app F))).symm ≪≫
        (adicUpperStarCompIso l pullback.condition).app G)

/-- `Ri_*` along a closed immersion into a locally noetherian scheme carries `Dᵇc(Z, ℚ̄_ℓ)` into
`Dᵇc(X, ℚ̄_ℓ)`: `i_*` is exact, so `Ri_* K ≅ D(i_*) K` has cohomology sheaves `i_* 𝓗ⁿ(K)`, which
are constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.adicLowerStar_of_isClosedImmersion`).
This does not use the finiteness theorem for `ℓ`-adic direct images. -/
theorem boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj_of_isClosedImmersion
    {K : DerivedCategory (AdicSheaf l Z)}
    (hK : DerivedCategory.boundedConstructibleAdic l Z K) :
    DerivedCategory.boundedConstructibleAdic l X ((i)_*ᵃ[l].rightDerivedFunctor.obj K) := by
  have := preservesFiniteColimits_adicLowerStar_of_isClosedImmersion (l := l) i
  refine (DerivedCategory.boundedConstructibleAdic l X).prop_of_iso
    (((i)_*ᵃ[l].rightDerivedFunctorIsoMapDerivedCategory).app K).symm
    ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦ ?_⟩
  exact (adicConstructibleSheaf l X).prop_of_iso
    ((((i)_*ᵃ[l]).mapDerivedCategoryHomologyFunctorIso n).app K)
    ((hK.2 n).adicLowerStar_of_isClosedImmersion i)

variable (l) in
/-- The direct image `i_* = Ri_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion into a
locally noetherian scheme, the restriction of `Ri_*`
(`boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj_of_isClosedImmersion`).
-/
noncomputable abbrev boundedConstructibleAdicClosedLowerStar :
    (DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  (DerivedCategory.boundedConstructibleAdic l Z).liftFullSubcategory _
    (i)_*ᵃ[l].rightDerivedFunctor
    fun _ hK ↦ boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj_of_isClosedImmersion
      i hK

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, stage `ℚ̄_ℓ`: the direct image
`i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion is fully faithful, being the
restriction of the fully faithful `Ri_*`
(`AlgebraicGeometry.ProEtale.full_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar`). -/
noncomputable def fullyFaithfulBoundedConstructibleAdicClosedLowerStar :
    (boundedConstructibleAdicClosedLowerStar l i).FullyFaithful :=
  .ofFullyFaithful _

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the stage `ℚ̄_ℓ`: for any right
adjoint `Ri^!` of `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`, the unit `Q ⟶ Ri^! i_* Q` is an
isomorphism, `i_*` being fully faithful
(`AlgebraicGeometry.ProEtale.fullyFaithfulBoundedConstructibleAdicClosedLowerStar`). -/
theorem isIso_unit_boundedConstructibleAdicClosedLowerStar
    {G : (DerivedCategory.boundedConstructibleAdic l X).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory}
    (adj : boundedConstructibleAdicClosedLowerStar l i ⊣ G) : IsIso adj.unit :=
  have := (fullyFaithfulBoundedConstructibleAdicClosedLowerStar (l := l) i).full
  have := (fullyFaithfulBoundedConstructibleAdicClosedLowerStar (l := l) i).faithful
  Adjunction.unit_isIso_of_L_fully_faithful adj

end AlgebraicGeometry.ProEtale
