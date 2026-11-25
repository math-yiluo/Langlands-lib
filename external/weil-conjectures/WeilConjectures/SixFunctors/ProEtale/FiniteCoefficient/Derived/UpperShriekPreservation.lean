/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.PurityPreservation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!
# The typing of the pro-étale exceptional inverse image at the finite stages

Let `k` be a field, `Y` a `k`-scheme of finite type and `f : X ⟶ Y` separated of finite type.
At a finite coefficient stage `Λ` (a finite ring whose exponent is invertible in `k`), the
pro-étale exceptional inverse image `Rf^! = ν_X^* ∘ f^× ∘ Rν_{Y,*}`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`, blueprint
`theorem-f-shriek-finite-coefficients`) carries `D_c^[a, b](Y_proét, Λ)` into
`D_c^[a - 2D, b + 2 dim Y + 1](X_proét, Λ)` and bounded constructible complexes of Tor amplitude
in `[a, b]` to bounded constructible complexes of Tor amplitude in `[a - 2D, b + 2 dim Y + 1]`,
where `D` is the maximal embedding dimension of a finite family of affine charts
`U ↪ 𝔸^{d_U}_V` of `f`. The constant `D` does not depend on the coefficient stage `Λ`
(`AlgebraicGeometry.ProEtale.exists_preservationClauses`).

Every bounded constructible pro-étale complex is `ν^* G` for a bounded constructible étale
complex `G`, and `Rf^! ν^* G ≅ ν^* f^× G`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso`), since the unit
`G ⟶ Rν_* ν^* G` is invertible on bounded below complexes. So this is the étale statement
`AlgebraicGeometry.Etale.preservationClauses_of_charts_of_topologicalKrullDim_le`
(`theorem-f-shriek-finite-coefficients--1`) transported along `ν^*`, which preserves and detects
homology concentration and Tor amplitude.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- For a bounded below complex `G` of étale sheaves, the pro-étale exceptional inverse image of
`ν^* G` is `ν^* f^× G`: the unit `G ⟶ Rν_* ν^* G` of the comparison adjunction is invertible
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`). -/
noncomputable def rightDerivedUpperShriekMapDerivedCategoryObjIso [Finite Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : _root_.DerivedCategory.TStructure.t.plus G) :
    (R(f)^![Λ]).obj (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj G) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
        ((Etale.rightDerivedUpperShriek Λ f).obj G) :=
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) Y G hG
  D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso ((Etale.rightDerivedUpperShriek _ f).mapIso
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app G)).symm)

/-- A separated finite-type morphism `f : X ⟶ Y` over a finite-type `k`-scheme is covered by
finitely many affine charts: affine opens `Uᵢ ⊆ X` mapping to affine opens `Vᵢ ⊆ Y`, with closed
immersions `cᵢ : Uᵢ ⟶ 𝔸^{nᵢ}_{Vᵢ}` over `Vᵢ`. These do not depend on any coefficients. -/
lemma exists_affineCharts {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ (m : ℕ) (U : Fin m → X.affineOpens) (_ : ∀ x, ∃ i, x ∈ (U i : X.Opens))
      (V : Fin m → Y.affineOpens) (n : Fin m → ℕ)
      (c : ∀ i, ((U i : X.Opens) : Scheme.{u}) ⟶ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens))),
      (∀ i, IsClosedImmersion (c i)) ∧
      ∀ i, c i ≫ 𝔸(ULift.{u} (Fin (n i)); (V i : Y.Opens)) ↘ _ ≫ (V i : Y.Opens).ι =
        (U i : X.Opens).ι ≫ f := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  -- affine charts `U ⊆ f⁻¹ V`
  have hchart (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hchart
  -- closed immersions of the charts into affine spaces over the `V`
  have hemb (x : X) : ∃ (n : ℕ) (c : ((U x : X.Opens) : Scheme.{u}) ⟶
      𝔸(ULift.{u} (Fin n); (V x : Y.Opens))), IsClosedImmersion c ∧
      c ≫ 𝔸(ULift.{u} (Fin n); (V x : Y.Opens)) ↘ _ ≫ (V x : Y.Opens).ι =
        (U x : X.Opens).ι ≫ f := by
    have hr : Set.range ((U x : X.Opens).ι ≫ f).base ⊆ Set.range (V x : Y.Opens).ι.base := by
      rintro - ⟨y, rfl⟩
      simpa using hUV x y.2
    let g := IsOpenImmersion.lift (V x : Y.Opens).ι ((U x : X.Opens).ι ≫ f) hr
    have hg : g ≫ (V x : Y.Opens).ι = (U x : X.Opens).ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have : LocallyOfFiniteType (g ≫ (V x : Y.Opens).ι) := by rw [hg]; infer_instance
    have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (V x : Y.Opens).ι
    obtain ⟨n, c, hc, hcl⟩ := exists_isClosedImmersion_affineSpace_of_isAffine g
    exact ⟨n, c, hcl, by rw [← Category.assoc, hc, hg]⟩
  choose n c hc hcf using hemb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x : X.Opens).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  let pt : Fin t.card → X := fun i ↦ (t.equivFin.symm i).1
  refine ⟨t.card, fun i ↦ U (pt i), fun x ↦ ?_, fun i ↦ V (pt i), fun i ↦ n (pt i),
    fun i ↦ c (pt i), fun i ↦ hc (pt i), fun i ↦ hcf (pt i)⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa [pt] using hx⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients` (the typing of `Rf_n^!` at the finite
stages): Preservation of bounded constructibility and of finite Tor amplitude by the pro-étale
exceptional inverse image, with bounds independent of the coefficient stage.

Let `k` be a field, `Y` a `k`-scheme of finite type and `f : X ⟶ Y` separated of finite type
(compactifiable and quasi-compact). There is `D : ℕ` (the maximal embedding dimension of a
finite family of affine charts `U ↪ 𝔸^{d_U}_V` of `f`) such that for every finite coefficient
ring `Λ` whose exponent is invertible in `k` (in the blueprint `Λ = A_{E,n} = 𝒪_E / ϖ_Eⁿ`, for
every `n`) and every `d_Y ≥ dim Y`, the pro-étale exceptional inverse image
`Rf^! = ν_X^* ∘ f^× ∘ Rν_{Y,*}` (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`)

1. carries `D_c^[a, b](Y_proét, Λ)` into `D_c^[a - 2D, b + 2d_Y + 1](X_proét, Λ)`; in particular
   it restricts to `Dᵇc(Y_proét, Λ) ⥤ Dᵇc(X_proét, Λ)`;
2. carries bounded constructible complexes of Tor amplitude in `[a, b]` to bounded constructible
   complexes of Tor amplitude in `[a - 2D, b + 2d_Y + 1]`.

Bounded constructible pro-étale complexes are those of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`, which is the blueprint's
notion at the finite stages by `theorem-comparison-constructible-sheaves`). Writing `L ≅ ν^* G`, we
have `Rf^! L ≅ ν^* f^× G`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso`), and the étale
statement is `AlgebraicGeometry.Etale.preservationClauses_of_charts_of_topologicalKrullDim_le`
(`theorem-f-shriek-finite-coefficients--1`) for charts chosen once and for all
(`AlgebraicGeometry.ProEtale.exists_affineCharts`); `ν^*` preserves and detects homology
concentration and Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`). -/
theorem exists_preservationClauses {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ D : ℕ, ∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))]
      (dY : ℕ), topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) →
    (∀ (a b : ℤ)
      (L : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ))),
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
          ((R(f)^![Λ]).obj L)) ∧
    ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
            ((R(f)^![Λ]).obj K) ∧
          DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
            ((R(f)^![Λ]).obj K) := by
  obtain ⟨m, U, hU, V, n, c, hcl, hc⟩ := exists_affineCharts aY f
  refine ⟨Finset.univ.sup n, fun Λ _ _ _ dY hY ↦ ?_⟩
  have : ∀ i, IsClosedImmersion (c i) := hcl
  obtain ⟨h₁, h₂⟩ := Etale.preservationClauses_of_charts_of_topologicalKrullDim_le Λ aY f dY hY
    U hU V n c hc _ fun i ↦ Finset.le_sup (Finset.mem_univ i)
  refine ⟨fun a b L hL ↦ ?_, fun a b K hK hta ↦ ?_⟩
  · obtain ⟨G, hG, ⟨e⟩⟩ := hL.1
    have hGab : _root_.DerivedCategory.homologyConcentratedIn a b G :=
      Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
        ν^*(Y)[ModuleCat.{u + 1} Λ] (ObjectProperty.prop_of_iso _ e.symm hL.2)
    have h := h₁ a b G ⟨hG, hGab⟩
    let E := (R(f)^![Λ]).mapIso e.symm ≪≫
      rightDerivedUpperShriekMapDerivedCategoryObjIso f G hG.1.1
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso E.symm
        (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj h.1),
      ObjectProperty.prop_of_iso _ E.symm
        (Functor.homologyConcentratedIn_mapDerivedCategory_obj _ h.2)⟩
  · obtain ⟨G, hG, ⟨e⟩⟩ := hK
    have hGt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b G :=
      (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
        ((DerivedCategory.torAmplitudeIn _ Y a b).prop_of_iso e.symm hta)
    have h := h₂ a b G hG hGt
    let E := (R(f)^![Λ]).mapIso e.symm ≪≫
      rightDerivedUpperShriekMapDerivedCategoryObjIso f G hG.1.1
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso E.symm
        (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj h.1),
      (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso E.symm
        ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ _).2 h.2)⟩

end ProEtale

end AlgebraicGeometry
