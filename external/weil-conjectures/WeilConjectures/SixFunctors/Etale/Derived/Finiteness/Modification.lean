/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ExtensionByZero
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Constructibility of direct images under a proper modification

Let `π : Y ⟶ X` be proper and an isomorphism over an open `j : U ⟶ X`, with closed complement
`i : Z ⟶ X`. This file proves:

- `AlgebraicGeometry.Etale.nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso`
  (`proposition-proper-direct-image-finite-coefficients`): `Rπ_*(j'_! G') ≅ j_! G` for a sheaf `G`
  on `U` with pullback `G'` to `U' = π⁻¹(U)`; that is, `π_* j'_! G' = j_! G` and
  `Rᵠπ_* j'_! G' = 0` for `q > 0`. This uses proper base change along `i`.
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_modification`
  (`proposition-proper-direct-image-finite-coefficients`): `𝒞(π ≫ f)` and `𝒞(i ≫ f)` imply `𝒞(f)`,
  by the open–closed short exact sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **A bounded below base change isomorphism, on the unbounded derived categories.** For a
commutative square `g' ≫ f = f' ≫ g` and a sheaf `E` on `X` at which the bounded below derived
base change map is an isomorphism (e.g. by proper or étale base change), the isomorphism
`g^* Rf_*(E[0]) ≅ Rf'_*((g'^* E)[0])` of the unbounded derived categories. -/
noncomputable def upperStarRightDerivedLowerStarSingleIso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app
      ((Plus.singleFunctor _ 0).obj E))] :
    D((g)^*[ModuleCat.{u + 1} Λ]).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj E)) ≅
      (R((f')_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((g')^*[ModuleCat.{u + 1} Λ].obj E)) :=
  D((g)^*[ModuleCat.{u + 1} Λ]).mapIso ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((Plus.singleFunctorιIso _ 0).app E).symm ≪≫
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _).symm) ≪≫
    (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.app _).symm ≪≫
    Plus.ι.mapIso (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app
      ((Plus.singleFunctor _ 0).obj E))) ≪≫
    Plus.ι.mapIso ((f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
      ((((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app E)) ≪≫
    (f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _ ≪≫
    (R((f')_*[ModuleCat.{u + 1} Λ])).mapIso
      ((Plus.singleFunctorιIso _ 0).app ((g')^*[ModuleCat.{u + 1} Λ].obj E))

variable [Finite Λ]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Extension by zero under a
proper modification.

Let `π : Y ⟶ X` be proper and `j : U ⟶ X` an open immersion such that `π⁻¹(U) ⟶ U` is an
isomorphism: here `j' : U' ⟶ Y`, `π' : U' ⟶ U` is a pullback square with `π'` an isomorphism.
For an étale sheaf `G` of `Λ`-modules on `U` with pullback `G' = π'^* G` to `U'`,
`Rπ_*(j'_! G') ≅ j_! G`, i.e. `π_* j'_! G' ≅ j_! G` and `Rᵠπ_* j'_! G' = 0` for `q > 0`. Here
`Λ` is a finite ring, as proper base change is used.

Write `M = Rπ_*(j'_! G')` and let `i` be the closed complement of `j`. By proper base change,
`i^* M` is the derived direct image of the restriction of `j'_! G'` to `π⁻¹(Z)`, which is zero;
so the counit `j_! j^* M ⟶ M` is an isomorphism, by the open–closed triangle. By étale base
change, `j^* M ≅ Rπ'_*(j'^* j'_! G') ≅ Rπ'_*(π'^* G) ≅ G`, `π'` being an isomorphism. -/
theorem nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso {X Y U U' : Scheme.{u}}
    (π : Y ⟶ X) [IsProper π] (j : U ⟶ X) [IsOpenImmersion j] (j' : U' ⟶ Y) [IsOpenImmersion j']
    (π' : U' ⟶ U) [IsIso π'] (sq : IsPullback j' π' π j)
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((R((π)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((j')_!open[ModuleCat.{u + 1} Λ].obj ((π')^*[ModuleCat.{u + 1} Λ].obj G))) ≅
      (singleFunctor _ 0).obj ((j)_!open[ModuleCat.{u + 1} Λ].obj G)) := by
  set A := ModuleCat.{u + 1} Λ
  set E := (j')_!open[A].obj ((π')^*[A].obj G)
  set M := (R((π)_*[A])).obj ((singleFunctor _ 0).obj E)
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  -- the closed complement of `j`
  let i := j.closedComplement
  have hij : Set.range i.base = (Set.range j.base)ᶜ := j.range_closedComplement
  -- `i^* M = 0` by proper base change
  have hZ : IsZero (D((i)^*[A]).obj M) := by
    let sqi := IsPullback.of_hasPullback π i
    have : IsIso (derivedBaseChangeMapPlus A sqi.toCommSq) := by
      rw [← baseChange_eq_derivedBaseChangeMapPlus]
      exact isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ sqi
    refine IsZero.of_iso ?_ (upperStarRightDerivedLowerStarSingleIso sqi.toCommSq E)
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    refine isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j' _ ?_ _
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h1 : π.base (j'.base a) = j.base (π'.base a) := by
      simpa using congrArg (fun φ ↦ φ.base a) sq.w
    have h2 : π.base ((pullback.fst π i).base b) = i.base ((pullback.snd π i).base b) := by
      simpa using congrArg (fun φ ↦ φ.base b) (pullback.condition (f := π) (g := i))
    have hmem : i.base ((pullback.snd π i).base b) ∈ Set.range i.base := ⟨_, rfl⟩
    rw [hij] at hmem
    exact hmem ⟨π'.base a, by rw [← h1, ← hb, h2]⟩
  -- hence the counit `j_! j^* M ⟶ M` is an isomorphism
  obtain ⟨w, hT⟩ := exists_distTriang_openClosed A j i hij M
  have hc : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M) :=
    (Triangle.isZero₃_iff_isIso₁ _ hT).1 (Functor.map_isZero _ hZ)
  -- `j^* M ≅ G[0]` by étale base change
  have : IsIso (derivedBaseChangeMapPlus A sq.toCommSq) :=
    isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  let e₁ : D((j)^*[A]).obj M ≅ (singleFunctor _ 0).obj G :=
    upperStarRightDerivedLowerStarSingleIso sq.toCommSq E ≪≫
      (R((π')_*[A])).mapIso ((singleFunctor _ 0).mapIso
        (asIso ((openImmersionLowerShriekUpperStarAdjunction A j').unit.app _)).symm) ≪≫
      (rightDerivedFunctorLowerStarIsoMapDerivedCategory _ π').app _ ≪≫
      (((π')_*[A]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (singleFunctor _ 0).mapIso (asIso ((upperStarLowerStarAdjunction A π').unit.app G)).symm
  exact ⟨(asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M)).symm ≪≫
    D((j)_!open[A]).mapIso e₁ ≪≫ (((j)_!open[A]).mapDerivedCategorySingleFunctor 0).app G⟩

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Proper modification transfer
without an amplitude claim.

Let `f : X ⟶ S` be a morphism and `π : Y ⟶ X` proper, an isomorphism over the open
`j : U ⟶ X` (that is, the projection `π⁻¹(U) ⟶ U` is an isomorphism), and let `i : Z ⟶ X` be a
closed immersion with range the complement of `U`. If `𝒞(π ≫ f)` and `𝒞(i ≫ f)` hold, then
`𝒞(f)` holds. Here `Λ` is a finite ring. The blueprint takes `f` proper and `Z` with its reduced
structure; neither is needed. The open immersion `j` is assumed quasi-compact (automatic for `X`
Noetherian, e.g. of finite type over a field as in the blueprint), so that extension by zero
along its base change preserves constructibility.

The open–closed sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0` gives a distinguished triangle;
`Rf_*(j_! j^* F) ≅ R(π ≫ f)_*(j'_! G')` by
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso` and
`Rf_*(i_* i^* F) ≅ R(i ≫ f)_*(i^* F)` since `i_*` is exact, and constructible homology is a
triangulated property. -/
theorem HasConstructibleDirectImages.of_modification {X Y Z U S : Scheme.{u}} (f : X ⟶ S)
    (π : Y ⟶ X) [IsProper π] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X)
    [IsClosedImmersion i] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hπ : IsIso (pullback.snd π j)) (hπf : HasConstructibleDirectImages Λ (π ≫ f))
    (hif : HasConstructibleDirectImages Λ (i ≫ f)) :
    HasConstructibleDirectImages Λ f := by
  intro F hF
  let A := ModuleCat.{u + 1} Λ
  let P := (Etale.DerivedCategory.constructibleHomology A S).inverseImage (R((f)_*[A]))
  have hT := (shortExact_openClosedShortComplex A j i F hij).singleTriangle_distinguished
  have h₁ : P ((singleFunctor _ 0).obj ((j)_!open[A].obj ((j)^*[A].obj F))) := by
    obtain ⟨e⟩ := nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso π j
      (pullback.fst π j) (pullback.snd π j) (IsPullback.of_hasPullback π j) ((j)^*[A].obj F)
    have : IsConstructibleSheaf ((j)^*[A].obj F) := IsConstructibleSheaf.upperStar j F
    have : IsConstructibleSheaf ((pullback.snd π j)^*[A].obj ((j)^*[A].obj F)) :=
      IsConstructibleSheaf.upperStar _ _
    have hE : IsConstructibleSheaf ((pullback.fst π j)_!open[A].obj
        ((pullback.snd π j)^*[A].obj ((j)^*[A].obj F))) :=
      IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact _ _
    exact (Etale.DerivedCategory.constructibleHomology A S).prop_of_iso
      (((R((f)_*[A])).mapIso e.symm ≪≫ (rightDerivedLowerStarComp _ π f).app _).symm)
      (hπf _ hE)
  have h₃ : P ((singleFunctor _ 0).obj ((i)_*[A].obj ((i)^*[A].obj F))) := by
    have : IsConstructibleSheaf ((i)^*[A].obj F) := IsConstructibleSheaf.upperStar i F
    exact (Etale.DerivedCategory.constructibleHomology A S).prop_of_iso
      (rightDerivedLowerStarSingleLowerStarIso i f _).symm (hif _ this)
  exact P.ext_of_isTriangulatedClosed₂ _ hT h₁ h₃

end Etale

end AlgebraicGeometry
