/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# The closed-support triangle on the pro-étale site

Let `i : Z ⟶ X` be a closed immersion with quasi-compact complementary open immersion
`j : U ⟶ X` (for instance, `X` noetherian), and let `R` be a ring. On the unbounded derived
categories of pro-étale sheaves of `R`-modules, the direct image `Ri_*` has the right adjoint
`Ri^!` of `AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`, and for
every `K` the counit of `Ri_* ⊣ Ri^!` and the unit of `Lj^* ⊣ Rj_*` extend to a distinguished
triangle

`Ri_* Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶ (Ri_* Ri^! K)[1]`

(blueprint `lemma-local-cohomology-right-adjoint--2`). No constructibility is involved.

The proof is formal from the following sheaf-level facts:

- `j^* i_* = 0` (`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint`), so that
  `Hom((Ri_* M)[n], Rj_* N) = 0`;
- `j^* j_* ≅ 𝟭`, so that `Rj_*` is fully faithful and `Lj^*` inverts the unit of
  `Lj^* ⊣ Rj_*`;
- a sheaf killed by `j^*` is in the essential image of the exact functor `i_*`
  (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`), so that
  a complex killed by `Lj^*` is in the essential image of `Ri_*`.

Complete the unit `K ⟶ Rj_* Lj^* K` to a distinguished triangle `K' ⟶ K ⟶ Rj_* Lj^* K ⟶`;
then `Lj^* K' = 0`, so `K'` lies in the essential image of `Ri_*`, and
`CategoryTheory.Pretriangulated.exists_distTriang_counit_of_subsingleton` identifies `K'` with
`Ri_* Ri^! K`.

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar`:
  `D(j^*) Ri_* = 0`.
- `AlgebraicGeometry.ProEtale.subsingleton_hom_shift_rightDerivedFunctor_lowerStar`:
  `Hom((Ri_* M)[n], Rj_* N) = 0`.
- `AlgebraicGeometry.ProEtale.exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit`:
  the closed-support triangle (blueprint `lemma-local-cohomology-right-adjoint--2`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [CommRing R] {Z U X : Scheme.{u}}

variable (R) in
/-- The adjunction `D(g^*) ⊣ Rg_*` on unbounded derived categories of pro-étale sheaves of
modules: `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction` transported along the
identification `Lg^* ≅ D(g^*)` of the derived functor of the exact functor `g^*`. -/
noncomputable def mapDerivedUpperStarLowerStarAdjunction {Y : Scheme.{u}} (g : Y ⟶ X) :
    D((g)^*[ModuleCat.{u + 1} R]) ⊣ R((g)_*[ModuleCat.{u + 1} R]) :=
  (derivedUpperStarLowerStarAdjunction _ g).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory _ g)

/-- For an open immersion `j`, the counit `D(j^*) Rj_* ⟶ 𝟭` is an isomorphism, i.e. `Rj_*` is
fully faithful: `D(j_!) ⊣ D(j^*) ⊣ Rj_*` is an adjoint triple whose first unit is invertible,
since `j^* j_! ≅ 𝟭` on sheaves
(`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekAdjunction_unit`). -/
instance isIso_mapDerivedUpperStarLowerStarAdjunction_counit (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (mapDerivedUpperStarLowerStarAdjunction R j).counit :=
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction _ j).unit_isIso_of_L_fully_faithful
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨derivedOpenImmersionLowerShriekUpperStarAdjunction _ j,
      mapDerivedUpperStarLowerStarAdjunction R j⟩).1 inferInstance

/-- For an open immersion `j`, the pullback `Lj^*` inverts the unit `K ⟶ Rj_* Lj^* K` of
`Lj^* ⊣ Rj_*`: by a triangle identity, `Lj^*` of the unit is inverse to the counit at `Lj^* K`,
which is an isomorphism (`Rj_*` is fully faithful). -/
lemma isIso_leftDerivedUpperStar_map_derivedUpperStarLowerStarAdjunction_unit_app (j : U ⟶ X)
    [IsOpenImmersion j] (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    IsIso ((L((j)^*[ModuleCat.{u + 1} R])).map
      ((derivedUpperStarLowerStarAdjunction _ j).unit.app K)) := by
  set adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j
  have hff := (mapDerivedUpperStarLowerStarAdjunction R j).fullyFaithfulROfIsIsoCounit
  have := hff.full
  have := hff.faithful
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  have : IsIso ((L((j)^*[ModuleCat.{u + 1} R])).map (adj.unit.app K) ≫
      adj.counit.app ((L((j)^*[ModuleCat.{u + 1} R])).obj K)) := by
    rw [adj.left_triangle_components K]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app _)

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

omit [IsClosedImmersion i] in
/-- `D(j^*) D(i_*) = 0` when the ranges of `i` and the open immersion `j` are disjoint: on
homology sheaves this is `j^* i_* = 0`
(`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint`). -/
lemma isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_lowerStar
    [PreservesFiniteLimits ((i)_*[ModuleCat.{u + 1} R])]
    [PreservesFiniteColimits ((i)_*[ModuleCat.{u + 1} R])]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj (D((i)_*[ModuleCat.{u + 1} R]).obj M)) :=
  (Functor.isZero_mapDerivedCategory_obj ((i)_*[ModuleCat.{u + 1} R] ⋙
    (j)^*[ModuleCat.{u + 1} R]) M fun _ ↦ isZero_upperStar_lowerStar_of_disjoint _ i j hij
      _).of_iso ((((i)_*[ModuleCat.{u + 1} R]).mapDerivedCategoryCompIso _).app M)

/-- `D(j^*) Ri_* = 0` for a closed immersion `i` whose range is the complement of the range of
the quasi-compact open immersion `j`: `Ri_*` is `D(i_*)`, `i_*` being exact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`). -/
lemma isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj (R((i)_*[ModuleCat.{u + 1} R]).obj M)) :=
  have := preservesFiniteColimits_lowerStar_of_isCompl (R := R) i j hij
  (isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_lowerStar i j hij.disjoint
    M).of_iso (D((j)^*[ModuleCat.{u + 1} R]).mapIso
      (((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctorIsoMapDerivedCategory.app M))

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pro-etale closed-support triangle before
constructible restriction (the vanishing used in the proof).

For a closed immersion `i` whose range is the complement of the range of the quasi-compact open
immersion `j`, `Hom((Ri_* M)[n], Rj_* N) = 0` for all `M ∈ D(Z_proét)`, `N ∈ D(U_proét)` and
`n ∈ ℤ`: by `D(j^*) ⊣ Rj_*` it is `Hom(D(j^*)((Ri_* M)[n]), N)`, and `D(j^*) Ri_* = 0`
(`AlgebraicGeometry.ProEtale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar`).
-/
theorem subsingleton_hom_shift_rightDerivedFunctor_lowerStar [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R)))
    (N : DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))) (n : ℤ) :
    Subsingleton ((R((i)_*[ModuleCat.{u + 1} R]).obj M)⟦n⟧ ⟶
      R((j)_*[ModuleCat.{u + 1} R]).obj N) := by
  have hz : IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj
      ((R((i)_*[ModuleCat.{u + 1} R]).obj M)⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero
      (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar i j hij M)).of_iso
      ((D((j)^*[ModuleCat.{u + 1} R]).commShiftIso n).app _)
  have : Subsingleton (D((j)^*[ModuleCat.{u + 1} R]).obj
      ((R((i)_*[ModuleCat.{u + 1} R]).obj M)⟦n⟧) ⟶ N) :=
    ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
  exact ((mapDerivedUpperStarLowerStarAdjunction R j).homEquiv _ _).symm.subsingleton

/-- An object `E` of `D(X_proét)` with `D(i^*) E = 0` and `D(j^*) E = 0` is zero, for a closed
immersion `i` whose range is the complement of the range of the quasi-compact open immersion
`j`: on homology sheaves this is
`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`. -/
theorem isZero_of_isZero_mapDerivedCategoryUpperStar_of_isCompl [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {E : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hi : IsZero (D((i)^*[ModuleCat.{u + 1} R]).obj E))
    (hj : IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj E)) : IsZero E :=
  (DerivedCategory.isZero_iff _).2 fun n ↦ isZero_of_isZero_upperStar_of_isCompl i j hij _
    (((DerivedCategory.isZero_iff _).1 hi n).of_iso
      (((i)^*[ModuleCat.{u + 1} R].mapDerivedCategoryHomologyFunctorIso n).app E))
    (((DerivedCategory.isZero_iff _).1 hj n).of_iso
      (((j)^*[ModuleCat.{u + 1} R].mapDerivedCategoryHomologyFunctorIso n).app E))

/-- An object `E` of `D(X_proét)` with `D(j^*) E = 0` lies in the essential image of `Ri_*`,
for a closed immersion `i` whose range is the complement of the range of the quasi-compact open
immersion `j`.

The unit `E ⟶ D(i_*) D(i^*) E` of the adjunction `D(i^*) ⊣ D(i_*)` (both functors are exact) is
an isomorphism: its cone is killed by `D(i^*)`, which inverts the unit because the counit
`i^* i_* ⟶ 𝟭` is invertible, and by `D(j^*)`, as both ends of the unit are killed by `D(j^*)`;
so the cone vanishes (`isZero_of_isZero_mapDerivedCategoryUpperStar_of_isCompl`). -/
theorem rightDerivedFunctor_lowerStar_essImage_of_isZero [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {E : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hE : IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj E)) :
    (R((i)_*[ModuleCat.{u + 1} R])).essImage E := by
  have := preservesFiniteColimits_lowerStar_of_isCompl (R := R) i j hij
  set adj := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).mapDerivedCategoryAdjunction
  have : IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit :=
    isIso_upperStarLowerStarAdjunction_counit (ModuleCat.{u + 1} R) i
  have : IsIso adj.counit := Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  obtain ⟨W, v, w, h₁⟩ := distinguished_cocone_triangle (adj.unit.app E)
  have hiu : IsIso (D((i)^*[ModuleCat.{u + 1} R]).map (adj.unit.app E)) :=
    have := IsIso.id (D((i)^*[ModuleCat.{u + 1} R]).obj E)
    IsIso.of_isIso_fac_right (adj.left_triangle_components E)
  have hju : IsIso (D((j)^*[ModuleCat.{u + 1} R]).map (adj.unit.app E)) :=
    isIso_of_source_target_iso_zero _ hE.isoZero
      (isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_lowerStar i j hij.disjoint
        _).isoZero
  have hW : IsZero W := isZero_of_isZero_mapDerivedCategoryUpperStar_of_isCompl i j hij
    ((Triangle.isZero₃_iff_isIso₁ _
      (D((i)^*[ModuleCat.{u + 1} R]).map_distinguished _ h₁)).2 hiu)
    ((Triangle.isZero₃_iff_isIso₁ _
      (D((j)^*[ModuleCat.{u + 1} R]).map_distinguished _ h₁)).2 hju)
  have : IsIso (adj.unit.app E) := (Triangle.isZero₃_iff_isIso₁ _ h₁).1 hW
  exact ⟨D((i)^*[ModuleCat.{u + 1} R]).obj E,
    ⟨((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (asIso (adj.unit.app E)).symm⟩⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pro-etale closed-support triangle before
constructible restriction

Let `i : Z ⟶ X` be a closed immersion whose range is the complement of the range of the
quasi-compact open immersion `j : U ⟶ X` (for instance, `X` noetherian), and let
`Ri^!` be the right adjoint of the direct image `Ri_*` on the unbounded derived categories of
pro-étale sheaves of `R`-modules
(`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`). For every `K`, the
counit of `Ri_* ⊣ Ri^!` and the unit of `Lj^* ⊣ Rj_*` extend to a distinguished triangle

```
  Ri_* Ri^! K --ε_K--> K --η_K--> Rj_* Lj^* K --w--> (Ri_* Ri^! K)[1].
```

No constructibility of `Ri^! K` is involved.

Complete `η_K` to a distinguished triangle `K' ⟶ K ⟶ Rj_* Lj^* K ⟶ K'[1]`. As `Lj^*` inverts
`η_K` (`Rj_*` is fully faithful), `Lj^* K' = 0`, so `K'` is in the essential image of `Ri_*`
(`AlgebraicGeometry.ProEtale.rightDerivedFunctor_lowerStar_essImage_of_isZero`). Since `Ri_*`
is fully faithful and `Hom((Ri_* M)[n], Rj_* Lj^* K) = 0`
(`AlgebraicGeometry.ProEtale.subsingleton_hom_shift_rightDerivedFunctor_lowerStar`), the
counit `ε_K` identifies `Ri_* Ri^! K` with `K'`
(`CategoryTheory.Pretriangulated.exists_distTriang_counit_of_subsingleton`). -/
theorem exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    ∃ w, Triangle.mk ((derivedLowerStarClosedUpperShriekAdjunction i j hij).counit.app K)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit.app K) w ∈
        distTriang _ := by
  obtain ⟨K', a, δ, hT⟩ := distinguished_cocone_triangle₁
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit.app K)
  have hK' : IsZero (D((j)^*[ModuleCat.{u + 1} R]).obj K') := by
    have := isIso_leftDerivedUpperStar_map_derivedUpperStarLowerStarAdjunction_unit_app (R := R)
      j K
    have : IsIso (D((j)^*[ModuleCat.{u + 1} R]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit.app K)) :=
      (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ j) _).1 this
    exact (Triangle.isZero₁_iff_isIso₂ _ (D((j)^*[ModuleCat.{u + 1} R]).map_distinguished _
      hT)).2 this
  have hff : (R((i)_*[ModuleCat.{u + 1} R])).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  exact exists_distTriang_counit_of_subsingleton
    (derivedLowerStarClosedUpperShriekAdjunction i j hij) hff hT
    (fun M n ↦ subsingleton_hom_shift_rightDerivedFunctor_lowerStar i j hij M _ n)
    (rightDerivedFunctor_lowerStar_essImage_of_isZero i j hij hK')

/-- The *closed-support triangle* of `K` with connecting map `w`:

```
  Ri_* Ri^! K --ε_K--> K --η_K--> Rj_* Lj^* K --w--> (Ri_* Ri^! K)[1]
```

where `ε` is the counit of `Ri_* ⊣ Ri^!`
(`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`) and `η` the unit of
`Lj^* ⊣ Rj_*`. -/
noncomputable abbrev closedSupportTriangle [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)))
    (w : R((j)_*[ModuleCat.{u + 1} R]).obj (L((j)^*[ModuleCat.{u + 1} R]).obj K) ⟶
      (R((i)_*[ModuleCat.{u + 1} R]).obj
        ((closedUpperShriek (ModuleCat.{u + 1} R) i j).rightDerivedFunctor.obj K))⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :=
  Triangle.mk ((derivedLowerStarClosedUpperShriekAdjunction i j hij).counit.app K)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit.app K) w

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pro-etale closed-support triangle before
constructible restriction (uniqueness of the connecting map).

The connecting map of the closed-support triangle
`AlgebraicGeometry.ProEtale.closedSupportTriangle` is unique [BBD, 1.1.9]: for two choices
`w`, `w'`, the morphism of triangles extending `𝟙 K` has components `(𝟙, 𝟙, 𝟙)`, because
`Hom((Ri_* Ri^! K)[1], Rj_* Lj^* K) = 0`
(`AlgebraicGeometry.ProEtale.subsingleton_hom_shift_rightDerivedFunctor_lowerStar`). -/
theorem existsUnique_distTriang_closedSupportTriangle [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    ∃! w, closedSupportTriangle i j hij K w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ :=
    exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit i j hij K
  refine ⟨w, hw, fun w' hw' ↦ ?_⟩
  have : Subsingleton ((closedSupportTriangle i j hij K w').obj₁⟦(1 : ℤ)⟧ ⟶
      (closedSupportTriangle i j hij K w).obj₃) :=
    subsingleton_hom_shift_rightDerivedFunctor_lowerStar i j hij _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw' hw (𝟙 _)
    (by rw [Category.id_comp]; exact comp_distTriang_mor_zero₁₂ _ hw')
  have h₁ : τ.hom₁ = 𝟙 _ := Triangle.cancel_mor₁_of_subsingleton hw
    (by rw [← τ.comm₁, hτ, Category.comp_id, Category.id_comp]; rfl)
  have h₃ : τ.hom₃ = 𝟙 _ := Triangle.cancel_mor₂_of_subsingleton hw'
    (by rw [τ.comm₂, hτ, Category.id_comp, Category.comp_id]; rfl)
  have h := τ.comm₃
  rw [h₁, h₃] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  exact h

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pro-etale closed-support triangle before
constructible restriction (naturality).

For `φ : K ⟶ K'` and distinguished closed-support triangles of `K` and `K'`, the triple
`(Ri_* Ri^! φ, φ, Rj_* Lj^* φ)` is a morphism of triangles, and it is the only morphism of
triangles with middle component `φ`
(`CategoryTheory.Pretriangulated.triangleHom_ext_of_subsingleton`). -/
theorem existsUnique_triangleHom_closedSupportTriangle [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K K' : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))} (φ : K ⟶ K')
    {w w'} (hw : closedSupportTriangle i j hij K w ∈ distTriang _)
    (hw' : closedSupportTriangle i j hij K' w' ∈ distTriang _) :
    ∃! τ : closedSupportTriangle i j hij K w ⟶ closedSupportTriangle i j hij K' w',
      τ.hom₂ = φ ∧
      τ.hom₁ = R((i)_*[ModuleCat.{u + 1} R]).map
        ((closedUpperShriek (ModuleCat.{u + 1} R) i j).rightDerivedFunctor.map φ) ∧
      τ.hom₃ = R((j)_*[ModuleCat.{u + 1} R]).map (L((j)^*[ModuleCat.{u + 1} R]).map φ) := by
  have : Subsingleton ((closedSupportTriangle i j hij K w).obj₁⟦(1 : ℤ)⟧ ⟶
      (closedSupportTriangle i j hij K' w').obj₃) :=
    subsingleton_hom_shift_rightDerivedFunctor_lowerStar i j hij _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw hw' φ (by
    rw [← Category.assoc]
    erw [← (derivedLowerStarClosedUpperShriekAdjunction i j hij).counit_naturality]
    rw [Category.assoc]
    erw [comp_distTriang_mor_zero₁₂ _ hw']
    rw [comp_zero])
  refine ⟨τ, ⟨hτ, Triangle.cancel_mor₁_of_subsingleton hw' ?_,
    Triangle.cancel_mor₂_of_subsingleton hw ?_⟩, fun τ' hτ' ↦
      triangleHom_ext_of_subsingleton hw hw' (hτ'.1.trans hτ.symm)⟩
  · rw [← τ.comm₁, hτ]
    exact ((derivedLowerStarClosedUpperShriekAdjunction i j hij).counit_naturality φ).symm
  · rw [τ.comm₂, hτ]
    exact ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit_naturality φ).symm

/-- `Ri^! Rj_* = 0`: for `M ∈ D(Z_proét)`, maps `M ⟶ Ri^! Rj_* N` correspond to maps
`Ri_* M ⟶ Rj_* N`, and there are none but zero
(`AlgebraicGeometry.ProEtale.subsingleton_hom_shift_rightDerivedFunctor_lowerStar`). -/
theorem isZero_closedUpperShriek_rightDerivedFunctor_obj_rightDerivedFunctor_lowerStar
    [QuasiCompact j] (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (N : DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))) :
    IsZero ((closedUpperShriek (ModuleCat.{u + 1} R) i j).rightDerivedFunctor.obj
      (R((j)_*[ModuleCat.{u + 1} R]).obj N)) := by
  set E := (closedUpperShriek (ModuleCat.{u + 1} R) i j).rightDerivedFunctor.obj
    (R((j)_*[ModuleCat.{u + 1} R]).obj N)
  rw [IsZero.iff_id_eq_zero]
  have := subsingleton_hom_shift_rightDerivedFunctor_lowerStar i j hij E N 0
  have : Subsingleton (R((i)_*[ModuleCat.{u + 1} R]).obj E ⟶
      R((j)_*[ModuleCat.{u + 1} R]).obj N) :=
    ((shiftFunctorZero _ ℤ).app _).homFromEquiv.symm.subsingleton
  have : Subsingleton (E ⟶ E) :=
    ((derivedLowerStarClosedUpperShriekAdjunction i j hij).homEquiv _ _).symm.subsingleton
  exact Subsingleton.elim _ _

end ProEtale

end AlgebraicGeometry
