/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Sheaves supported on a closed subscheme, with `ℓ`-adic coefficients

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` the complementary quasi-compact open
immersion. This file proves the sheaf-level and derived-level facts behind the closed-support
triangle `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` (blueprint `lemma-local-cohomology-right-adjoint--2`) for
sheaves of modules over the constant `ℓ`-adic sheaf, `AlgebraicGeometry.ProEtale.AdicSheaf`.

## A recollement criterion on derived categories

The derived statements are deduced, in a general form, from the following abelian data: exact
functors `i^* : A ⥤ A_Z`, `i_* : A_Z ⥤ A`, `j^* : A ⥤ A_U` with `i^* ⊣ i_*`, the counit
`i^* i_* ⟶ 𝟭` invertible, `j^* i_* = 0`, and `i^*`, `j^*` jointly detecting zero objects. Then:

* `D(j^*) Ri_* = 0`
  (`DerivedCategory.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj`);
* `D(i^*)` and `D(j^*)` jointly detect zero objects
  (`DerivedCategory.isZero_of_isZero_mapDerivedCategory_obj`);
* the unit `K ⟶ Ri_* D(i^*) K` of `D(i^*) ⊣ Ri_*` is an isomorphism when `D(j^*) K = 0`, so `K`
  lies in the essential image of `Ri_*`
  (`DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero`,
  `DerivedCategory.rightDerivedFunctor_essImage_of_isZero`).

Moreover, for an adjunction `L ⊣ R` with `L` exact and invertible counit, the counit of the
derived adjunction `D(L) ⊣ RR` is invertible
(`CategoryTheory.Adjunction.isIso_mapDerivedCategoryRightDerivedAdjunction_counit`).

These are the inputs of `CategoryTheory.Pretriangulated.Recollement`. They apply to any
categories of sheaves of modules with these properties, e.g. to Weil sheaves.

## The `ℓ`-adic case

* `j^* i_* = 0` (`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_obj_adicLowerStar_obj`);
* `i^*`, `j^*` jointly detect zero objects
  (`AlgebraicGeometry.ProEtale.AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl`);
* `i_*` is exact (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isCompl`);
* a sheaf `F` with `j^* F = 0` has invertible unit `F ⟶ i_* i^* F`
  (`AlgebraicGeometry.ProEtale.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl`).

All of them are transported from the underlying pro-étale sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.WeilCoefficients`) through the forgetful functor `AdicSheaf.forget`. On
derived categories, `D(g^*) ⊣ Rg_*`
(`AlgebraicGeometry.ProEtale.adicDerivedUpperStarLowerStarAdjunction`) has invertible counit for
`g` a closed or an open immersion, and the criterion above gives `D(j^*) Ri_* = 0` and the
essential image of `Ri_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- For an adjunction `L ⊣ R` with `L` exact and invertible counit (i.e. `R` fully faithful), the
counit of the derived adjunction `D(L) ⊣ RR` is invertible: `R` preserves K-injective complexes,
being right adjoint to an exact functor, so `RR` is fully faithful. -/
instance isIso_mapDerivedCategoryRightDerivedAdjunction_counit (adj : L ⊣ R)
    [IsIso adj.counit] : IsIso adj.mapDerivedCategoryRightDerivedAdjunction.counit :=
  have := adj.preservesKInjectiveComplexes
  have h := adj.fullyFaithfulROfIsIsoCounit
  have := h.full
  have := h.faithful
  adj.mapDerivedCategoryRightDerivedAdjunction.counit_isIso_of_R_fully_faithful

end CategoryTheory.Adjunction

namespace DerivedCategory

variable {A Z U : Type*} [Category A] [Category Z] [Category U] [Abelian A] [Abelian Z]
  [Abelian U] [HasDerivedCategory A] [HasDerivedCategory Z] [HasDerivedCategory U]
  {iUp : A ⥤ Z} {iLow : Z ⥤ A} {jUp : A ⥤ U}
  [iUp.Additive] [iLow.Additive] [jUp.Additive]
  [PreservesFiniteLimits iUp] [PreservesFiniteColimits iUp]
  [PreservesFiniteLimits iLow] [PreservesFiniteColimits iLow]
  [PreservesFiniteLimits jUp] [PreservesFiniteColimits jUp]

omit [iUp.Additive] [PreservesFiniteLimits iUp]
  [PreservesFiniteColimits iUp] in
/-- If `j^* i_* = 0` on objects, for exact `i_*` and `j^*`, then `D(j^*) D(i_*) = 0`. -/
lemma isZero_mapDerivedCategory_obj_mapDerivedCategory_obj
    (h₀ : ∀ M, IsZero (jUp.obj (iLow.obj M))) (M : DerivedCategory Z) :
    IsZero (jUp.mapDerivedCategory.obj (iLow.mapDerivedCategory.obj M)) :=
  (Functor.isZero_mapDerivedCategory_obj (iLow ⋙ jUp) M fun _ ↦ h₀ _).of_iso
    ((iLow.mapDerivedCategoryCompIso jUp).app M)

omit [iUp.Additive] [PreservesFiniteLimits iUp]
  [PreservesFiniteColimits iUp] in
/-- If `j^* i_* = 0` on objects, for exact `i_*` and `j^*`, then `D(j^*) Ri_* = 0`. -/
lemma isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj [HasKInjectiveResolutions Z]
    (h₀ : ∀ M, IsZero (jUp.obj (iLow.obj M))) (M : DerivedCategory Z) :
    IsZero (jUp.mapDerivedCategory.obj (iLow.rightDerivedFunctor.obj M)) :=
  (isZero_mapDerivedCategory_obj_mapDerivedCategory_obj h₀ M).of_iso
    (jUp.mapDerivedCategory.mapIso (iLow.rightDerivedFunctorIsoMapDerivedCategory.app M))

omit [iLow.Additive] [PreservesFiniteLimits iLow] [PreservesFiniteColimits iLow] in
/-- If the exact functors `i^*` and `j^*` jointly detect zero objects, so do `D(i^*)` and `D(j^*)`:
on homology objects, `H^n(D(g^*) K) ≅ g^* H^n(K)`. -/
lemma isZero_of_isZero_mapDerivedCategory_obj
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F) {K : DerivedCategory A}
    (hi : IsZero (iUp.mapDerivedCategory.obj K)) (hj : IsZero (jUp.mapDerivedCategory.obj K)) :
    IsZero K :=
  (DerivedCategory.isZero_iff _).2 fun n ↦ hdet _
    (((DerivedCategory.isZero_iff _).1 hi n).of_iso
      ((iUp.mapDerivedCategoryHomologyFunctorIso n).app K))
    (((DerivedCategory.isZero_iff _).1 hj n).of_iso
      ((jUp.mapDerivedCategoryHomologyFunctorIso n).app K))

variable [HasKInjectiveResolutions Z] (adj : iUp ⊣ iLow)

/-- **Complexes killed by `j^*` come from the closed part.** Let `i^* ⊣ i_*` be an adjunction of
exact functors with invertible counit, and `j^*` exact, with `j^* i_* = 0` and `i^*`, `j^*`
jointly detecting zero objects. For `K` with `D(j^*) K = 0`, the unit `K ⟶ Ri_* D(i^*) K` of
`D(i^*) ⊣ Ri_*` is an isomorphism: its cone is killed by `D(i^*)`, which inverts the unit since
the counit is invertible, and by `D(j^*)`, which kills both its ends. -/
lemma isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero [IsIso adj.counit]
    (h₀ : ∀ M, IsZero (jUp.obj (iLow.obj M)))
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F) {K : DerivedCategory A}
    (hK : IsZero (jUp.mapDerivedCategory.obj K)) :
    IsIso (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app K) := by
  set adj' := adj.mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨W, v, w, h₁⟩ := distinguished_cocone_triangle (adj'.unit.app K)
  have hiu : IsIso (iUp.mapDerivedCategory.map (adj'.unit.app K)) :=
    have := IsIso.id (iUp.mapDerivedCategory.obj K)
    IsIso.of_isIso_fac_right (adj'.left_triangle_components K)
  have hju : IsIso (jUp.mapDerivedCategory.map (adj'.unit.app K)) :=
    isIso_of_source_target_iso_zero _ hK.isoZero
      (isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj h₀ _).isoZero
  have hW : IsZero W := isZero_of_isZero_mapDerivedCategory_obj hdet
    ((Triangle.isZero₃_iff_isIso₁ _ (iUp.mapDerivedCategory.map_distinguished _ h₁)).2 hiu)
    ((Triangle.isZero₃_iff_isIso₁ _ (jUp.mapDerivedCategory.map_distinguished _ h₁)).2 hju)
  exact (Triangle.isZero₃_iff_isIso₁ _ h₁).1 hW

/-- **Complexes killed by `j^*` come from the closed part**: under the hypotheses of
`DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero`, a complex
`K` with `D(j^*) K = 0` lies in the essential image of `Ri_*`. -/
lemma rightDerivedFunctor_essImage_of_isZero [IsIso adj.counit]
    (h₀ : ∀ M, IsZero (jUp.obj (iLow.obj M)))
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F) {K : DerivedCategory A}
    (hK : IsZero (jUp.mapDerivedCategory.obj K)) : iLow.rightDerivedFunctor.essImage K :=
  have := isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero adj h₀ hdet hK
  ⟨_, ⟨(asIso (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app K)).symm⟩⟩

end DerivedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {Z U X : Scheme.{u}}

/-- `j^* i_* = 0` on sheaves of modules over the constant `ℓ`-adic sheaf, for any `i` whose range
misses the range of the open immersion `j`: the underlying sheaf is `j^* i_*` of the underlying
sheaf of `ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint`). -/
lemma isZero_adicUpperStar_obj_adicLowerStar_obj (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) (M : AdicSheaf l Z) :
    IsZero ((j)^*ᵃ[l].obj ((i)_*ᵃ[l].obj M)) :=
  AdicSheaf.isZero_of_isZero_X (isZero_upperStar_lowerStar_of_disjoint _ i j hij M.X)

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

omit [IsOpenImmersion j] in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` for `ℓ`-adic sheaves: for a
closed immersion `i` with quasi-compact open complement `j`, a sheaf `F` of `ℚ̄_ℓ,X`-modules with
`i^* F = 0` and `j^* F = 0` is zero
(`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl` on the underlying sheaf). -/
theorem AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (F : AdicSheaf l X)
    (hi : IsZero ((i)^*ᵃ[l].obj F)) (hj : IsZero ((j)^*ᵃ[l].obj F)) : IsZero F :=
  AdicSheaf.isZero_of_isZero_X (isZero_of_isZero_upperStar_of_isCompl i j hij F.X
    ((AdicSheaf.forget Z).map_isZero hi) ((AdicSheaf.forget U).map_isZero hj))

/-- Blueprint `lemma-passing-schematic-closure--1` for `ℓ`-adic sheaves: a sheaf `F` of
`ℚ̄_ℓ,X`-modules lies in the essential image of `i_*` if and only if `j^* F = 0`. -/
theorem adicLowerStar_essImage_iff_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (F : AdicSheaf l X) :
    ((i)_*ᵃ[l]).essImage F ↔ IsZero ((j)^*ᵃ[l].obj F) := by
  refine ⟨fun ⟨G, ⟨e⟩⟩ ↦ (isZero_adicUpperStar_obj_adicLowerStar_obj i j hij.disjoint G).of_iso
    ((j)^*ᵃ[l].mapIso e.symm), fun hF ↦ ?_⟩
  have := isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl i j hij F hF
  exact ⟨_, ⟨(asIso ((adicUpperStarLowerStarAdjunction l i).unit.app F)).symm⟩⟩

/-! ### Derived categories -/

variable (l) in
/-- The adjunction `D(g^*) ⊣ Rg_*` on the unbounded derived categories of sheaves of modules over
the constant `ℓ`-adic sheaves, `g^*` being exact
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`). -/
noncomputable def adicDerivedUpperStarLowerStarAdjunction {Y W : Scheme.{u}} (g : Y ⟶ W) :
    (g)^*ᵃ[l].mapDerivedCategory ⊣ (g)_*ᵃ[l].rightDerivedFunctor :=
  (adicUpperStarLowerStarAdjunction l g).mapDerivedCategoryRightDerivedAdjunction

/-- For a closed immersion `i`, the counit `D(i^*) Ri_* ⟶ 𝟭` is an isomorphism, i.e. `Ri_*` is
fully faithful. -/
instance isIso_adicDerivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion :
    IsIso (adicDerivedUpperStarLowerStarAdjunction l i).counit :=
  Adjunction.isIso_mapDerivedCategoryRightDerivedAdjunction_counit _

/-- For an open immersion `j`, the counit `D(j^*) Rj_* ⟶ 𝟭` is an isomorphism, i.e. `Rj_*` is
fully faithful, since `j^* j_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_adicDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion :
    IsIso (adicDerivedUpperStarLowerStarAdjunction l j).counit :=
  Adjunction.isIso_mapDerivedCategoryRightDerivedAdjunction_counit _

instance (g : U ⟶ X) [IsOpenImmersion g] : (g)_*ᵃ[l].Full :=
  (adicUpperStarLowerStarAdjunction l g).fullyFaithfulROfIsIsoCounit.full

instance (g : U ⟶ X) [IsOpenImmersion g] : (g)_*ᵃ[l].Faithful :=
  (adicUpperStarLowerStarAdjunction l g).fullyFaithfulROfIsIsoCounit.faithful

/-- `D(j^*) Ri_* = 0` for a closed immersion `i` with quasi-compact open complement `j`, on
sheaves of modules over the constant `ℓ`-adic sheaves. -/
lemma isZero_mapDerivedCategory_adicUpperStar_obj_rightDerivedFunctor_adicLowerStar_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (AdicSheaf l Z)) :
    IsZero ((j)^*ᵃ[l].mapDerivedCategory.obj ((i)_*ᵃ[l].rightDerivedFunctor.obj M)) :=
  have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) i j hij
  DerivedCategory.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj
    (isZero_adicUpperStar_obj_adicLowerStar_obj i j hij.disjoint) M

/-- For a closed immersion `i` with quasi-compact open complement `j`, a complex `K` of sheaves of
`ℚ̄_ℓ,X`-modules with `D(j^*) K = 0` has invertible unit `K ⟶ Ri_* D(i^*) K`. -/
lemma isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) {K : DerivedCategory (AdicSheaf l X)}
    (hK : IsZero ((j)^*ᵃ[l].mapDerivedCategory.obj K)) :
    IsIso ((adicDerivedUpperStarLowerStarAdjunction l i).unit.app K) :=
  have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) i j hij
  DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero _
    (isZero_adicUpperStar_obj_adicLowerStar_obj i j hij.disjoint)
    (AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl i j hij) hK

/-- For a closed immersion `i` with quasi-compact open complement `j`, a complex `K` of sheaves of
`ℚ̄_ℓ,X`-modules with `D(j^*) K = 0` lies in the essential image of `Ri_*`. -/
lemma rightDerivedFunctor_adicLowerStar_essImage_of_isZero
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) {K : DerivedCategory (AdicSheaf l X)}
    (hK : IsZero ((j)^*ᵃ[l].mapDerivedCategory.obj K)) :
    (i)_*ᵃ[l].rightDerivedFunctor.essImage K :=
  have := isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero i j hij hK
  ⟨_, ⟨(asIso ((adicDerivedUpperStarLowerStarAdjunction l i).unit.app K)).symm⟩⟩

end AlgebraicGeometry.ProEtale
