/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Pro-étale complexes on an open cover

Let `X` be a scheme with an open cover `X = ⋃ᵢ Uᵢ`. This file records how complexes of pro-étale
sheaves on `X` are controlled by their restrictions to the `Uᵢ`.

## Main results

- `AlgebraicGeometry.ProEtale.nonempty_iso_mapDerivedCategory_upperStar_derivedHom`: restriction
  to an open commutes with the internal hom, `j^* RHom(K, N) ≅ RHom(j^* K, j^* N)`.
- `AlgebraicGeometry.ProEtale.isZero_of_forall_isZero_mapDerivedCategory_upperStar`: a complex
  vanishes if its restrictions to the members of an open cover do.
- `AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_counit_app_of_openCover`: a
  complex `R` such that `Rν_* R` is bounded below is of étale origin, `ν^* Rν_* R ≅ R`, as soon as
  its restrictions to the members of an open cover are of the form `ν^* N`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite ZeroObject

open scoped CategoryTheory.Functor

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Conservative

variable {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)

include hU in
/-- The members of an open cover of `X` form a pro-étale covering family of `X`. -/
lemma ofArrows_opens_ι_mem_proetalePrecoverage :
    Presieve.ofArrows (fun i ↦ (U i : Scheme.{u})) (fun i ↦ (U i).ι) ∈
      Scheme.proetalePrecoverage X :=
  Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨i, by simpa using hi⟩,
        fun i ↦ inferInstanceAs (IsOpenImmersion (U i).ι)⟩)

include hU in
/-- A pro-étale sheaf on `X` vanishes if its restrictions to the members of an open cover
vanish. -/
lemma isZero_of_forall_isZero_upperStar_obj (F : Sheaf (Scheme.ProEt.topology X) A)
    (h : ∀ i, IsZero ((((U i).ι)^*[A]).obj F)) : IsZero F := by
  have : IsIso (0 : F ⟶ 0) := by
    refine ProEtale.isIso_of_isIso_localizationRestriction A (0 : F ⟶ 0) (fun i ↦ (U i).ι)
      (ofArrows_opens_ι_mem_proetalePrecoverage U hU) fun i ↦ ?_
    let e := ProEtale.upperStarIsoLocalizationRestriction A (U i).ι inferInstance
    exact isIso_of_source_target_iso_zero _ ((h i).of_iso (e.app F).symm).isoZero
      (((ProEtale.upperStar A (U i).ι).map_isZero (isZero_zero _)).of_iso (e.app 0).symm).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

include hU in
/-- A complex of pro-étale sheaves on `X` vanishes if its restrictions to the members of an open
cover vanish: its homology sheaves then vanish on the cover. -/
lemma isZero_of_forall_isZero_mapDerivedCategory_upperStar
    (C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (h : ∀ i, IsZero (D(((U i).ι)^*[A]).obj C)) : IsZero C :=
  _root_.DerivedCategory.isZero_of_forall_isZero_homology _ fun q ↦
    isZero_of_forall_isZero_upperStar_obj A U hU _ fun i ↦
      ((_root_.DerivedCategory.homologyFunctor _ q).map_isZero (h i)).of_iso
        (((((U i).ι)^*[A]).mapDerivedCategoryHomologyFunctorIso q).app C)

end Conservative

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Hom

variable [ProEtale.UpperStarPreservesFlat A]

/-- **Restriction to an open commutes with the internal hom**, `j^* RHom(K, N) ≅
RHom(j^* K, j^* N)`: the two sides are right adjoint to `G ↦ K ⊗ᴸ j_! G` and to
`G ↦ j_!(j^* K ⊗ᴸ G)`, which agree by the projection formula for `j_!` (and the symmetry of the
derived tensor product). This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.nonempty_iso_mapDerivedCategory_upperStar_derivedHom`. -/
theorem nonempty_iso_mapDerivedCategory_upperStar_derivedHom {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    Nonempty (D((j)^*[A]).obj (((ProEtale.derivedHom A X).obj (op K)).obj N) ≅
      ((ProEtale.derivedHom A U).obj (op (D((j)^*[A]).obj K))).obj (D((j)^*[A]).obj N)) := by
  obtain ⟨_⟩ :=
    _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology X) A)
  obtain ⟨_⟩ :=
    _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology U) A)
  let adj₁ := (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction A j).comp
    (ProEtale.derivedTensorHomAdjunction A K)
  let adj₂ := (ProEtale.derivedTensorHomAdjunction A (D((j)^*[A]).obj K)).comp
      (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
  let e : D((j)_!open[A]) ⋙ (ProEtale.derivedTensor A X).obj K ≅
      (ProEtale.derivedTensor A U).obj (D((j)^*[A]).obj K) ⋙ D((j)_!open[A]) :=
    Functor.isoWhiskerLeft _ (BraidedCategory.tensorLeftIsoTensorRight K) ≪≫
      (((flipFunctor _ _ _).mapIso
        (derivedOpenImmersionLowerShriekProjectionIso A j)).app K).symm ≪≫
      Functor.isoWhiskerRight ((curriedTensor _).flip.mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory A j).app K) ≪≫
          (BraidedCategory.tensorLeftIsoTensorRight _).symm) D((j)_!open[A])
  exact ⟨((adj₁.ofNatIsoLeft e).rightAdjointUniq adj₂).app N⟩

end Hom

section Gluing

/-- The restriction along `g : Y ⟶ X` commutes with the comparison pullback on derived
categories, `g^* ν_X^* ≅ ν_Y^* g^*`, induced by
`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`. -/
noncomputable def mapDerivedCategoryComparisonUpperStarCompUpperStarIso {Y X : Scheme.{u}}
    (g : Y ⟶ X) :
    D(ν^*(X)[A]) ⋙ D((g)^*[A]) ≅ D(Etale.upperStar A g) ⋙ D(ν^*(Y)[A]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso A g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The extension by zero along an open immersion `j : U ⟶ X` commutes with the comparison
pullback on derived categories, `ν_X^* j_! ≅ j_! ν_U^*`, induced by
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarIso`. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    D(Etale.openImmersionLowerShriek A j) ⋙ D(ν^*(X)[A]) ≅
      D(ν^*(U)[A]) ⋙ D(ProEtale.openImmersionLowerShriek A j) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComparisonUpperStarIso A j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- If `Rν_* C = 0`, there is no nonzero map from a complex of étale origin `ν^* G` to the
restriction of `C` to an open `U`: such maps correspond to maps `j_! ν^* G ≅ ν^* j_! G ⟶ C`,
hence to maps `j_! G ⟶ Rν_* C = 0`. -/
lemma eq_zero_of_isZero_rightDerivedComparisonLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hC : IsZero ((R(ν_*(X)[A])).obj C))
    {G : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (f : D(ν^*(U)[A]).obj G ⟶ D((j)^*[A]).obj C) : f = 0 := by
  let adj := ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  have hφ : ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso A j).app G).hom ≫
      (adj.homEquiv _ _).symm f = 0 :=
    ((derivedComparisonAdjunction A X).homEquiv _ _).injective (hC.eq_of_tgt _ _)
  have h : (adj.homEquiv _ _).symm f = 0 :=
    (cancel_epi ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso A j).app
      G).hom).1 (by rw [hφ, comp_zero])
  rw [← (adj.homEquiv _ _).apply_symm_apply f, h, Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero]

variable {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)

include hU in
/-- **Étale origin is local.** Let `R` be a complex of pro-étale sheaves on `X` such that
`Rν_* R` is bounded below, and whose restriction to every member of an open cover of `X` is of
the form `ν^* N`. Then the counit `ν^* Rν_* R ⟶ R` is an isomorphism, so `R` is of étale origin.

Let `C` be the cone of the counit. Since the unit is invertible on bounded below complexes,
`Rν_*` of the counit is an isomorphism, so `Rν_* C = 0`. On a member `U` of the cover, maps
from complexes of étale origin to `C|_U` vanish
(`AlgebraicGeometry.ProEtale.eq_zero_of_isZero_rightDerivedComparisonLowerStar`). As `R|_U`
and `(ν^* Rν_* R)|_U` are of étale origin, the triangle `(ν^* Rν_* R)|_U ⟶ R|_U ⟶ C|_U ⟶`
then shows that `C|_U = 0`, and `C = 0` by
`AlgebraicGeometry.ProEtale.isZero_of_forall_isZero_mapDerivedCategory_upperStar`. -/
theorem isIso_derivedComparisonAdjunction_counit_app_of_openCover
    (R : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (hR : _root_.DerivedCategory.TStructure.t.plus ((R(ν_*(X)[A])).obj R))
    (h : ∀ i, ∃ N : _root_.DerivedCategory (Sheaf (U i : Scheme.{u}).smallEtaleTopology A),
      Nonempty (D(((U i).ι)^*[A]).obj R ≅ D(ν^*(U i)[A]).obj N)) :
    IsIso ((derivedComparisonAdjunction A X).counit.app R) := by
  let adj := derivedComparisonAdjunction A X
  -- `Rν_*` of the counit is an isomorphism
  have := isIso_derivedComparisonAdjunction_unit_app A X _ hR
  have : IsIso (adj.unit.app _ ≫ (R(ν_*(X)[A])).map (adj.counit.app R)) := by
    rw [adj.right_triangle_components]; exact IsIso.id _
  have hGε : IsIso ((R(ν_*(X)[A])).map (adj.counit.app R)) :=
    IsIso.of_isIso_comp_left (adj.unit.app _) _
  obtain ⟨C, g, h₃, hT⟩ := Pretriangulated.distinguished_cocone_triangle (adj.counit.app R)
  have hC : IsZero ((R(ν_*(X)[A])).obj C) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((R(ν_*(X)[A])).map_distinguished _ hT)).2 hGε
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  refine isZero_of_forall_isZero_mapDerivedCategory_upperStar A U hU C fun i ↦ ?_
  obtain ⟨N, ⟨e⟩⟩ := h i
  have hT' := (D(((U i).ι)^*[A])).map_distinguished _ hT
  -- the map `R|_U ⟶ C|_U` vanishes
  have h₂ : (D(((U i).ι)^*[A])).map g = 0 :=
    (cancel_epi e.inv).1 (by
      rw [eq_zero_of_isZero_rightDerivedComparisonLowerStar A (U i).ι hC
        (e.inv ≫ (D(((U i).ι)^*[A])).map g), comp_zero])
  -- so the map `C|_U ⟶ (ν^* Rν_* R)|_U[1]` is a split monomorphism
  have := Pretriangulated.Triangle.mono₃ _ hT' h₂
  have := isSplitMono_of_mono
    ((D(((U i).ι)^*[A])).mapTriangle.obj (Pretriangulated.Triangle.mk (adj.counit.app R) g h₃)).mor₃
  -- whose retraction vanishes, its source being of étale origin
  let e' : D(ν^*(U i)[A]).obj
        ((D(Etale.upperStar A (U i).ι).obj ((R(ν_*(X)[A])).obj R))⟦(1 : ℤ)⟧) ≅
      (D(((U i).ι)^*[A]).obj (D(ν^*(X)[A]).obj ((R(ν_*(X)[A])).obj R)))⟦(1 : ℤ)⟧ :=
    (D(ν^*(U i)[A]).commShiftIso (1 : ℤ)).app _ ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso
      ((mapDerivedCategoryComparisonUpperStarCompUpperStarIso A (U i).ι).app _).symm
  have hr : retraction ((D(((U i).ι)^*[A])).mapTriangle.obj
      (Pretriangulated.Triangle.mk (adj.counit.app R) g h₃)).mor₃ = 0 :=
    (cancel_epi e'.hom).1 (by
      rw [eq_zero_of_isZero_rightDerivedComparisonLowerStar A (U i).ι hC (e'.hom ≫ _),
        comp_zero])
  rw [IsZero.iff_id_eq_zero]
  exact (IsSplitMono.id ((D(((U i).ι)^*[A])).mapTriangle.obj
    (Pretriangulated.Triangle.mk (adj.counit.app R) g h₃)).mor₃).symm.trans
      (by rw [hr, comp_zero])

end Gluing

end AlgebraicGeometry.ProEtale
