/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper

/-!
# The idempotent of a clopen subscheme on the derived category

For an open immersion `j : U ⟶ X` with closed range, the derived category `D(X_proét)`
carries a canonical endomorphism `e_U : 𝟭 ⟶ 𝟭` of its identity functor, "multiplication by
the characteristic function of `U`": the composite

```
  𝟭 ──η──▶ Rj_* Lj^* ≃ j_* j^* ≃ j_! j^* ──ε──▶ 𝟭
```

of the unit of `Lj^* ⊣ Rj_*`, the levelwise identifications `Lj^* ≃ j^*` and `Rj_* ≃ j_*` of
the derived functors of the exact functors `j^*` and `j_*`, the inverse of the comparison
`j_! ⟶ j_*` (an isomorphism because the range of `j` is closed) and the counit of the derived
adjunction `j_! ⊣ j^*`.

Every map in it is canonical: none depends on a choice of compactification.

## Main definitions

- `AlgebraicGeometry.ProEtale.clopenIdempotentSheaf`: the endomorphism `e_U` of the identity
  functor of the category of pro-étale sheaves on `X`.
- `AlgebraicGeometry.ProEtale.clopenIdempotent`: the endomorphism `e_U` of the identity
  functor of `D(X_proét)`.

## Main results

- `AlgebraicGeometry.ProEtale.clopenIdempotent_app_Qh_obj`: on a complex, `e_U` is induced by
  the sheaf-level idempotent.
- `AlgebraicGeometry.ProEtale.sum_clopenIdempotent`: the idempotents of a finite partition of
  `X` into clopen subschemes sum to the identity.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j` with closed range, the pushforward `j_*` is right exact: it is
isomorphic to the extension by zero `j_!`, a left adjoint. -/
lemma preservesFiniteColimits_lowerStar_of_isClosed_range (hj : IsClosed (Set.range j.base)) :
    PreservesFiniteColimits (j)_*[A] :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  preservesFiniteColimits_of_natIso (asIso (openImmersionLowerShriekToLowerStar A j))

/-- The derived pushforward along an open immersion `j` with closed range is the extension by
zero applied levelwise, `Rj_* ≃ j_*` (`j_*` is exact) followed by the inverse of the
comparison `j_! ≃ j_*`. -/
noncomputable def rightDerivedLowerStarIsoOfIsClosedRange (hj : IsClosed (Set.range j.base)) :
    R((j)_*[A]) ≅ D((j)_!open[A]) :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  have := preservesFiniteColimits_lowerStar_of_isClosed_range A j hj
  (j)_*[A].rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (openImmersionLowerShriekToLowerStar A j)).symm


/-- Morphisms of pro-étale sheaves on `X` are determined by their restrictions along a family of
open immersions `g i : W i ⟶ X` covering `X`: the kernel of their difference becomes an
isomorphism after each restriction, hence is one by
`AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction`. -/
lemma hom_ext_of_openImmersionRestriction {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ⋃ i, Set.range (g i).base = Set.univ) {G G' : Sheaf (Scheme.ProEt.topology X) A}
    {φ ψ : G ⟶ G'}
    (h : ∀ i, (openImmersionRestriction A (g i)).map φ =
      (openImmersionRestriction A (g i)).map ψ) :
    φ = ψ := by
  have hcover : Presieve.ofArrows _ g ∈ Scheme.proetalePrecoverage X :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ Set.mem_iUnion.mp (hg.ge (Set.mem_univ x)), fun i ↦ inferInstance⟩)
  have : IsIso (kernel.ι (φ - ψ)) :=
    isIso_of_isIso_localizationRestriction A _ g hcover fun i ↦
      KernelFork.IsLimit.isIso_ι _
        (KernelFork.mapIsLimit _ (kernelIsKernel (φ - ψ)) (openImmersionRestriction A (g i)))
        (by rw [Functor.map_sub, h i, sub_self])
  rw [← sub_eq_zero, ← cancel_epi (kernel.ι (φ - ψ)), kernel.condition, comp_zero]

/-- The restriction along `j` of the comparison `j_! ⟶ j_*` at `G`, preceded by the unit of
`j_! ⊣ j^*`, is the inverse of the counit of `j^* ⊣ j_*`. -/
lemma openImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar_app
    (G : Sheaf (Scheme.ProEt.topology U) A) :
    (openImmersionLowerShriekAdjunction A j).unit.app G ≫
        (openImmersionRestriction A j).map ((openImmersionLowerShriekToLowerStar A j).app G) =
      inv ((openImmersionRestrictionLowerStarAdjunction A j).counit.app G) := by
  rw [openImmersionLowerShriekToLowerStar_app, Functor.map_comp, NatIso.isIso_inv_app]
  erw [(openImmersionLowerShriekAdjunction A j).unit_naturality_assoc]
  erw [Adjunction.right_triangle_components, Category.comp_id]

/-- The idempotent `e_U : 𝟭 ⟶ 𝟭` of the clopen subscheme `U` on pro-étale sheaves on `X`, for an
open immersion `j : U ⟶ X` with closed range: the composite

```
  𝟭 ──η──▶ j_* j^* ≃ j_! j^* ──ε──▶ 𝟭
```

of the unit of `j^* ⊣ j_*`, the inverse of the comparison `j_! ⟶ j_*` and the counit of
`j_! ⊣ j^*`. Its image on derived categories is `AlgebraicGeometry.ProEtale.clopenIdempotent`
(`AlgebraicGeometry.ProEtale.clopenIdempotent_app_Qh_obj`). -/
noncomputable def clopenIdempotentSheaf (hj : IsClosed (Set.range j.base)) :
    𝟭 (Sheaf (Scheme.ProEt.topology X) A) ⟶ 𝟭 _ :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  (upperStarLowerStarAdjunction A j).unit ≫
    Functor.whiskerLeft (j)^*[A] (inv (openImmersionLowerShriekToLowerStar A j)) ≫
    (openImmersionLowerShriekUpperStarAdjunction A j).counit

/-- The components of `AlgebraicGeometry.ProEtale.clopenIdempotentSheaf`, written with the
restriction `j^*` of `AlgebraicGeometry.ProEtale.openImmersionRestriction` in place of the
pullback. -/
lemma clopenIdempotentSheaf_app (hj : IsClosed (Set.range j.base))
    (F : Sheaf (Scheme.ProEt.topology X) A) :
    have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
    (clopenIdempotentSheaf A j hj).app F =
      (openImmersionRestrictionLowerStarAdjunction A j).unit.app F ≫
        (inv (openImmersionLowerShriekToLowerStar A j)).app
          ((openImmersionRestriction A j).obj F) ≫
        (openImmersionLowerShriekAdjunction A j).counit.app F := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  simp only [clopenIdempotentSheaf, NatTrans.comp_app, Functor.whiskerLeft_app,
    openImmersionLowerShriekUpperStarAdjunction, localizationLowerShriekUpperStarAdjunction,
    Adjunction.ofNatIsoRight_counit, Functor.whiskerRight_app]
  rw [Iso.symm_inv, ← NatTrans.naturality_assoc, upperStarIsoLocalizationRestriction]
  erw [Adjunction.unit_leftAdjointUniq_hom_app_assoc]
  rfl

/-- The idempotent `e_U` restricts to the identity on `U`. -/
lemma openImmersionRestriction_map_clopenIdempotentSheaf_app
    (hj : IsClosed (Set.range j.base)) (F : Sheaf (Scheme.ProEt.topology X) A) :
    (openImmersionRestriction A j).map ((clopenIdempotentSheaf A j hj).app F) = 𝟙 _ := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  have h₁ := IsIso.eq_inv_of_inv_hom_id
    ((openImmersionRestrictionLowerStarAdjunction A j).left_triangle_components F)
  have h₂ := IsIso.eq_inv_of_hom_inv_id
    ((openImmersionLowerShriekAdjunction A j).right_triangle_components F)
  have h₃ : (openImmersionRestriction A j).map ((openImmersionLowerShriekToLowerStar A j).app
      ((openImmersionRestriction A j).obj F)) =
        inv ((openImmersionLowerShriekAdjunction A j).unit.app _) ≫
          inv ((openImmersionRestrictionLowerStarAdjunction A j).counit.app _) := by
    rw [← openImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar_app,
      IsIso.inv_hom_id_assoc]
  rw [clopenIdempotentSheaf_app, Functor.map_comp, Functor.map_comp, NatIso.isIso_inv_app,
    Functor.map_inv, h₁, h₂]
  simp [h₃]

/-- The idempotent `e_U` restricts to zero on an open `k : W ⟶ X` disjoint from `U`, since it
factors through `j_* j^*`, which vanishes on `W`. -/
lemma openImmersionRestriction_map_clopenIdempotentSheaf_app_of_disjoint {W : Scheme.{u}}
    (k : W ⟶ X) [IsOpenImmersion k] (hjk : Set.range j.base ∩ Set.range k.base = ∅)
    (hj : IsClosed (Set.range j.base)) (F : Sheaf (Scheme.ProEt.topology X) A) :
    (openImmersionRestriction A k).map ((clopenIdempotentSheaf A j hj).app F) = 0 := by
  rw [clopenIdempotentSheaf_app, Functor.map_comp,
    (isZero_openImmersionRestriction_lowerStar A j k hjk _).eq_of_tgt
      ((openImmersionRestriction A k).map _) 0, zero_comp]

/-- The idempotents of a finite partition of `X` into clopen subschemes sum to the identity:
`∑ᵢ e_{Uᵢ} = 𝟙`. Both sides agree after restriction to each `Uₖ`, where `e_{Uₖ}` restricts to the
identity and the other idempotents to zero. -/
theorem sum_clopenIdempotentSheaf {ι : Type*} [Fintype ι] {B : ι → Scheme.{u}}
    (j : ∀ i, B i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ) :
    ∑ i, clopenIdempotentSheaf A (j i) (hclosed i) = 𝟙 _ := by
  refine NatTrans.ext (funext fun F ↦ ?_)
  rw [NatTrans.app_sum, NatTrans.id_app]
  refine hom_ext_of_openImmersionRestriction A j hcover fun k ↦ ?_
  rw [Functor.map_sum, Finset.sum_eq_single k,
    openImmersionRestriction_map_clopenIdempotentSheaf_app, CategoryTheory.Functor.map_id]
  · exact fun i _ hik ↦ openImmersionRestriction_map_clopenIdempotentSheaf_app_of_disjoint A
      (j i) (j k) (Set.disjoint_iff_inter_eq_empty.mp (hdisj hik)) _ F
  · exact fun h ↦ absurd (Finset.mem_univ k) h
/- The K-flat resolution package on `A`, which makes the derived pullback `Lj^*` and the
derived adjunction `j_! ⊣ j^*` available. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The idempotent `e_U : 𝟭 ⟶ 𝟭` of the clopen subscheme `U` on `D(X_proét)`, for an open
immersion `j : U ⟶ X` with closed range: the composite

```
  𝟭 ──η──▶ Rj_* Lj^* ≃ j_! j^* ──ε──▶ 𝟭
```

of the unit of `Lj^* ⊣ Rj_*`, `Lj^* ≃ j^*`, `rightDerivedLowerStarIsoOfIsClosedRange` and
the counit of the derived adjunction `j_! ⊣ j^*`. -/
noncomputable def clopenIdempotent (hj : IsClosed (Set.range j.base)) :
    𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ⟶ 𝟭 _ :=
  (derivedUpperStarLowerStarAdjunction A j).unit ≫
    (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A j) _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarIsoOfIsClosedRange A j hj)).hom ≫
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit

/-- On the image `Qh K` of an object of the homotopy category, the idempotent `e_U` is the image
of the composite of the unit of `j^* ⊣ j_*`, the inverse of the comparison `j_! ⟶ j_*` and the
counit of `j_! ⊣ j^*` on homotopy categories. -/
lemma clopenIdempotent_app_Qh_obj (hj : IsClosed (Set.range j.base))
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ)) :
    have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
    (clopenIdempotent A j hj).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
        (((upperStarLowerStarAdjunction A j).mapHomotopyCategory (.up ℤ)).unit.app K ≫
          (NatTrans.mapHomotopyCategory (inv (openImmersionLowerShriekToLowerStar A j))
            (.up ℤ)).app _ ≫
          ((openImmersionLowerShriekUpperStarAdjunction A j).mapHomotopyCategory
            (.up ℤ)).counit.app K) := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  have := preservesFiniteColimits_lowerStar_of_isClosed_range A j hj
  have hC := (openImmersionLowerShriekUpperStarAdjunction A
    j).mapDerivedCategoryAdjunction_counit_app_Qh_obj K
  have hU := (upperStarLowerStarAdjunction A j).mapDerivedCategoryAdjunction_unit_app_Qh_obj K
  have hη : (upperStarLowerStarAdjunction A j).mapDerivedCategoryAdjunction.unit.app
      (DerivedCategory.Qh.obj K) =
      (derivedUpperStarLowerStarAdjunction A j).unit.app (DerivedCategory.Qh.obj K) ≫
      (j)_*[A].rightDerivedFunctor.map ((leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app
        (DerivedCategory.Qh.obj K)) ≫
      (j)_*[A].rightDerivedFunctorIsoMapDerivedCategory.hom.app ((j)^*[A].mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K)) := by
    simp only [Adjunction.mapDerivedCategoryAdjunction, Adjunction.ofNatIsoRight_unit,
      Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc, derivedUpperStarLowerStarAdjunction,
      leftDerivedUpperStarIsoMapDerivedCategory]
  simp only [clopenIdempotent, rightDerivedLowerStarIsoOfIsClosedRange, NatTrans.comp_app,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [reassoc_of% hη.symm, derivedOpenImmersionLowerShriekUpperStarAdjunction, hC,
    ← NatTrans.naturality_assoc]
  erw [Functor.mapDerivedCategoryNatIso_fach_assoc]
  rw [reassoc_of% hU, ← Functor.map_comp, ← Functor.map_comp, Iso.symm_hom, asIso_inv]

/-- The idempotents of a finite partition of `X` into clopen subschemes sum to the identity of
`D(X_proét)`: `∑ᵢ e_{Uᵢ} = 𝟙`. On a complex, each `e_{Uᵢ}` is induced by the sheaf-level
idempotent `AlgebraicGeometry.ProEtale.clopenIdempotentSheaf`, and those sum to the identity
(`AlgebraicGeometry.ProEtale.sum_clopenIdempotentSheaf`). -/
theorem sum_clopenIdempotent {ι : Type*} [Fintype ι] {B : ι → Scheme.{u}}
    (j : ∀ i, B i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ) :
    ∑ i, clopenIdempotent A (j i) (hclosed i) = 𝟙 _ := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ)) fun K ↦ ?_
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have h := NatTrans.congr_app (sum_clopenIdempotentSheaf A j hclosed hdisj hcover)
  rw [NatTrans.app_sum, NatTrans.id_app,
    Finset.sum_congr rfl fun i _ ↦ clopenIdempotent_app_Qh_obj A (j i) (hclosed i) _]
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  have := fun i ↦ isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A (j i) (hclosed i)
  -- the homotopy category level composite is the image of the one on complexes
  have key (i : ι) :
      (HomotopyCategory.quotient _ _).map
          (((upperStarLowerStarAdjunction A (j i)).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomotopyCategory (inv (openImmersionLowerShriekToLowerStar A (j i)))
          (.up ℤ)).app (((j i)^*[A].mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj K)) ≫
        (HomotopyCategory.quotient _ _).map
          (((openImmersionLowerShriekUpperStarAdjunction A (j i)).mapHomologicalComplex
            (.up ℤ)).counit.app K) =
      (HomotopyCategory.quotient _ _).map
        (((upperStarLowerStarAdjunction A (j i)).mapHomologicalComplex (.up ℤ)).unit.app K ≫
          (NatTrans.mapHomologicalComplex (inv (openImmersionLowerShriekToLowerStar A (j i)))
            (.up ℤ)).app _ ≫
          ((openImmersionLowerShriekUpperStarAdjunction A (j i)).mapHomologicalComplex
            (.up ℤ)).counit.app K) := by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  simp only [key, ← Functor.map_sum]
  refine Eq.trans (congrArg DerivedCategory.Qh.map ((congrArg (HomotopyCategory.quotient _ _).map
    ?_).trans (CategoryTheory.Functor.map_id _ K))) (CategoryTheory.Functor.map_id _ _)
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum]
  simp only [clopenIdempotentSheaf, NatTrans.app_sum, NatTrans.comp_app] at h ⊢
  simp only [Functor.id_obj, HomologicalComplex.Hom.fAddMonoidHom_apply,
    HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.id_f]
  exact h (K.X n)

end AlgebraicGeometry.ProEtale
