/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Derived global sections of a finite disjoint union

Let `S` be the disjoint union of finitely many schemes `T i`, with inclusions `f i : T i ⟶ S`
(that is, `Cofan.mk S f` is a colimit cofan). For a complex `K` of étale sheaves of
`Λ`-modules on `S`, the units `K ⟶ R(f i)_* (f i)^* K` exhibit `K` as the product of the
pushforwards of its restrictions to the pieces, and consequently the restriction maps
`RΓ(S, K) ⟶ RΓ(T i, (f i)^* K)` exhibit `RΓ(S, K)` as the product of the `RΓ(T i, (f i)^* K)`.

## Main results

- `AlgebraicGeometry.Etale.isIso_piLift_unit_of_isColimit`: `K ≅ ∏ᵢ R(f i)_* (f i)^* K`.
- `AlgebraicGeometry.Etale.isIso_piLift_globalSectionsRestriction_of_isColimit`:
  `RΓ(S, K) ≅ ∏ᵢ RΓ(T i, (f i)^* K)`.
- `AlgebraicGeometry.Etale.globalSectionsRestriction_ext_of_isColimit` and
  `AlgebraicGeometry.Etale.eq_zero_of_globalSectionsRestriction_of_isColimit`: morphisms into
  `RΓ(S, K)` are detected by the restrictions to the pieces.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Cofan

variable {ι : Type*} [Finite ι] {S : Scheme.{u}} {T : ι → Scheme.{u}} {f : ∀ i, T i ⟶ S}

/-- The canonical isomorphism from the coproduct `∐ T` to the point of a colimit cofan. -/
private noncomputable def sigmaIsoOfIsColimit (hS : IsColimit (Cofan.mk S f)) : ∐ T ≅ S :=
  (colimit.isColimit _).coconePointUniqueUpToIso hS

/-- The isomorphism `∐ T ≅ S` restricts to `f i` on the summand `T i`. -/
private lemma sigmaι_sigmaIsoOfIsColimit_hom (hS : IsColimit (Cofan.mk S f)) (i : ι) :
    Sigma.ι T i ≫ (sigmaIsoOfIsColimit hS).hom = f i :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hS ⟨i⟩

/-- The inclusions of the pieces of a finite disjoint union are open immersions. -/
lemma isOpenImmersion_of_isColimit_cofan (hS : IsColimit (Cofan.mk S f)) (i : ι) :
    IsOpenImmersion (f i) := by
  rw [← sigmaι_sigmaIsoOfIsColimit_hom hS i]
  infer_instance

/-- The pieces of a finite disjoint union have pairwise disjoint images. -/
lemma disjoint_range_of_isColimit_cofan (hS : IsColimit (Cofan.mk S f)) {i j : ι}
    (hij : i ≠ j) : Disjoint (Set.range (f i).base) (Set.range (f j).base) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  rw [← sigmaι_sigmaIsoOfIsColimit_hom hS i, ← sigmaι_sigmaIsoOfIsColimit_hom hS j] at hy
  have h := congrArg (sigmaIsoOfIsColimit hS).inv.base hy
  simp only [← TopCat.comp_app, ← Scheme.Hom.comp_base, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at h
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff T j i y x).1 h)).symm

/-- The pieces of a finite disjoint union cover it. -/
lemma exists_eq_of_isColimit_cofan (hS : IsColimit (Cofan.mk S f)) (x : S) :
    ∃ (i : ι) (y : T i), (f i).base y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover T).covers ((sigmaIsoOfIsColimit hS).inv.base x)
  refine ⟨(sigmaOpenCover T).idx ((sigmaIsoOfIsColimit hS).inv.base x), y, ?_⟩
  rw [← sigmaι_sigmaIsoOfIsColimit_hom hS, Scheme.Hom.comp_apply]
  simp only [sigmaOpenCover_f] at hy
  erw [hy, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

end Cofan

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Isomorphisms of `D(X_ét, Λ)` are detected after pulling back along a finite jointly
surjective family of morphisms, indexed by a type in an arbitrary universe. -/
private lemma isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_exists_eq {X : Scheme.{u}}
    {ι : Type*} [Finite ι] {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L)
    (hφ : ∀ i, IsIso (D((a i)^*[ModuleCat.{u + 1} Λ]).map φ)) : IsIso φ := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  rw [DerivedCategory.isIso_iff]
  intro m
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective _
    (fun k : ULift.{u} (Fin n) ↦ a (e.symm k.down)) (fun x ↦ ?_) _ fun k ↦ ?_
  · obtain ⟨i, y, hy⟩ := ha x
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    exact ⟨⟨k⟩, y, hy⟩
  · exact (NatIso.isIso_map_iff
      (((a (e.symm k.down))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso m) φ).2
      (Functor.map_isIso (DerivedCategory.homologyFunctor _ m)
        (D((a (e.symm k.down))^*[ModuleCat.{u + 1} Λ]).map φ))

variable {ι : Type*} [Finite ι] {S : Scheme.{u}} {T : ι → Scheme.{u}} (f : ∀ i, T i ⟶ S)

/-- **A complex on a finite disjoint union is the product of the pushforwards of its
restrictions to the pieces**: the units `K ⟶ R(f i)_* (f i)^* K` induce an isomorphism
`K ≅ ∏ᵢ R(f i)_* (f i)^* K`. -/
lemma isIso_piLift_unit_of_isColimit (hS : IsColimit (Cofan.mk S f))
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Pi.lift fun i ↦
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (f i)).unit.app K) := by
  have := isOpenImmersion_of_isColimit_cofan hS
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_exists_eq f
    (exists_eq_of_isColimit_cofan hS) _ fun j ↦ ?_
  let G := D((f j)^*[ModuleCat.{u + 1} Λ])
  let g := fun i ↦
    G.map ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (f i)).unit.app K)
  -- the summands `i ≠ j` vanish on `T j`
  have hz (i : ι) (hij : i ≠ j) : IsZero (G.obj ((R((f i)_*[ModuleCat.{u + 1} Λ])).obj
      (D((f i)^*[ModuleCat.{u + 1} Λ]).obj K))) :=
    isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range _ (f j) (f i)
      (disjoint_range_of_isColimit_cofan hS (Ne.symm hij)) _
  -- the unit at `j` becomes invertible on `T j`, the counit being invertible
  have hj : IsIso (g j) := by
    have : IsIso (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (f j)).counit :=
      (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction _ (f j))
        (mapDerivedUpperStarLowerStarAdjunction _ (f j))).isIso_unit_iff_isIso_counit.1
        inferInstance
    have h := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (f j)).left_triangle_components K
    have : g j = inv ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (f j)).counit.app (G.obj K)) := by
      rw [← cancel_mono ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (f j)).counit.app (G.obj K)), IsIso.inv_hom_id]
      exact h
    rw [this]
    infer_instance
  have hg : IsIso (Pi.lift g) := by
    refine ⟨Pi.π _ j ≫ inv (g j), ?_, ?_⟩
    · rw [Pi.lift_comp_π_assoc, IsIso.hom_inv_id]
    · refine Pi.hom_ext _ _ fun i ↦ ?_
      by_cases hij : i = j
      · subst hij
        simp
      · exact (hz i hij).eq_of_tgt _ _
  have : IsIso (G.map (Pi.lift fun i ↦
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (f i)).unit.app K) ≫
        piComparison G _) := by
    rw [map_lift_piComparison]
    exact hg
  exact IsIso.of_isIso_comp_right _ (piComparison G _)

/-- **Derived global sections of a finite disjoint union**: the restriction maps
`RΓ(S, K) ⟶ RΓ(T i, (f i)^* K)` induce an isomorphism `RΓ(S, K) ≅ ∏ᵢ RΓ(T i, (f i)^* K)`. -/
lemma isIso_piLift_globalSectionsRestriction_of_isColimit (hS : IsColimit (Cofan.mk S f))
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Pi.lift fun i ↦ globalSectionsRestriction (f i) K) := by
  have := isIso_piLift_unit_of_isColimit f hS K
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S).Additive := by
    unfold rightDerivedGlobalSections; infer_instance
  have h : (Pi.lift fun i ↦ globalSectionsRestriction (f i) K) =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S).map (Pi.lift fun i ↦
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (f i)).unit.app K) ≫
        piComparison _ _ ≫ Limits.Pi.map fun i ↦
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ (f i)).hom.app _ := by
    refine Pi.hom_ext _ _ fun i ↦ ?_
    simp [globalSectionsRestriction]
  rw [h]
  infer_instance

/-- **Morphisms into the derived global sections of a finite disjoint union are detected on the
pieces.** -/
theorem globalSectionsRestriction_ext_of_isColimit (hS : IsColimit (Cofan.mk S f))
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {N : DerivedCategory (ModuleCat.{u + 1} Λ)}
    (φ ψ : N ⟶ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S).obj K)
    (h : ∀ i, φ ≫ globalSectionsRestriction (f i) K = ψ ≫ globalSectionsRestriction (f i) K) :
    φ = ψ := by
  have := isIso_piLift_globalSectionsRestriction_of_isColimit f hS K
  rw [← cancel_mono (Pi.lift fun i ↦ globalSectionsRestriction (f i) K)]
  exact Pi.hom_ext _ _ fun i ↦ by simpa using h i

/-- **A morphism into the derived global sections of a finite disjoint union vanishes as soon as
its restrictions to all the pieces vanish.** -/
theorem eq_zero_of_globalSectionsRestriction_of_isColimit (hS : IsColimit (Cofan.mk S f))
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {N : DerivedCategory (ModuleCat.{u + 1} Λ)}
    (φ : N ⟶ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S).obj K)
    (h : ∀ i, φ ≫ globalSectionsRestriction (f i) K = 0) :
    φ = 0 :=
  globalSectionsRestriction_ext_of_isColimit f hS K φ 0 fun i ↦ by simpa using h i

end AlgebraicGeometry.Etale
