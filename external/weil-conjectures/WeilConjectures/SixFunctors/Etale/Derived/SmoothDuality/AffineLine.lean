/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapCounit
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDuality
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunction

/-!
# Smooth duality for the affine line

The affine-line case of blueprint `lemma-affine-space-etale-localization--1`, from the
projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]` (`proposition-adjunction-projective-line--1`,
`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`).

* If `Rf_! ⊣ G` is an adjunction whose counit is a trace counit
  `Rf_!(G K) ≅ Rf_!(T ⊗ᴸ Lf^* K) ≅ Rf_! T ⊗ᴸ K ⟶ K`
  (`AlgebraicGeometry.Etale.lowerShriekTraceCounit`), then all tensor maps of `Rf_! ⊣ G`, hence of
  `Rf_! ⊣ Rf^!`, are isomorphisms, and `ω_f ≅ G Λ_Y ≅ T`
  (`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_counit_eq`,
  `AlgebraicGeometry.Etale.dualizingComplexIsoOfAdjunction`).
* For `q : ℙ¹_S ⟶ S` this gives smooth duality in degree `-2`, `ω_q ≅ Λ(1)[2]`
  (`AlgebraicGeometry.Etale.projectiveLineSmoothDuality`).
* The projection `p : 𝔸¹_S ⟶ S` is the open immersion `j : 𝔸¹_S ⟶ ℙ¹_S` followed by `q`; open
  immersions satisfy smooth duality in degree `0` (they are étale), so `p` satisfies smooth
  duality in degree `-2` (`AlgebraicGeometry.Etale.affineLineSmoothDuality`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_counit_eq`
- `AlgebraicGeometry.Etale.projectiveLineSmoothDuality`
- `AlgebraicGeometry.Etale.affineLineSmoothDuality`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- Braid étale sheaves through `Etale.sheafBraidedCategory`, as the generic definitions of the
-- derived tensor product do.
attribute [local instance 20000] Etale.sheafBraidedCategory

section TraceCounit

variable {Λ} {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
  {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  {t : (R(f)_![ModuleCat.{u + 1} Λ]).obj T ⟶ 𝟙_ _}
  {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  {γ : ∀ K, G.obj K ≅ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).obj
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)}
  {adj : R(f)_![ModuleCat.{u + 1} Λ] ⊣ G}

/-- If the counit of `Rf_! ⊣ G` is the trace counit of `t : Rf_! T ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.lowerShriekTraceCounit`), then every tensor map
`G M ⊗ᴸ Lf^* N ⟶ G(M ⊗ᴸ N)` of `Rf_! ⊣ G` is an isomorphism: it is the reassociation
`(T ⊗ᴸ Lf^* M) ⊗ᴸ Lf^* N ≅ T ⊗ᴸ Lf^*(M ⊗ᴸ N)`
(`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_counit_eq`). -/
theorem isIso_lowerShriekRightAdjointTensorMap_of_counit_eq
    (hε : ∀ K, adj.counit.app K = lowerShriekTraceCounit Λ f T t γ K)
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (lowerShriekRightAdjointTensorMap adj M N) :=
  Adjunction.isIso_projectionTensorMap_of_counit_eq adj _
    (projectionMap_app_app_naturality_left f)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso _ f N N').hom) (projectionMapAssociativity Λ f).assoc
    T t γ hε M N

/-- If `Rf_!` has a right adjoint `G` whose counit is the trace counit of
`t : Rf_! T ⟶ Λ_Y`, then the canonical tensor map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an
isomorphism for every `K`: the tensor maps of the two right adjoints `G` and `Rf^!` of `Rf_!`
agree. -/
theorem isIso_dualizingComplexTensorMap_of_counit_eq
    (hε : ∀ K, adj.counit.app K = lowerShriekTraceCounit Λ f T t γ K)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ f K) := by
  rw [dualizingComplexTensorMap, isIso_lowerShriekRightAdjointUnitTensorMap_iff,
    lowerShriekRightAdjointTensorMap, Adjunction.isIso_projectionTensorMap_iff_of_adjunction _
      (rightDerivedUpperShriekAdjunction Λ f) adj (projectionMap_app_app_naturality_left f)]
  exact isIso_lowerShriekRightAdjointTensorMap_of_counit_eq hε _ _

variable (adj γ) in
/-- If `Rf_!` has a right adjoint `G` with `G K ≅ T ⊗ᴸ Lf^* K`, then the dualizing complex is
`ω_f = Rf^! Λ_Y ≅ G Λ_Y ≅ T ⊗ᴸ Lf^* Λ_Y ≅ T`. -/
noncomputable def dualizingComplexIsoOfAdjunction : dualizingComplex Λ f ≅ T :=
  (Adjunction.rightAdjointUniq (rightDerivedUpperShriekAdjunction Λ f) adj).app (𝟙_ _) ≪≫
    γ (𝟙_ _) ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).mapIso
      (leftDerivedUpperStarUnitIso _ f) ≪≫ derivedTensorRightUnitor _ X T

end TraceCounit

omit [Finite Λ] in
/-- The shifted Tate twist `Λ_X(m)[n]` is a shifted rank-one local system in degree `-n`. -/
theorem isShiftedRankOneLocalSystem_tateObject_shift [HasTateTwist Λ] (X : Scheme.{u})
    [HasInvertibleExponent Λ X] (m n : ℤ) :
    IsShiftedRankOneLocalSystem ((tateObject Λ X m)⟦n⟧) n := by
  obtain ⟨L, hL, hs, ⟨e⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) X m
  exact ⟨L, hL, hs, ⟨(shiftFunctor _ n).mapIso e⟩⟩

/-- **Smooth duality for the projective line**: for a scheme `S` on which the exponent of `Λ`
is invertible, the projection `q : ℙ¹_S ⟶ S` satisfies smooth duality in degree `-2`. The
projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]` has the trace counit
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`), so the tensor maps of `q` are
isomorphisms and `ω_q ≅ Λ(1)[2]`. -/
theorem projectiveLineSmoothDuality [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    SatisfiesSmoothDuality Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) 2 := by
  intro _
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (ℙ(Option
    (ULift.{u} (Fin 1)); S) ↘ S)
  obtain ⟨adj, hε⟩ := exists_projectiveLineAdjunction Λ S
  exact ⟨(isShiftedRankOneLocalSystem_tateObject_shift Λ _ 1 2).of_iso
    (dualizingComplexIsoOfAdjunction (projectiveLineTwistShiftIso Λ S) adj).symm,
    isIso_dualizingComplexTensorMap_of_counit_eq hε⟩

variable {Λ} in
/-- **Smooth duality for the affine line** (`lemma-affine-space-etale-localization--1` for `d = 1`):
the projection `p : 𝔸¹_S ⟶ S` is the open immersion `j : 𝔸¹_S ⟶ ℙ¹_S` followed by `q : ℙ¹_S ⟶ S`.
Since `j` is étale it satisfies smooth duality in degree `0`
(`AlgebraicGeometry.Etale.EtaleSmoothDuality`), and `q` satisfies it in degree `-2`
(`AlgebraicGeometry.Etale.projectiveLineSmoothDuality`); the tensor maps compose and
`ω_p ≅ Lj^* ω_q`. -/
theorem affineLineSmoothDuality [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]
    (hE : EtaleSmoothDuality Λ) : AffineLineSmoothDuality Λ := by
  intro S _ _ _
  set j := AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S
  set q := ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S
  have w : j ≫ q = 𝔸(ULift.{u} (Fin 1); S) ↘ S := AffineSpace.toRelativeProjectiveSpace_over _ _
  have : QuasiCompact (j ≫ q) := by
    rw [w]
    infer_instance
  have : QuasiCompact j := .of_comp _ q
  have : HasCompactification j := (Compactification.ofIsOpenImmersion _).hasCompactification
  obtain ⟨hωq, hθq⟩ := projectiveLineSmoothDuality Λ S
  obtain ⟨hθj, hωj⟩ := hE j
  refine ⟨?_, fun K ↦ isIso_dualizingComplexTensorMap_comp_of_forall Λ j q _ w hθj
    hωq.isInvertible K (hθq K)⟩
  obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_leftDerivedUpperStar Λ j q _ w (hθj _) hωj
  exact (hωq.leftDerivedUpperStar j).of_iso c.symm

end Etale

end AlgebraicGeometry
