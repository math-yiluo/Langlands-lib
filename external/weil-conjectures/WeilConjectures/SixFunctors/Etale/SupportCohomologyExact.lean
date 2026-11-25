/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# The short exact sequence of sections with support

Let `i : Z ⟶ X` be a closed immersion with open complement `U`. For an injective étale sheaf `I`
on `X` the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism, so for a complex `I` of injective
sheaves

`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`

is a short exact sequence of complexes. The resulting distinguished triangle
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`, with a connecting map natural in `K`, and the
long exact sequence of cohomology with support (blueprint `thm-pur-with-support-exactness`) are
`AlgebraicGeometry.Etale.sectionsWithSupportTriangle` and
`AlgebraicGeometry.Etale.exact_derivedSupportCohomology_sectionsWithSupportTriangle`
(`WeilConjectures.SixFunctors.Etale.SupportCohomologyTriangle`).

## Main statements

- `AlgebraicGeometry.Etale.isSplitEpi_ΓRes_openComplement_of_injective`
- `AlgebraicGeometry.Etale.shortExact_sectionsWithSupportShortComplex`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Site

variable {X : Scheme.{u}}

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
lemma isIso_of_isIso_left {V W : X.Etale} (f : V ⟶ W) (hf : IsIso f.left) : IsIso f := by
  have : IsIso ((Over.forget X).map ((Scheme.Etale.forget X).map f)) := hf
  have : IsIso ((Scheme.Etale.forget X).map f) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact isIso_of_reflects_iso f (Scheme.Etale.forget X)

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `U ×_X U ⟶ U` at `U` of the adjunction between composition with and base change
along the open immersion `j` is an isomorphism, `j` being a monomorphism. -/
instance isIso_mapPullbackAdj_counit_app_mk :
    IsIso ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app
      (Scheme.Etale.mk j)) :=
  isIso_of_isIso_left _ (inferInstanceAs (IsIso (pullback.fst j j)))

/-- The base change along the open immersion `j` of the map from `U` to the terminal étale
`X`-scheme `X` is an isomorphism `U ×_X U ≅ X ×_X U`, both being isomorphic to `U` over `U`. -/
instance isIso_overPullback_map_isTerminalMkId_from :
    IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).map
      ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j))) := by
  refine isIso_of_isIso_left _ ?_
  have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ j).map
    ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk j)).hom :=
    inferInstanceAs (IsIso (pullback.snd j j))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) j))
  exact IsIso.of_isIso_fac_right h

end Site

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Restriction

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For a sheaf `G` on `U`, the restriction `(j_* G)(X) ⟶ (j_* G)(U)` along the open immersion
`j` is an isomorphism: both are the sections of `G` over `U`. -/
instance isIso_lowerStar_obj_map_isTerminalMkId_from (G : Sheaf U.smallEtaleTopology A) :
    IsIso (((j)_*[A].obj G).obj.map ((Scheme.Etale.isTerminalMkId X).from
      (Scheme.Etale.mk j)).op) := by
  rw [lowerStar_obj_val_map]
  infer_instance

/-- For a sheaf `M` on `X`, the unit `M ⟶ j_* j^* M` of the restriction along the open immersion
`j` is an isomorphism on the sections over `U`. -/
instance isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
    (M : Sheaf X.smallEtaleTopology A) :
    IsIso (((openImmersionRestrictionLowerStarAdjunction A j).unit.app M).hom.app
      (op (Scheme.Etale.mk j))) :=
  inferInstanceAs (IsIso (𝟙 _ ≫ M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
    inferInstance trivial).counit.app (Scheme.Etale.mk j)).op ≫ 𝟙 _))

/-- The restriction `Γ(X, M) ⟶ M(U)` from the global sections to the sections over `U` is the
restriction along the map from `U` to the terminal étale `X`-scheme, preceded by the isomorphism
`Γ(X, M) ≅ M(X)`. -/
lemma ΓRes_eq (M : Sheaf X.smallEtaleTopology A) :
    M.ΓRes (op (Scheme.Etale.mk j)) =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) ≫
        M.obj.map ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)).op :=
  (M.ΓRes_map _).symm

instance (M : Sheaf X.smallEtaleTopology A) : IsIso (M.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
  M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.Etale.isTerminalMkId X).op

/-- If the unit `M ⟶ j_* j^* M` of the restriction along the open immersion `j` is a split
epimorphism, the restriction `Γ(X, M) ⟶ M(U)` of global sections is a split epimorphism. In the
square

```
M(X) ───────────▶ M(U)
 │ η_X               │ η_U ≅
 ▼                   ▼
(j_* j^* M)(X) ──≅──▶ (j_* j^* M)(U)
```

the bottom map and `η_U` are isomorphisms and `η_X` is split by the section of the unit. -/
lemma isSplitEpi_ΓRes_of_isSplitEpi_unit (M : Sheaf X.smallEtaleTopology A)
    [IsSplitEpi ((openImmersionRestrictionLowerStarAdjunction A j).unit.app M)] :
    IsSplitEpi (M.ΓRes (op (Scheme.Etale.mk j))) := by
  set η := (openImmersionRestrictionLowerStarAdjunction A j).unit.app M
  set t := (Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)
  set σ := section_ η
  have hσ : σ.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ η.hom.app (op (Scheme.Etale.mk (𝟙 X))) =
      𝟙 _ := by
    have h := (sheafToPresheaf _ A).congr_map (IsSplitEpi.id η)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact congr_app h _
  have hsq : M.obj.map t.op ≫ η.hom.app (op (Scheme.Etale.mk j)) =
      η.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
        ((j)_*[A].obj (openImmersionRestriction A j |>.obj M)).obj.map t.op :=
    η.hom.naturality t.op
  have : IsSplitEpi (M.obj.map t.op) :=
    ⟨⟨η.hom.app (op (Scheme.Etale.mk j)) ≫
        inv (((j)_*[A].obj (openImmersionRestriction A j |>.obj M)).obj.map t.op) ≫
          σ.hom.app (op (Scheme.Etale.mk (𝟙 X))), by
      rw [← cancel_mono (η.hom.app (op (Scheme.Etale.mk j))), assoc, assoc, hsq]
      simp only [assoc]
      rw [reassoc_of% hσ, IsIso.inv_hom_id, comp_id, id_comp]⟩⟩
  rw [ΓRes_eq]
  infer_instance

end Restriction

section Concrete

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJX hJZ in
/-- For an injective étale sheaf `I` on `X` and a closed immersion `i : Z ⟶ X` with open
complement `U`, the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism: the restriction
`I ⟶ j_* j^* I` to the open part is a split epimorphism
(`AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`). -/
theorem isSplitEpi_ΓRes_openComplement_of_injective (I : Sheaf X.smallEtaleTopology A)
    [Injective I] : IsSplitEpi (I.ΓRes (op (Scheme.Etale.mk i.openComplement.ι))) := by
  have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A i.openComplement.ι i
    i.range_eq_compl_range_openComplement_ι I
  have : IsSplitEpi ((openImmersionRestrictionLowerStarAdjunction A i.openComplement.ι).unit.app
      I) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A _)
      (openImmersionRestrictionLowerStarAdjunction A i.openComplement.ι)]
    infer_instance
  exact isSplitEpi_ΓRes_of_isSplitEpi_unit A _ I


/-- The sequence `Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I)` of complexes of a complex `I` of étale sheaves:
the inclusion of the sections with support in `Z`, and the restriction to the open complement
`U` of `Z`. -/
@[simps]
noncomputable def sectionsWithSupportShortComplex
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (Sheaf.ΓSupportι X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))) _).app I)
    ((NatTrans.mapHomologicalComplex (Sheaf.natTransΓRes X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))) _).app I)
    (by ext n; simp)

include hJX hJZ in
/-- For a complex `I` of injective sheaves, `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is a short
exact sequence of complexes: degreewise, `Γ_Z` is the kernel of the restriction, which is a
split epimorphism (`AlgebraicGeometry.Etale.isSplitEpi_ΓRes_openComplement_of_injective`). -/
theorem shortExact_sectionsWithSupportShortComplex
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    (sectionsWithSupportShortComplex A i I).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have := isSplitEpi_ΓRes_openComplement_of_injective A i (I.X n)
  have hκ := KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes X.smallEtaleTopology A
    (op (Scheme.Etale.mk i.openComplement.ι)))) ((evaluation _ A).obj (I.X n))
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hκ) ?_ ?_
  · change Mono ((Sheaf.ΓSupportι X.smallEtaleTopology A _).app (I.X n))
    infer_instance
  · change Epi ((I.X n).ΓRes _)
    infer_instance

end Concrete

end Etale

end AlgebraicGeometry
