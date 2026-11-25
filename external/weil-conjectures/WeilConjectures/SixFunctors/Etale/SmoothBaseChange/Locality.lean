/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.Mathlib.CategoryTheory.EpiMono
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Étale locality and composition of the base-change map

Two formal properties of the base-change map of the smooth base change theorem (blueprint
subsection `prose-08-06`), and their consequences for the base-change property `BC(p, Λ, q)` of
`AlgebraicGeometry.Etale.BaseChangeProperty`, used to reduce the smooth base change theorem to
smooth morphisms of relative dimension one:

- composition (blueprint `lemma-identity-pasting--2`, Stacks 0EZS): the base-change map of
  a composite square is the composite of the base-change maps of the two squares, so it is an
  isomorphism when they are, both for the derived base-change map and degreewise; in particular
  the derived base-change map of a square whose horizontal sides are isomorphisms is an
  isomorphism, as pasting it with the inverse square gives an identity square;
- étale locality (blueprint `prose-08-06`, Stacks 0EZR): if `X` is covered by étale
  `U_i ⟶ X` such that `U_i ⟶ S` factors as `f_i : U_i ⟶ V_i` followed by an étale
  `V_i ⟶ S`, the base-change map of a square on `X ⟶ S` is an isomorphism as soon as those of
  the induced squares on the `f_i` are, for the base-change map of sheaves, for the derived
  base-change map and for the degree-`q` base-change maps.

The proofs use the identification of the derived base-change morphism
`AlgebraicGeometry.Etale.baseChange` with `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`
(`AlgebraicGeometry.Etale.baseChange_eq_derivedBaseChangeMapPlus`) to access its pasting laws,
étale base change for the derived pushforward
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`), and the fact that the
restrictions along a jointly surjective family reflect isomorphisms
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_paste_horiz`,
  `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_paste_horiz`: composition.
- `AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_etale_cover`,
  `AlgebraicGeometry.Etale.isIso_baseChange_app_of_etale_cover`,
  `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale_cover`: étale locality.
- `AlgebraicGeometry.Etale.BaseChangeProperty.of_etale_cover`: étale locality of `BC(p, Λ, q)`.
- `AlgebraicGeometry.Etale.BaseChangeProperty.comp`: stability of `BC(p, Λ, q)` under
  composition.
- `AlgebraicGeometry.Etale.baseChangeProperty_of_isIso`: isomorphisms satisfy `BC(p, Λ, q)`.
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_inverses`: the derived base-change map of a
  square whose horizontal sides are isomorphisms is an isomorphism.

## Implementation notes

Several statements below are routed through auxiliary lemmas about abstract functors
(`isIso_whiskerLeft_whiskerRight_app_iff` and its companions) rather than through definitional
unfolding: comparing an object `(A ⋙ B).obj X` with `B.obj (A.obj X)` for the concrete derived
functors makes the kernel unfold them, while the instances of the abstract lemmas are checked
syntactically.

## References

- Stacks Project, Lemma 59.86.1, <https://stacks.math.columbia.edu/tag/0EZR>
- Stacks Project, Lemma 59.86.2, <https://stacks.math.columbia.edu/tag/0EZS>
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Composition

variable {X Z S T Y₂ Y : Scheme.{u}} {g : T ⟶ S} {p₂ : Z ⟶ S} {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z}
  {p₁ : X ⟶ Z} {e₁ : Y ⟶ Y₂} {h₁ : Y ⟶ X}

/-- **The base-change map of a composite square.** For a square on `p₂` along `g` and a square on
`p₁` along the base change `h₂` of `g`, the derived base-change map of the composite square on
`p₁ ≫ p₂` is the pullback along `p₁` of the base-change map of the first square followed by the
base-change map of the second one, modulo the composition isomorphisms of the pullbacks.
This is the derived exchange morphism of blueprint `definition-derived-base-change-map--1` read
through the pasting law `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz`. -/
theorem Etale.baseChange_app_paste_horiz (sq₂ : CommSq e₂ h₂ g p₂) (sq₁ : CommSq e₁ h₁ h₂ p₁)
    (sq : CommSq (e₁ ≫ e₂) h₁ g (p₁ ≫ p₂))
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p₁ p₂).hom.app
          (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K) ≫
        ((p₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁).app
          (((e₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) ≫
        ((h₁)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ e₂).inv.app K) := by
  simp only [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have := NatTrans.congr_app
    (Etale.derivedBaseChangeMapPlus_paste_horiz (ModuleCat.{u + 1} Λ) sq₂ sq₁ sq) K
  simpa using this

/-- Blueprint `lemma-identity-pasting--2`: base change for a composite square. If the
derived base-change map of the square on `p₂` is an isomorphism at `K` and the one of the
square on `p₁` is an isomorphism at the pullback `e₂^* K`, then the derived base-change map of
the composite square is an isomorphism at `K`. The composite square is any square whose sides
are the composites `e₁ ≫ e₂` and `p₁ ≫ p₂`. -/
@[stacks 0EZS]
theorem Etale.isIso_baseChange_app_of_paste_horiz {e : Y ⟶ T} {p : X ⟶ S}
    (sq₂ : CommSq e₂ h₂ g p₂) (sq₁ : CommSq e₁ h₁ h₂ p₁) (sq : CommSq e h₁ g p)
    (he : e₁ ≫ e₂ = e) (hp : p₁ ≫ p₂ = p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK₂ : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K))
    (hK₁ : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁).app
      (((e₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  subst he hp
  rw [Etale.baseChange_app_paste_horiz Λ sq₂ sq₁ sq K]
  infer_instance

/-- Blueprint `lemma-identity-pasting--2`, degreewise: the statement of
`AlgebraicGeometry.Etale.isIso_baseChange_app_of_paste_horiz` for the degree-`q` homology of
the derived base-change maps. The pullback along `p₁` is exact, so it preserves isomorphisms on
cohomology sheaves. -/
@[stacks 0EZS]
theorem Etale.isIso_homologyFunctor_map_baseChange_app_of_paste_horiz {e : Y ⟶ T} {p : X ⟶ S}
    (sq₂ : CommSq e₂ h₂ g p₂) (sq₁ : CommSq e₁ h₁ h₂ p₁) (sq : CommSq e h₁ g p)
    (he : e₁ ≫ e₂ = e) (hp : p₁ ≫ p₂ = p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ)
    (hK₂ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K)))
    (hK₁ : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁).app
        (((e₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K)) := by
  subst he hp
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      (((p₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K))) :=
    (NatIso.isIso_map_iff (((p₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      q) _).1 (by dsimp; infer_instance)
  rw [Etale.baseChange_app_paste_horiz Λ sq₂ sq₁ sq K]
  simp only [Functor.map_comp]
  infer_instance

/- Generic forms of the identifications between the components of whiskered natural
transformations, stated for abstract functors so that their instances at the concrete derived
functors are checked syntactically: comparing `(A ⋙ B).obj X` with `B.obj (A.obj X)` for the
concrete functors makes the kernel unfold the derived functors. -/
omit [CommRing Λ] in
private lemma isIso_whiskerLeft_whiskerRight_app_iff {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜]
    [Category* ℬ] [Category* 𝒞] [Category* 𝒟] (E : 𝒜 ⥤ ℬ) {P Q : ℬ ⥤ 𝒞} (α : P ⟶ Q)
    (Hh : 𝒞 ⥤ 𝒟) (X : 𝒜) :
    IsIso ((Functor.whiskerLeft E (Functor.whiskerRight α Hh)).app X) ↔
      IsIso (Hh.map (α.app (E.obj X))) :=
  Iff.rfl

omit [CommRing Λ] in
private lemma isIso_map_app_comp_obj_iff {𝒜 ℬ ℬ' 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* ℬ'] [Category* 𝒞] [Category* 𝒟] (E₁ : 𝒜 ⥤ ℬ') (E₂ : ℬ' ⥤ ℬ) {P Q : ℬ ⥤ 𝒞}
    (α : P ⟶ Q) (Hh : 𝒞 ⥤ 𝒟) (X : 𝒜) :
    IsIso (Hh.map (α.app ((E₁ ⋙ E₂).obj X))) ↔ IsIso (Hh.map (α.app (E₂.obj (E₁.obj X)))) :=
  Iff.rfl

omit [CommRing Λ] in
private lemma isIso_map_app_iff_of_iso {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* 𝒞] [Category* 𝒟] {E₁ E₂ : 𝒜 ⥤ ℬ} (ι : E₁ ≅ E₂) {P Q : ℬ ⥤ 𝒞} (α : P ⟶ Q)
    (Hh : 𝒞 ⥤ 𝒟) (X : 𝒜) :
    IsIso (Hh.map (α.app (E₁.obj X))) ↔ IsIso (Hh.map (α.app (E₂.obj X))) :=
  NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight α Hh) (ι.app X)

/-- The degree-`q` base-change map at a sheaf `F` is an isomorphism if and only if the degree-`q`
homology of the derived base-change map at `F` placed in degree `0` is. -/
theorem Etale.isIso_baseChangeHomologyMap_iff {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyNatTrans_eq]
  exact isIso_whiskerLeft_whiskerRight_app_iff _ _ _ _

/-- Blueprint `lemma-identity-pasting--2`, for the degree-`q` base-change maps of an abelian
sheaf `F`: if `p₂⁻¹ R^q g_* F ⟶ R^q h₂_* e₂⁻¹ F` and
`p₁⁻¹ R^q h₂_* (e₂⁻¹ F) ⟶ R^q h₁_* e₁⁻¹ e₂⁻¹ F` are isomorphisms, so is the base-change map
`(p₁ ≫ p₂)⁻¹ R^q g_* F ⟶ R^q h₁_* (e₁ ≫ e₂)⁻¹ F` of the composite square. -/
@[stacks 0EZS]
theorem Etale.isIso_baseChangeHomologyMap_of_paste_horiz {e : Y ⟶ T} {p : X ⟶ S}
    (sq₂ : IsPullback e₂ h₂ g p₂) (sq₁ : IsPullback e₁ h₁ h₂ p₁) (sq : IsPullback e h₁ g p)
    (he : e₁ ≫ e₂ = e) (hp : p₁ ≫ p₂ = p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF₂ : IsIso (Etale.baseChangeHomologyMap Λ sq₂ q F))
    (hF₁ : IsIso (Etale.baseChangeHomologyMap Λ sq₁ q ((e₂)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  rw [Etale.isIso_baseChangeHomologyMap_iff] at hF₂ hF₁ ⊢
  refine Etale.isIso_homologyFunctor_map_baseChange_app_of_paste_horiz Λ sq₂.toCommSq
    sq₁.toCommSq sq.toCommSq he hp _ q hF₂ ?_
  refine (isIso_map_app_comp_obj_iff _ _ _ _ _).1
    ((isIso_map_app_iff_of_iso
      ((((e₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)) _ _ _).2
      ((isIso_map_app_comp_obj_iff _ _ _ _ _).2 hF₁))

end Composition

section IsoSquares

variable {X Z S T Y₂ Y : Scheme.{u}} {g : T ⟶ S} {p₂ : Z ⟶ S} {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z}
  {p₁ : X ⟶ Z} {e₁ : Y ⟶ Y₂} {h₁ : Y ⟶ X}

/-- The pasting law `AlgebraicGeometry.Etale.baseChange_app_paste_horiz` for a composite square
whose horizontal sides are only equal to the composites `e₁ ≫ e₂` and `p₁ ≫ p₂`; the
composition isomorphisms of the pullbacks are taken along these sides. -/
theorem Etale.baseChange_app_paste_horiz_of_eq (sq₂ : CommSq e₂ h₂ g p₂)
    (sq₁ : CommSq e₁ h₁ h₂ p₁) {e : Y ⟶ T} {p : X ⟶ S} (sq : CommSq e h₁ g p)
    (he : e₁ ≫ e₂ = e) (hp : p₁ ≫ p₂ = p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) p₁ p₂ p hp.symm).hom.app
          (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K) ≫
        ((p₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₂).app K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁).app
          (((e₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) ≫
        ((h₁)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ e₂ e he.symm).inv.app K) := by
  subst he hp
  exact Etale.baseChange_app_paste_horiz Λ sq₂ sq₁ sq K

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived base-change map of an identity square is an isomorphism
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_id`). -/
lemma Etale.isIso_baseChange_app_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  have : IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus, Etale.derivedBaseChangeMapPlus_id]
    infer_instance
  infer_instance

/- The inverses of the horizontal sides are given explicitly rather than through `inv`: with
`inv` the kernel unfolds the derived functors when checking the pasted squares. -/
private lemma isSplitEpi_baseChange_app_upperStar_upperStar (sq : CommSq g' f' f g)
    (i' : X ⟶ X') (i : Y ⟶ Y') (hi'₁ : g' ≫ i' = 𝟙 X') (hi'₂ : i' ≫ g' = 𝟙 X)
    (hi₁ : g ≫ i = 𝟙 Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsSplitEpi ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app
      (((i')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
        (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) := by
  have sqi : CommSq i' f f' i := ⟨by
    calc i' ≫ f' = i' ≫ f' ≫ g ≫ i := by rw [hi₁, Category.comp_id]
      _ = i' ≫ g' ≫ f ≫ i := by rw [← Category.assoc f' g i, ← sq.w, Category.assoc]
      _ = f ≫ i := by rw [← Category.assoc, hi'₂, Category.id_comp]⟩
  have sqid : CommSq (𝟙 X') f' f' (𝟙 Y') := ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hp := Etale.baseChange_app_paste_horiz_of_eq Λ sqi sq sqid hi'₁ hi₁
    (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)
  have hiso := Etale.isIso_baseChange_app_id Λ f' sqid
    (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)
  rw [hp] at hiso
  exact isSplitEpi_of_isIso_comp _ _ _ _ hiso

/-- The derived base-change map of a square whose horizontal sides `g'` and `g` have inverses
`i'` and `i` is a split epimorphism: pasting the square with the inverse square gives an
identity square, whose derived base-change map is an isomorphism. -/
lemma Etale.isSplitEpi_baseChange_app_of_inverses (sq : CommSq g' f' f g) (i' : X ⟶ X')
    (i : Y ⟶ Y') (hi'₁ : g' ≫ i' = 𝟙 X') (hi'₂ : i' ≫ g' = 𝟙 X) (hi₁ : g ≫ i = 𝟙 Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsSplitEpi ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  have := isSplitEpi_baseChange_app_upperStar_upperStar Λ sq i' i hi'₁ hi'₂ hi₁ K
  let e : K ≅ ((i')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
      (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) :=
    (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).symm.app K ≪≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i' g' (𝟙 X) hi'₂.symm).app K
  have hn := (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).naturality e.hom
  have key : (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K =
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⋙
          ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus).map e.hom ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app _ ≫
        (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
          ((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus).map e.inv := by
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [key]
  infer_instance

/-- The derived base-change map of a square whose horizontal sides `g'` and `g` have inverses
`i'` and `i` is an isomorphism. Pasting the square with the inverse square gives an identity
square, so the pullback along `i` of the base-change map is a split monomorphism; it is also a
split epimorphism by `AlgebraicGeometry.Etale.isSplitEpi_baseChange_app_of_inverses`, and the
pullback along `i` reflects isomorphisms. -/
lemma Etale.isIso_baseChange_app_of_inverses (sq : CommSq g' f' f g) (i' : X ⟶ X')
    (i : Y ⟶ Y') (hi'₁ : g' ≫ i' = 𝟙 X') (hi'₂ : i' ≫ g' = 𝟙 X) (hi₁ : g ≫ i = 𝟙 Y')
    (hi₂ : i ≫ g = 𝟙 Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K) := by
  have sqi : CommSq i' f f' i := ⟨by
    calc i' ≫ f' = i' ≫ f' ≫ g ≫ i := by rw [hi₁, Category.comp_id]
      _ = i' ≫ g' ≫ f ≫ i := by rw [← Category.assoc f' g i, ← sq.w, Category.assoc]
      _ = f ≫ i := by rw [← Category.assoc, hi'₂, Category.id_comp]⟩
  have sqid : CommSq (𝟙 X) f f (𝟙 Y) := ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hp := Etale.baseChange_app_paste_horiz_of_eq Λ sq sqi sqid hi'₂ hi₂ K
  have hiso := Etale.isIso_baseChange_app_id Λ f sqid K
  rw [hp] at hiso
  have := Etale.isSplitEpi_baseChange_app_of_inverses Λ sq i' i hi'₁ hi'₂ hi₁ K
  have hx := isIso_of_isIso_comp_of_isSplitEpi _ _ _ _ hiso
  let e : 𝟭 _ ≅ ((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
      ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
    (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y').symm ≪≫
      Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g i (𝟙 Y') hi₁.symm
  exact (NatIso.isIso_map_iff e ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K)).2
    (Functor.map_isIso ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus _)

end IsoSquares

section Locality

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

omit [CommRing Λ] in
private lemma isIso_of_isIso_comp₄ {𝒞 : Type*} [Category* 𝒞] {W₀ W₁ W₂ W₃ W₄ : 𝒞}
    (x : W₀ ⟶ W₁) (y : W₁ ⟶ W₂) (z : W₂ ⟶ W₃) (w : W₃ ⟶ W₄) [IsIso x] [IsIso z] [IsIso w]
    (h : IsIso (x ≫ y ≫ z ≫ w)) : IsIso y := by
  have : IsIso (y ≫ z ≫ w) := IsIso.of_isIso_comp_left x _
  have : IsIso ((y ≫ z) ≫ w) := by rwa [Category.assoc]
  have : IsIso (y ≫ z) := IsIso.of_isIso_comp_right _ w
  exact IsIso.of_isIso_comp_right y z

/-- Let `a : U ⟶ X` be étale and let `sqa` be the base change of the Cartesian square `sq` along
`a`. The pullback along `a` of the derived base-change map of `sq`, followed by the base-change
map of `sqa`, is the base-change map of the composite square; since the base-change map of `sqa`
is an isomorphism (étale base change), the degree-`n` homology of the pullback of the
base-change map of `sq` is invertible as soon as the one of the composite square is. -/
private lemma isIso_homologyFunctor_map_upperStar_baseChange_app {U Y' : Scheme.{u}}
    (sq : IsPullback e h g p) (a : U ⟶ X) [Etale a] (d : Y' ⟶ Y) (h' : Y' ⟶ U)
    (sqa : IsPullback d h' h a)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (hK : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqa.toCommSq.horiz_comp sq.toCommSq)).app K))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K))) := by
  rw [Etale.baseChange_app_paste_horiz Λ sq.toCommSq sqa.toCommSq] at hK
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqa.toCommSq).app
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sqa
    infer_instance
  simp only [Functor.map_comp] at hK
  exact isIso_of_isIso_comp₄ _ _ _ _ hK

omit [CommRing Λ] in
private lemma isIso_map_map_iff {𝒜 ℬ ℬ' 𝒞 : Type*} [Category* 𝒜] [Category* ℬ] [Category* ℬ']
    [Category* 𝒞] {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ 𝒞} {G₁ : 𝒜 ⥤ ℬ'} {G₂ : ℬ' ⥤ 𝒞}
    (ι : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) {K L : 𝒜} (φ : K ⟶ L) :
    IsIso (F₂.map (F₁.map φ)) ↔ IsIso (G₂.map (G₁.map φ)) :=
  NatIso.isIso_map_iff ι φ

variable {ι : Type u} {U V T' Y' : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)]
  (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
  (f : ∀ i, U i ⟶ V i) (b : ∀ i, V i ⟶ S) [∀ i, Etale (b i)] (w : ∀ i, f i ≫ b i = a i ≫ p)
  (c : ∀ i, T' i ⟶ T) (g' : ∀ i, T' i ⟶ V i) (hc : ∀ i, IsPullback (c i) (g' i) g (b i))
  (e' : ∀ i, Y' i ⟶ T' i) (h' : ∀ i, Y' i ⟶ U i)
  (sqi : ∀ i, IsPullback (e' i) (h' i) (g' i) (f i))

omit [∀ i, Etale (a i)] [∀ i, Etale (b i)] in
include w hc sqi in
/-- The base change of the Cartesian square `sq` along `a i`, its top side being the map
`Y' i ⟶ Y` induced by the Cartesian square `sqi i` on `f i`. -/
private lemma exists_isPullback_upperStar (sq : IsPullback e h g p) (i : ι) :
    ∃ (d : Y' i ⟶ Y), IsPullback d (h' i) h (a i) ∧ e' i ≫ c i = d ≫ e := by
  let d := sq.lift (e' i ≫ c i) (h' i ≫ a i) (by
    rw [Category.assoc, (hc i).w, ← Category.assoc, (sqi i).w, Category.assoc, w i,
      Category.assoc])
  have hd : d ≫ e = e' i ≫ c i := sq.lift_fst _ _ _
  refine ⟨d, IsPullback.of_right ?_ (sq.lift_snd _ _ _) sq, hd.symm⟩
  rw [hd, ← w i]
  exact (sqi i).paste_horiz (hc i)

include ha w hc in
/-- Blueprint `prose-08-06` (2), degreewise: étale locality of the derived base-change
map on cohomology sheaves. Let `a i : U i ⟶ X` be a jointly surjective family of étale morphisms
such that `U i ⟶ X ⟶ S` factors as `f i : U i ⟶ V i` followed by an étale `b i : V i ⟶ S`, and
let `sqi i` be the base change of the Cartesian square `sq` along `V i ⟶ S` restricted to
`U i`. If the degree-`n` homology of the base-change map of `sqi i` at the restriction of `K` is
invertible for all `i`, then so is the one of `sq` at `K`. -/
@[stacks 0EZR]
theorem Etale.isIso_homologyFunctor_map_baseChange_app_of_etale_cover (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (hK : ∀ i, IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqi i).toCommSq).app
        (((c i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) := by
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha _
    fun i ↦ ?_
  refine (isIso_map_map_iff
    (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n) _).2 ?_
  obtain ⟨d, sqa, hd⟩ := exists_isPullback_upperStar a f b w c g' hc e' h' sqi sq i
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) (hc i).toCommSq).app K) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ (hc i)
    infer_instance
  exact isIso_homologyFunctor_map_upperStar_baseChange_app Λ sq (a i) d (h' i) sqa K n
    (Etale.isIso_homologyFunctor_map_baseChange_app_of_paste_horiz Λ (hc i).toCommSq
      (sqi i).toCommSq _ hd (w i) K n inferInstance (hK i))

include ha w hc in
/-- Blueprint `prose-08-06` (2): étale locality of the derived base-change map. In the
situation of `AlgebraicGeometry.Etale.isIso_homologyFunctor_map_baseChange_app_of_etale_cover`,
if the derived base-change maps of the squares `sqi i` at the restrictions of `K` are
isomorphisms, so is the derived base-change map of `sq` at `K`. -/
@[stacks 0EZR]
theorem Etale.isIso_baseChange_app_of_etale_cover (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ i, IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqi i).toCommSq).app
      (((c i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  (DerivedCategory.Plus.isIso_iff _).2 fun n ↦
    Etale.isIso_homologyFunctor_map_baseChange_app_of_etale_cover Λ a ha f b w c g' hc e' h' sqi
      sq K n fun _ ↦ inferInstance

include ha w hc in
/-- Blueprint `prose-08-06` (3): étale locality of the degree-`q` base-change map
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`. In the situation of
`AlgebraicGeometry.Etale.isIso_homologyFunctor_map_baseChange_app_of_etale_cover`, if the
degree-`q` base-change maps of the squares `sqi i` at the restrictions `F|_{T' i}` are
isomorphisms, so is the one of `sq` at `F`. -/
@[stacks 0EZR]
theorem Etale.isIso_baseChangeHomologyMap_of_etale_cover (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsIso (Etale.baseChangeHomologyMap Λ (sqi i) q
      ((c i)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  rw [Etale.isIso_baseChangeHomologyMap_iff]
  refine Etale.isIso_homologyFunctor_map_baseChange_app_of_etale_cover Λ a ha f b w c g' hc e'
    h' sqi sq _ q fun i ↦ ?_
  have hFi := hF i
  rw [Etale.isIso_baseChangeHomologyMap_iff] at hFi
  exact (isIso_map_app_comp_obj_iff _ _ _ _ _).1
    ((isIso_map_app_iff_of_iso
      ((((c i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)) _ _ _).2
      ((isIso_map_app_comp_obj_iff _ _ _ _ _).2 hFi))

omit [∀ i, Etale (a i)] [∀ i, Etale (b i)] in
private lemma isIso_baseChangeMap_app_of_paste_horiz {X₁ Z₁ Y₁ Y₂ : Scheme.{u}} {p₂ : Z₁ ⟶ S}
    {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z₁} {p₁ : X₁ ⟶ Z₁} {e₁ : Y₁ ⟶ Y₂} {h₁ : Y₁ ⟶ X₁}
    {e₀ : Y₁ ⟶ T} {p₀ : X₁ ⟶ S} (sq₂ : CommSq e₂ h₂ g p₂) (sq₁ : CommSq e₁ h₁ h₂ p₁)
    (sq₀ : CommSq e₀ h₁ g p₀) (he : e₁ ≫ e₂ = e₀) (hp : p₁ ≫ p₂ = p₀)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF₂ : IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq₂).app F))
    (hF₁ : IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq₁).app
      ((e₂)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq₀).app F) := by
  subst he hp
  rw [Etale.baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} Λ) sq₂ sq₁ sq₀ F]
  infer_instance

include ha w hc in
/-- Blueprint `prose-08-06` (1): étale locality of the base-change map
`p⁻¹ g_* F ⟶ h_* e⁻¹ F` of sheaves. In the situation of
`AlgebraicGeometry.Etale.isIso_homologyFunctor_map_baseChange_app_of_etale_cover`, if the
base-change maps of the squares `sqi i` at the restrictions `F|_{T' i}` are isomorphisms, so is
the one of `sq` at `F`. -/
@[stacks 0EZR]
theorem Etale.isIso_baseChangeMap_app_of_etale_cover (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) (sqi i).toCommSq).app
      ((c i)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) := by
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha _
    fun i ↦ ?_
  obtain ⟨d, sqa, hd⟩ := exists_isPullback_upperStar a f b w c g' hc e' h' sqi sq i
  have : Etale d := MorphismProperty.of_isPullback sqa.flip inferInstance
  have : Etale (c i) := MorphismProperty.of_isPullback (hc i).flip inferInstance
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sqa.toCommSq) :=
    Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ) sqa.flip
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) (hc i).toCommSq) :=
    Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ) (hc i).flip
  have hout := isIso_baseChangeMap_app_of_paste_horiz Λ (hc i).toCommSq
    (sqi i).toCommSq (sqa.toCommSq.horiz_comp sq.toCommSq) hd (w i) F inferInstance (hF i)
  rw [Etale.baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} Λ) sq.toCommSq sqa.toCommSq] at hout
  exact isIso_of_isIso_comp₄ _ _ _ _ hout

end Locality

variable {X S : Scheme.{u}} {p : X ⟶ S}

/-- Etale locality of the base-change property (degree `q`). This is a consequence of
blueprint `prose-08-06` (Stacks 0EZR), which is stated for a single Cartesian square
and a single sheaf.

Let `a_i : U_i ⟶ X` be a jointly surjective family of étale morphisms such that each composite
`U_i ⟶ X ⟶ S` factors as `f_i : U_i ⟶ V_i` followed by an étale morphism `b_i : V_i ⟶ S`. If
the base-change property `BC(f_i, Λ, q)` holds for every `i`, then `BC(p, Λ, q)` holds: the
restriction of the base-change map of a square on `p` to `U_i` is the base-change map of the
square on `f_i` obtained by base change along `V_i ⟶ S`, and a morphism of étale sheaves
which is an isomorphism on an étale covering is an isomorphism. -/
@[stacks 0EZR]
theorem Etale.BaseChangeProperty.of_etale_cover {q : ℤ} {ι : Type u} {U V : ι → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)] (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    (f : ∀ i, U i ⟶ V i) (b : ∀ i, V i ⟶ S) [∀ i, Etale (b i)] (w : ∀ i, f i ≫ b i = a i ≫ p)
    (hf : ∀ i, Etale.BaseChangeProperty Λ (f i) q) :
    Etale.BaseChangeProperty Λ p q := by
  intro T Y g e h _ _ sq F
  exact Etale.isIso_baseChangeHomologyMap_of_etale_cover Λ a ha f b w
    (fun i ↦ pullback.snd (b i) g) (fun i ↦ pullback.fst (b i) g)
    (fun i ↦ (IsPullback.of_hasPullback (b i) g).flip)
    (fun i ↦ pullback.snd (f i) (pullback.fst (b i) g))
    (fun i ↦ pullback.fst (f i) (pullback.fst (b i) g))
    (fun i ↦ (IsPullback.of_hasPullback _ _).flip) sq q F fun i ↦ hf i _ _ _ _ _

/-- Base change for composites (degree `q`). This is a consequence of blueprint
`lemma-identity-pasting--2` (Stacks 0EZS), which is stated for a single composite square
and a single sheaf.

If `BC(p₁, Λ, q)` and `BC(p₂, Λ, q)` hold, then so does `BC(p₁ ≫ p₂, Λ, q)`: a Cartesian square
on `p₁ ≫ p₂` along a quasi-compact quasi-separated `g` is the pasting of a Cartesian square on
`p₂` along `g` and a Cartesian square on `p₁` along the base change of `g`, which is again
quasi-compact quasi-separated, and the base-change map of the pasted square is the composite
of the base-change maps of the two squares. -/
@[stacks 0EZS]
theorem Etale.BaseChangeProperty.comp {Z : Scheme.{u}} {p₁ : X ⟶ Z} {p₂ : Z ⟶ S} {q : ℤ}
    (h₁ : Etale.BaseChangeProperty Λ p₁ q) (h₂ : Etale.BaseChangeProperty Λ p₂ q) :
    Etale.BaseChangeProperty Λ (p₁ ≫ p₂) q := by
  intro T Y g e h _ _ sq F
  have sq₂ : IsPullback (pullback.snd p₂ g) (pullback.fst p₂ g) g p₂ :=
    (IsPullback.of_hasPullback p₂ g).flip
  let e₁ : Y ⟶ pullback p₂ g := pullback.lift (h ≫ p₁) e (by simpa using sq.w.symm)
  have he : e₁ ≫ pullback.snd p₂ g = e := pullback.lift_snd _ _ _
  have sq₁ : IsPullback e₁ h (pullback.fst p₂ g) p₁ :=
    IsPullback.of_right (he ▸ sq) (pullback.lift_fst _ _ _) sq₂
  exact Etale.isIso_baseChangeHomologyMap_of_paste_horiz Λ sq₂ sq₁ sq he rfl q F
    (h₂ g _ _ sq₂ F) (h₁ _ _ _ sq₁ _)

/-- An isomorphism `p` satisfies the base-change property `BC(p, Λ, q)` in every degree: an
isomorphism is étale, and for a Cartesian square on an étale morphism the derived base-change
map is an isomorphism (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`), hence
so is its degree-`q` homology. -/
theorem Etale.baseChangeProperty_of_isIso (p : X ⟶ S) [IsIso p] (q : ℤ) :
    Etale.BaseChangeProperty Λ p q := by
  intro T Y g e h _ _ sq F
  rw [Etale.isIso_baseChangeHomologyMap_iff, Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  infer_instance

end AlgebraicGeometry
