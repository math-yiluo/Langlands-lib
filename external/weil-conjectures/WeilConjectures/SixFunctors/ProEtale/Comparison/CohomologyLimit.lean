/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.EtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-!
# Continuity of pro-étale cohomology along cofiltered limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an abelian étale sheaf on `S`. Then the
pro-étale cohomology of the sheaves of étale origin `ν^*(F|_{Xᵢ})` is continuous:
`Hᵠ(X_proét, ν^*(F|_X)) = colimᵢ Hᵠ((Xᵢ)_proét, ν^*(F|_{Xᵢ}))`, in every degree `q`. This is the
pro-étale counterpart of the continuity of étale cohomology
(`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`, [Stacks, Tag 09YQ]), to which it
is reduced through the comparison isomorphism `Hᵠ(Y_ét, G) ≃ Hᵠ(Y_proét, ν^* G)`
(`AlgebraicGeometry.ProEtale.bijective_cohomologyComparison`).

The point is that this comparison is natural in `Y`: for a morphism of schemes `g : Z ⟶ Y`, the
pro-étale pullback map on cohomology (`AlgebraicGeometry.ProEtale.cohomologyMap`) corresponds to
the étale one (`AlgebraicGeometry.Etale.cohomologyMap`) under the comparison maps and the
isomorphism `g^* ∘ ν_Y^* ≅ ν_Z^* ∘ g^*` of
`AlgebraicGeometry.ProEtale.comparisonUpperStarUpperStarIso`
(`AlgebraicGeometry.ProEtale.cohomologyMap_cohomologyComparison`).

## Main definitions

- `AlgebraicGeometry.ProEtale.cohomologyMap`: the pullback `Hⁿ(Y_proét, G) ⟶ Hⁿ(Z_proét, g^* G)`
  along a morphism of schemes `g : Z ⟶ Y`.
- `AlgebraicGeometry.ProEtale.cohomologyRestrictOver`: for a morphism `f : Y ⟶ Z` of schemes over
  `S`, the restriction map `Hᵠ(Z_proét, ν^*(F|_Z)) ⟶ Hᵠ(Y_proét, ν^*(F|_Y))`.

## Main results

- `AlgebraicGeometry.ProEtale.exists_cohomologyRestrictOver_eq_of_isLimit`: every pro-étale
  cohomology class on the limit comes from some stage.
- `AlgebraicGeometry.ProEtale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`: a class at a
  stage which vanishes on the limit vanishes at a later stage.
-/

@[expose] public section

universe w w' v₀ u₀ u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme

section Pullback

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The identification `ℤ_Z ≅ g^* ℤ_Y` of constant pro-étale sheaves along a morphism of schemes
`g : Z ⟶ Y`, obtained from the étale one through the comparison: `ℤ_Z ≅ ν_Z^* ℤ_Z ≅
ν_Z^* g^* ℤ_Y ≅ g^* ν_Y^* ℤ_Y ≅ g^* ℤ_Y`, using
`AlgebraicGeometry.ProEtale.constantIntIsoComparisonUpperStar`,
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso` and
`AlgebraicGeometry.ProEtale.comparisonUpperStarUpperStarIso`. -/
noncomputable def upperStarConstantIntIso :
    (constantSheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj
        ((constantSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  constantIntIsoComparisonUpperStar Z ≪≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app _) ≪≫
    (comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} g).symm.app _ ≪≫
    (ProEtale.upperStar AddCommGrpCat.{u + 1} g).mapIso (constantIntIsoComparisonUpperStar Y).symm

/-- The pullback map `Hⁿ(Y_proét, G) ⟶ Hⁿ(Z_proét, g^* G)` on pro-étale cohomology along a
morphism of schemes `g : Z ⟶ Y`: an `Ext`-class out of the constant sheaf `ℤ` is pushed forward
along the exact functor `g^*` and precomposed with
`AlgebraicGeometry.ProEtale.upperStarConstantIntIso`. -/
noncomputable def cohomologyMap (G : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) (n : ℕ) :
    Sheaf.H G n →+ Sheaf.H ((ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj G) n :=
  Sheaf.H.mapFunctor _ (upperStarConstantIntIso g) G n

/-- **Naturality of the comparison in the scheme.** For a morphism of schemes `g : Z ⟶ Y` and an
étale sheaf `G` on `Y`, the square

```
   Hⁿ(Y_ét, G) ────cohomologyComparison────→ Hⁿ(Y_proét, ν^* G)
        │                                          │
        │ Etale.cohomologyMap g                    │ ProEtale.cohomologyMap g, then
        ↓                                          ↓ g^* ν^* G ≅ ν^* g^* G
   Hⁿ(Z_ét, g^* G) ──cohomologyComparison──→ Hⁿ(Z_proét, ν^* g^* G)
```

commutes. -/
lemma cohomologyMap_cohomologyComparison (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H G n) :
    Sheaf.H.map ((comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} g).hom.app G) n
        (cohomologyMap g _ n (cohomologyComparison Y G n x)) =
      cohomologyComparison Z _ n (Etale.cohomologyMap g G n x) := by
  rw [Sheaf.H.map_apply, cohomologyMap, Sheaf.H.mapFunctor_apply, cohomologyComparison_apply,
    cohomologyComparison_apply, Etale.cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_mapExactFunctor_of_iso _ _ _
      (comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} g).symm,
    ← Ext.mapExactFunctor_mapExactFunctor, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  simp only [Iso.symm_hom, Iso.symm_inv, Iso.inv_hom_id_app,
    Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc]
  congr 2
  simp only [upperStarConstantIntIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc, constantIntIsoComparisonUpperStar, Iso.symm_inv]
  rw [← Iso.app_hom (comparisonUpperStarConstantSheafIsoAddCommGrpCat Y), Iso.hom_inv_id_map_assoc,
    Iso.inv_hom_id_app]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

end Pullback

section Restrict

variable {S Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY)
  (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)

/-- For a morphism `f : Y ⟶ Z` of schemes over `S` (with structure maps `pY`, `pZ`), the
restriction map `Hᵠ(Z_proét, ν^*(pZ^* F)) ⟶ Hᵠ(Y_proét, ν^*(pY^* F))` on the pro-étale
cohomology of the sheaves of étale origin `ν^*(F|_Z)`: pullback along `f` followed by the
identifications `f^* ν^* (pZ^* F) ≅ ν^* f^* (pZ^* F) ≅ ν^* (pY^* F)`. -/
noncomputable def cohomologyRestrictOver :
    Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} pZ).obj F)) q →+
      Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} pY).obj F)) q :=
  (Sheaf.H.map ((comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} f).hom.app _ ≫
      (comparisonUpperStar AddCommGrpCat.{u + 1} Y).map
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm).inv.app F)) q).comp
    (cohomologyMap f _ q)

/-- The pro-étale restriction map corresponds to the étale one under the comparison
isomorphisms `Hᵠ(-_ét, G) ≃ Hᵠ(-_proét, ν^* G)`. -/
lemma cohomologyRestrictOver_cohomologyComparison
    (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} pZ).obj F) q) :
    cohomologyRestrictOver pY pZ f hf F q (cohomologyComparison Z _ q y) =
      cohomologyComparison Y _ q (Sheaf.H.map
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm).inv.app F) q
        (Etale.cohomologyMap f _ q y)) := by
  rw [cohomologyRestrictOver, AddMonoidHom.comp_apply, Sheaf.H.map_comp_apply]
  exact (congrArg _ (cohomologyMap_cohomologyComparison f _ q y)).trans
    (cohomologyComparison_map _ _ _ _).symm

end Restrict

/-- The maps induced on sheaf cohomology by the two components of an isomorphism of sheaves are
mutually inverse. -/
lemma _root_.CategoryTheory.Sheaf.H.map_hom_map_inv_apply {C : Type u₀} [Category.{v₀} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    {n : ℕ} (x : Sheaf.H G n) : Sheaf.H.map e.hom n (Sheaf.H.map e.inv n x) = x := by
  rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]

/-- The maps induced on sheaf cohomology by the two components of an isomorphism of sheaves are
mutually inverse. -/
lemma _root_.CategoryTheory.Sheaf.H.map_inv_map_hom_apply {C : Type u₀} [Category.{v₀} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    {n : ℕ} (x : Sheaf.H F n) : Sheaf.H.map e.inv n (Sheaf.H.map e.hom n x) = x :=
  Sheaf.H.map_hom_map_inv_apply e.symm x

section Limit

variable {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
  {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
  (c : Cone D) (q : ℕ)

/-- **Continuity of pro-étale cohomology, surjectivity.** Let `(Xᵢ)` be a cofiltered system of
qcqs schemes over `S` with affine transition maps and limit `X`, and `F` an abelian étale sheaf
on `S`. Every class in `Hᵠ(X_proét, ν^*(F|_X))` comes from some `Hᵠ((Xᵢ)_proét, ν^*(F|_{Xᵢ}))`.
It is reduced to the étale case `AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`
through `AlgebraicGeometry.ProEtale.cohomologyRestrictOver_cohomologyComparison`. -/
theorem exists_cohomologyRestrictOver_eq_of_isLimit (hc : IsLimit ((Over.forget S).mapCone c))
    (x : Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} c.pt.left).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F)) q) :
    ∃ (i : I) (y : Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} (D.obj i).left).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F)) q),
      cohomologyRestrictOver c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = x := by
  obtain ⟨x', rfl⟩ := (bijective_cohomologyComparison _ _ q).2 x
  obtain ⟨i, y, hy⟩ := (Etale.cohomologyMap_isColimit_of_isLimit F D c hc q).1 x'
  refine ⟨i, cohomologyComparison _ _ q y, ?_⟩
  refine (cohomologyRestrictOver_cohomologyComparison _ _ _ _ F q y).trans (congrArg _ ?_)
  refine (congrArg (Sheaf.H.map _ q) hy).trans ?_
  exact Sheaf.H.map_inv_map_hom_apply ((Etale.upperStarComp AddCommGrpCat.{u + 1}
    (c.π.app i).left (D.obj i).hom c.pt.hom (Over.w _).symm).app F) x'

/-- **Continuity of pro-étale cohomology, injectivity.** Let `(Xᵢ)` be a cofiltered system of
qcqs schemes over `S` with affine transition maps and limit `X`, and `F` an abelian étale sheaf
on `S`. A class in `Hᵠ((Xᵢ)_proét, ν^*(F|_{Xᵢ}))` which vanishes on `X` vanishes on some `Xⱼ`,
`j ⟶ i`. Together with `AlgebraicGeometry.ProEtale.exists_cohomologyRestrictOver_eq_of_isLimit`
this says `Hᵠ(X_proét, ν^*(F|_X)) = colimᵢ Hᵠ((Xᵢ)_proét, ν^*(F|_{Xᵢ}))`. -/
theorem exists_cohomologyRestrictOver_eq_zero_of_isLimit
    (hc : IsLimit ((Over.forget S).mapCone c)) (i : I)
    (y : Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} (D.obj i).left).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F)) q)
    (hy : cohomologyRestrictOver c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = 0) :
    ∃ (j : I) (g : j ⟶ i),
      cohomologyRestrictOver (D.obj j).hom (D.obj i).hom (D.map g).left (Over.w _) F q y = 0 := by
  obtain ⟨y', rfl⟩ := (bijective_cohomologyComparison _ _ q).2 y
  rw [cohomologyRestrictOver_cohomologyComparison, ← map_zero (cohomologyComparison _ _ q)] at hy
  have h := (Sheaf.H.map_hom_map_inv_apply ((Etale.upperStarComp AddCommGrpCat.{u + 1}
    (c.π.app i).left (D.obj i).hom c.pt.hom (Over.w _).symm).app F) _).symm.trans
    ((congrArg _ ((bijective_cohomologyComparison _ _ q).1 hy)).trans (map_zero _))
  obtain ⟨j, g, hg⟩ := (Etale.cohomologyMap_isColimit_of_isLimit F D c hc q).2 i y' h
  refine ⟨j, g, ?_⟩
  rw [cohomologyRestrictOver_cohomologyComparison, hg, map_zero, map_zero]

end Limit

end AlgebraicGeometry.ProEtale
