/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Identity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
public import WeilConjectures.Tactic.ExactModProofs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-!

# The composition isomorphism of the lower shriek for open immersions

For open immersions `j : Y ⟶ X` and `ι : X ⟶ Z` of separated `k`-schemes of finite type, the
composition isomorphism `R(j ≫ ι)_! ≅ Rj_! ⋙ Rι_!` of the lower shriek on bounded constructible
`ℚ̄_ℓ`-complexes is, through the identifications `Rf_! ≅ f_!` of the lower shriek of an open
immersion with the extension by zero, the composition isomorphism `(j ≫ ι)_! ≅ j_! ⋙ ι_!` of the
extensions by zero
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion`
).

The composition isomorphism of the lower shriek is computed by any triangle of compactifications
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`); for the
triangle of the trivial compactifications `Y ⟶[j] X ⟶[𝟙] X`, `X ⟶[ι] Z ⟶[𝟙] Z` and
`Y ⟶[j ≫ ι] Z ⟶[𝟙] Z`, the composition isomorphism of the triangle in the exchange formalism is
the composition isomorphism of the extensions by zero, read through `R(𝟙)_* ≅ 𝟭`
(`CategoryTheory.ExchangeFormalism.compIso_ofComp_hom_app`).

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.ExchangeFormalism

universe w v₁ v u

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

variable (𝒪) in
/-- The triangle of factorizations `X ⟶[i₁] Y ⟶[𝟙] Y`, `Y ⟶[i₂] S ⟶[𝟙] S`, `X ⟶[i] S ⟶[𝟙] S`
of composable morphisms `i₁`, `i₂` of `𝒪` with `i₁ ≫ i₂ = i`, through `q = i₂` and `r = 𝟙`. -/
abbrev ShriekTriangle.ofComp {X Y S : 𝒞} (i₁ : X ⟶ Y) (i₂ : Y ⟶ S) (i : X ⟶ S) [Fact (𝒪 i₁)]
    [Fact (𝒪 i₂)] [Fact (𝒪 i)] (h : i₁ ≫ i₂ = i) : ShriekTriangle 𝒪 X Y S where
  Z₁ := Y
  Z₂ := S
  W := S
  i₁ := i₁
  p₁ := 𝟙 Y
  i₂ := i₂
  p₂ := 𝟙 S
  i := i
  p := 𝟙 S
  q := i₂
  r := 𝟙 S
  i_q := h
  r_p := Category.id_comp _
  w := by simp

/-- **The composition isomorphism of the triangle `ShriekTriangle.ofComp`** is the composition
isomorphism of the extensions by zero, read through `(𝟙)_* ≅ 𝟭`. -/
lemma compIso_ofComp_hom_app {X Y S : 𝒞} (i₁ : X ⟶ Y) (i₂ : Y ⟶ S) (i : X ⟶ S) [Fact (𝒪 i₁)]
    [Fact (𝒪 i₂)] [Fact (𝒪 i)] (h : i₁ ≫ i₂ = i)
    [IsIso (F.baseChange (𝟙 Y) i₂ i₂ (𝟙 S) (ShriekTriangle.ofComp 𝒪 i₁ i₂ i h).w)]
    [IsIso (F.exchange (𝟙 Y) i₂ i₂ (𝟙 S) (ShriekTriangle.ofComp 𝒪 i₁ i₂ i h).w)]
    (K : F.obj X) :
    (F.compIso (ShriekTriangle.ofComp 𝒪 i₁ i₂ i h)).hom.app K =
      (F.pf (𝟙 S)).map ((F.sh i₂).map ((F.pfId Y).hom.app ((F.sh i₁).obj K)) ≫
        (F.shComp' i₁ i₂ i h).inv.app K) := by
  rw [compIso_hom_app]
  dsimp only
  rw [F.exchange_id_horiz i₂, F.pfComp'_id_left_inv_app]
  have n := (F.pfId S).inv.naturality ((F.shComp' i₁ i₂ i h).inv.app K)
  simp only [Functor.id_map] at n
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.comp_obj, Functor.id_obj, Category.id_comp,
    Category.assoc, Functor.map_comp]
  simp only [← Functor.map_comp, ← reassoc_of% n, Iso.inv_hom_id_app, Category.comp_id,
    Functor.id_obj]

end CategoryTheory.ExchangeFormalism

/-- The triangle of compactifications of two open immersions `j`, `ι` by themselves. -/
noncomputable abbrev AlgebraicGeometry.Compactification.Triangle.ofIsOpenImmersion
    {A B C : AlgebraicGeometry.Scheme} (j : A ⟶ B) (ι : B ⟶ C)
    [AlgebraicGeometry.IsOpenImmersion j] [AlgebraicGeometry.IsOpenImmersion ι] :
    AlgebraicGeometry.Compactification.Triangle j ι where
  cf := .ofIsOpenImmersion j
  cg := .ofIsOpenImmersion ι
  cfg := .ofIsOpenImmersion (j ≫ ι)
  q := ι
  p := 𝟙 C
  i_q := rfl
  p_g := Category.id_comp _
  isPullback := IsPullback.id_horiz ι

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

variable {Y X Z : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The diagram chase behind
`boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion`, in abstract
categories. -/
lemma lowerShriekComp_hom_app_of_compIso_aux {A B C : Type*} [Category A] [Category B]
    [Category C] {Lf jf : A ⥤ B} {Lg : B ⥤ C} {jg : B ⥤ C} {Lfg jfg : A ⥤ C} {PX : B ⥤ B}
    {PZ : C ⥤ C} (lsc : Lfg ≅ Lf ⋙ Lg) (a : Lfg ≅ jfg ⋙ PZ)
    (T : (jf ⋙ PX) ⋙ (jg ⋙ PZ) ≅ jfg ⋙ PZ) (If : jf ⋙ PX ≅ Lf) (Ig : jg ⋙ PZ ≅ Lg)
    (ρX : PX ≅ 𝟭 B) (ρZ : PZ ≅ 𝟭 C) (oc : jfg ≅ jf ⋙ jg)
    (hlsc : lsc.hom = a.hom ≫ T.inv ≫ NatTrans.hcomp If.hom Ig.hom)
    (hT : ∀ K, T.hom.app K = PZ.map (jg.map (ρX.hom.app (jf.obj K)) ≫ oc.inv.app K)) (K : A) :
    lsc.hom.app K ≫
        CategoryStruct.comp (Z := jg.obj (jf.obj K))
          (Lg.map (CategoryStruct.comp (Z := jf.obj K) (If.inv.app K) (ρX.hom.app (jf.obj K))))
          (CategoryStruct.comp (Z := jg.obj (jf.obj K)) (Ig.inv.app (jf.obj K))
            (ρZ.hom.app (jg.obj (jf.obj K)))) =
      a.hom.app K ≫
        CategoryStruct.comp (Y := jfg.obj K) (ρZ.hom.app (jfg.obj K)) (oc.hom.app K) := by
  have nI := Ig.inv.naturality (ρX.hom.app (jf.obj K))
  have nρ := ρZ.hom.naturality (oc.inv.app K)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at nI nρ
  rw [hlsc, NatTrans.comp_app, NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc,
    Category.assoc, Category.assoc, ← Lg.map_comp_assoc, Iso.hom_inv_id_app_assoc, reassoc_of% nI]
  erw [Iso.hom_inv_id_app_assoc]
  congr 1
  rw [← cancel_epi (T.hom.app K), Iso.hom_inv_id_app_assoc, hT, Functor.map_comp,
    Category.assoc, reassoc_of% nρ, Iso.inv_hom_id_app]
  simp

/-- The identification `Rj_! ≅ j_!` of an open immersion, at `K`, through the comparison with the
compactification `ofIsOpenImmersion`. -/
lemma boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl_hom_app
    (j : Y ⟶ X) [IsOpenImmersion j.left] (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app K =
      CategoryStruct.comp
        (Y := (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
          boundedConstructibleLowerStar ℓ (𝟙 X)).obj K)
        (Z := (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          j).obj K)
        (NatTrans.app (Iso.inv
          (X := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
            boundedConstructibleLowerStar ℓ (𝟙 X)) (Y := boundedConstructibleLowerShriek ℓ j)
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (Compactification.ofIsOpenImmersion j.left) (compactificationOverField j))) K)
        ((boundedConstructibleLowerStarId ℓ X).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            K)) := by
  rw [← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm]
  simp [boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl]

/-- The identification `Rj_! ≅ j_!` of an open immersion, at `K`, through the comparison with the
compactification `ofIsOpenImmersion`. -/
lemma boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl_hom_app'
    (j : Y ⟶ X) [IsOpenImmersion j.left] (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app K =
      CategoryStruct.comp
        (Y := (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
          boundedConstructibleLowerStar ℓ (𝟙 X)).obj K)
        (Z := (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          j).obj K)
        (NatTrans.app (Iso.hom (X := boundedConstructibleLowerShriek ℓ j)
          (Y := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
            boundedConstructibleLowerStar ℓ (𝟙 X))
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (compactificationOverField j) (Compactification.ofIsOpenImmersion j.left))) K)
        ((boundedConstructibleLowerStarId ℓ X).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            K)) := by
  simp [boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl]

/-- The triangle of factorizations of open immersions `j`, `ι` by themselves, in the exchange
formalism of bounded constructible complexes. -/
noncomputable abbrev openImmersionShriekTriangle (j : Y ⟶ X) (ι : X ⟶ Z) [IsOpenImmersion j.left]
    [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] :=
  ExchangeFormalism.ShriekTriangle.ofComp SepFinType.openImmersion (SepFinType.homMk j)
    (SepFinType.homMk ι) (SepFinType.homMk (j ≫ ι)) rfl

lemma isIso_baseChange_openImmersionShriekTriangle (j : Y ⟶ X) (ι : X ⟶ Z)
    [IsOpenImmersion j.left] [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] :
    IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk ι) (SepFinType.homMk ι)
      (𝟙 (SepFinType.mk Z)) (openImmersionShriekTriangle j ι).w) :=
  isIso_baseChange_triangleShriekTriangle ℓ
    (Compactification.Triangle.ofIsOpenImmersion j.left ι.left)

lemma isIso_exchange_openImmersionShriekTriangle (j : Y ⟶ X) (ι : X ⟶ Z)
    [IsOpenImmersion j.left] [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] :
    haveI := isIso_baseChange_openImmersionShriekTriangle ℓ j ι
    IsIso ((𝔽).exchange (𝟙 (SepFinType.mk X)) (SepFinType.homMk ι) (SepFinType.homMk ι)
      (𝟙 (SepFinType.mk Z)) (openImmersionShriekTriangle j ι).w) :=
  isIso_exchange_triangleShriekTriangle ℓ
    (Compactification.Triangle.ofIsOpenImmersion j.left ι.left)

/-- `boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle` for the triangle of
compactifications of two open immersions by themselves. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_openImmersionShriekTriangle
    (j : Y ⟶ X) (ι : X ⟶ Z) [IsOpenImmersion j.left] [IsOpenImmersion ι.left]
    [IsOpenImmersion (j ≫ ι).left] :
    haveI := isIso_baseChange_openImmersionShriekTriangle ℓ j ι
    haveI := isIso_exchange_openImmersionShriekTriangle ℓ j ι
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (j ≫ ι))
          (Compactification.ofIsOpenImmersion (j ≫ ι).left)).hom ≫
        ((𝔽).compIso (openImmersionShriekTriangle j ι)).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (Compactification.ofIsOpenImmersion j.left)
          (compactificationOverField j)).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (Compactification.ofIsOpenImmersion ι.left)
            (compactificationOverField ι)).hom :=
  boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ j ι
    (Compactification.Triangle.ofIsOpenImmersion j.left ι.left)

/-- The composition isomorphism of `openImmersionShriekTriangle` is the composition isomorphism
of the extensions by zero, read through `R(𝟙)_* ≅ 𝟭`. -/
lemma compIso_openImmersionShriekTriangle_hom_app (j : Y ⟶ X) (ι : X ⟶ Z)
    [IsOpenImmersion j.left] [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_baseChange_openImmersionShriekTriangle ℓ j ι
    haveI := isIso_exchange_openImmersionShriekTriangle ℓ j ι
    ((𝔽).compIso (openImmersionShriekTriangle j ι)).hom.app K =
      (boundedConstructibleLowerStar ℓ (𝟙 Z)).map
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι).map
          ((boundedConstructibleLowerStarId ℓ X).hom.app
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              K)) ≫
          (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
            ι).inv.app K) := by
  have := isIso_baseChange_openImmersionShriekTriangle ℓ j ι
  have := isIso_exchange_openImmersionShriekTriangle ℓ j ι
  rw [boundedConstructibleOpenImmersionLowerShriekComp_eq_shComp']
  exact (𝔽).compIso_ofComp_hom_app (SepFinType.homMk j) (SepFinType.homMk ι)
    (SepFinType.homMk (j ≫ ι)) rfl K

theorem boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion
    (j : Y ⟶ X) (ι : X ⟶ Z) [IsOpenImmersion j.left] [IsOpenImmersion ι.left]
    [IsOpenImmersion (j ≫ ι).left] (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ ι).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app K) ≫
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            K) =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (j ≫ ι)).hom.app K ≫
        (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
          ι).hom.app K := by
  have := isIso_baseChange_openImmersionShriekTriangle ℓ j ι
  have := isIso_exchange_openImmersionShriekTriangle ℓ j ι
  have h := lowerShriekComp_hom_app_of_compIso_aux
    (jf := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (jg := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι)
    (jfg := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (j ≫ ι))
    (PX := boundedConstructibleLowerStar ℓ (𝟙 X)) (PZ := boundedConstructibleLowerStar ℓ (𝟙 Z))
    (Lf := boundedConstructibleLowerShriek ℓ j) (Lg := boundedConstructibleLowerShriek ℓ ι)
    (Lfg := boundedConstructibleLowerShriek ℓ (j ≫ ι))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (compactificationOverField (j ≫ ι))
      (Compactification.ofIsOpenImmersion (j ≫ ι).left))
    ((𝔽).compIso (openImmersionShriekTriangle j ι))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (Compactification.ofIsOpenImmersion j.left)
      (compactificationOverField j))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (Compactification.ofIsOpenImmersion ι.left)
      (compactificationOverField ι))
    (boundedConstructibleLowerStarId ℓ X) (boundedConstructibleLowerStarId ℓ Z)
    (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j ι)
    (boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_openImmersionShriekTriangle ℓ j ι)
    (compIso_openImmersionShriekTriangle_hom_app ℓ j ι) K
  rw [boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl_hom_app,
    boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl_hom_app,
    boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl_hom_app',
    Category.assoc]
  cast_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing
