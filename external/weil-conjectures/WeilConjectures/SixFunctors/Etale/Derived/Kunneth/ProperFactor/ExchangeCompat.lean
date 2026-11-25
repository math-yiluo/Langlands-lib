/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# The Künneth map and the exchange map of an open immersion

Let `j : U ⟶ X` be a morphism of `S`-schemes, `Y` an `S`-scheme, `W = X ×_S Y` with projections
`q : W ⟶ X`, `r : W ⟶ Y`, and `V = U ×_X W` with projections `p : V ⟶ U`, `h : V ⟶ W`. The
Künneth maps (`AlgebraicGeometry.Etale.kunnethMap`) of `(X, Y)` at `Rj_* F` and of `(U, Y)` at
`F` are compatible with the exchange map `β : Lq^* Rj_* F ⟶ Rh_* Lp^* F`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) and the composition isomorphism
`Ra_{X*} Rj_* ≅ Ra_{U*}` (blueprint `lemma-kunneth-finite-direct-image--1`).

As a consequence, for `S = Spec k` with `k` separably closed and `Λ` a finite ring whose exponent
is invertible in `k`, `RΓ(W, β)` is an isomorphism: this is the projective case of the proof of
blueprint `corollary-open-direct-image-over-field--2`.

## Main statements

- `AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap`
(`lemma-kunneth-finite-direct-image--1`).
- `AlgebraicGeometry.Etale.isIso_rightDerivedGlobalSections_map_derivedBaseChangeMap_of_isProper`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {S X Y U W V : Scheme.{u}}

/-- The transpose of the Künneth map `κ_{E,K}` along `Lc^* ⊣ Rc_*`, written with the tensor
comparison of `Lc^*`: it is
`Lc^*(Rf_* E ⊗ᴸ Rg_* K) ⟶ Lc^* Rf_* E ⊗ᴸ Lc^* Rg_* K ⟶ Lp^* E ⊗ᴸ Lq^* K`, the second map being
`Lc^* Rf_* E ≅ Lp^* Lf^* Rf_* E ⟶ Lp^* E` tensored with
`Lc^* Rg_* K ≅ Lq^* Lg^* Rg_* K ⟶ Lq^* K`. -/
@[reassoc]
lemma map_kunnethMap_comp_counit (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((c)^*[A]).map (kunnethMap A p q f g c hp hq E K) ≫
        (derivedUpperStarLowerStarAdjunction A c).counit.app _ =
      ((leftDerivedUpperStarTensorComparison A c).app _).app _ ≫
        ((-⊗ᴸ-(W)[A]).map ((leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
          L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E))).app _ ≫
        ((-⊗ᴸ-(W)[A]).obj _).map ((leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K)) := by
  refine ((derivedUpperStarLowerStarAdjunction A c).homEquiv_counit
    (g := kunnethMap A p q f g c hp hq E K)).symm.trans ?_
  rw [kunnethMap, Equiv.symm_apply_apply,
    ← leftDerivedUpperStarTensorComparison_comp_derivedTensor_assoc A p f c hp.symm]
  congr 1
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map, Category.assoc,
    comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id_app,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

omit [Etale.UpperStarPreservesFlat A] in
/-- The counit `Lr'^* Ra_{Y*} K ≅ Lc'^* Ra_{Y*} K ⟶ ...` of a composite `r' = h ≫ r`: the map
`Lc'^* Ra_{Y*} K ≅ Lr'^* La_Y^* Ra_{Y*} K ⟶ Lr'^* K` agrees with
`Lc'^* Ra_{Y*} K ≅ Lh^* Lc^* Ra_{Y*} K ≅ Lh^* Lr^* La_Y^* Ra_{Y*} K ⟶ Lh^* Lr^* K ≅ Lr'^* K`. -/
lemma leftDerivedUpperStarComp_hom_app_map_counit_comp (h : V ⟶ W) (r : W ⟶ Y) (aY : Y ⟶ S)
    (c : W ⟶ S) (r' : V ⟶ Y) (c' : V ⟶ S) (hr : r ≫ aY = c) (hr' : h ≫ r = r')
    (hc' : h ≫ c = c') (hr'c : r' ≫ aY = c')
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A r' aY c' hr'c.symm).hom.app _ ≫
        L((r')^*[A]).map ((derivedUpperStarLowerStarAdjunction A aY).counit.app K) =
      (leftDerivedUpperStarComp A h c c' hc'.symm).hom.app _ ≫
        L((h)^*[A]).map ((leftDerivedUpperStarComp A r aY c hr.symm).hom.app _ ≫
          L((r)^*[A]).map ((derivedUpperStarLowerStarAdjunction A aY).counit.app K)) ≫
        (leftDerivedUpperStarComp A h r r' hr'.symm).inv.app K := by
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
    leftDerivedUpperStarComp_assoc'_app A h r aY r' c c' hr'.symm hr.symm hr'c.symm,
    Category.assoc, Category.assoc]
  erw [← (leftDerivedUpperStarComp A h r r' hr'.symm).hom.naturality_assoc]
  simp

omit [Etale.UpperStarPreservesFlat A] in
/-- The counit of a composite `a_U = j ≫ a_X` and the exchange map: the map
`Lc'^* Ra_{X*} Rj_* F ≅ Lc'^* Ra_{U*} F ≅ Lp^* La_U^* Ra_{U*} F ⟶ Lp^* F` agrees with
`Lc'^* Ra_{X*} Rj_* F ≅ Lh^* Lq^* La_X^* Ra_{X*} Rj_* F ⟶ Lh^* Lq^* Rj_* F ≅ Lp^* Lj^* Rj_* F
⟶ Lp^* F`. -/
lemma leftDerivedUpperStarComp_hom_app_map_counit_comp_derivedSquareUpperStarIso
    (j : U ⟶ X) (aX : X ⟶ S) (aU : U ⟶ S) (hj : j ≫ aX = aU) (q : W ⟶ X) (c : W ⟶ S)
    (hq : q ≫ aX = c) (p : V ⟶ U) (h : V ⟶ W) (sq : CommSq p h j q) (c' : V ⟶ S)
    (hc' : h ≫ c = c') (hp : p ≫ aU = c')
    (F : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    L((c')^*[A]).map ((rightDerivedLowerStarCompIsoOfComp A j aX aU hj).hom.app F) ≫
        (leftDerivedUpperStarComp A p aU c' hp.symm).hom.app _ ≫
        L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A aU).counit.app F) =
      (leftDerivedUpperStarComp A h c c' hc'.symm).hom.app _ ≫
        L((h)^*[A]).map ((leftDerivedUpperStarComp A q aX c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A aX).counit.app
            (R((j)_*[A]).obj F))) ≫
        (derivedSquareUpperStarIso A sq).hom.app (R((j)_*[A]).obj F) ≫
        L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A j).counit.app F) := by
  have hc'pj : c' = (p ≫ j) ≫ aX := by rw [Category.assoc, hj, hp]
  erw [(leftDerivedUpperStarComp A p aU c' hp.symm).hom.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp,
    map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit A j aX aU hj F,
    Functor.map_comp, Functor.map_comp, ← Category.assoc]
  erw [leftDerivedUpperStarComp_assoc'_app A p j aX (p ≫ j) aU c' rfl hj.symm hc'pj]
  rw [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp]
  simp only [Category.assoc]
  erw [leftDerivedUpperStarComp_assoc'_app_assoc A h q aX (p ≫ j) c c' sq.w hq.symm hc'pj]
  congr 1
  erw [← (leftDerivedUpperStarComp A h q (p ≫ j) sq.w).hom.naturality_assoc,
    ← (leftDerivedUpperStarComp A p j (p ≫ j) rfl).hom.naturality_assoc]
  simp

/-- Blueprint `lemma-kunneth-finite-direct-image--1`: compatibility of the Künneth maps with the
exchange map of the square

```
  V --h--> W --r--> Y
  |        |        |
  p        q        a_Y
  v        v        v
  U --j--> X --a_X-> S
```

For `F ∈ D(U_ét)` and `K ∈ D(Y_ét)`, the Künneth map of `(U, Y)` at `(F, K)`, precomposed with
the composition isomorphism `Ra_{X*} Rj_* F ≅ Ra_{U*} F`, is the Künneth map of `(X, Y)` at
`(Rj_* F, K)` followed by `Rc_*` of the exchange map `β : Lq^* Rj_* F ⟶ Rh_* Lp^* F` tensored with
`Lr^* K`, the projection map of `h`, the composition isomorphism `Rc_* Rh_* ≅ Rc'_*` and
`Lh^* Lr^* K ≅ Lr'^* K`. -/
lemma kunnethMap_derivedBaseChangeMap (aX : X ⟶ S) (aY : Y ⟶ S) (aU : U ⟶ S)
    (q : W ⟶ X) (r : W ⟶ Y) (c : W ⟶ S) (hq : q ≫ aX = c) (hr : r ≫ aY = c)
    (j : U ⟶ X) (hj : j ≫ aX = aU) (p : V ⟶ U) (h : V ⟶ W) (sq : CommSq p h j q)
    (r' : V ⟶ Y) (hr' : h ≫ r = r') (c' : V ⟶ S) (hc' : h ≫ c = c')
    (hp : p ≫ aU = c') (hr'c : r' ≫ aY = c')
    (F : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(S)[A]).map ((rightDerivedLowerStarCompIsoOfComp A j aX aU hj).hom.app F)).app
        (R((aY)_*[A]).obj K) ≫ kunnethMap A p r' aU aY c' hp hr'c F K =
      kunnethMap A q r aX aY c hq hr (R((j)_*[A]).obj F) K ≫
        R((c)_*[A]).map
          (((-⊗ᴸ-(W)[A]).map ((derivedBaseChangeMap A sq).app F)).app (L((r)^*[A]).obj K) ≫
            ((rightDerivedLowerStarProjectionMap A h).app _).app _) ≫
        (rightDerivedLowerStarCompIsoOfComp A h c c' hc').hom.app _ ≫
        R((c')_*[A]).map (((-⊗ᴸ-(V)[A]).obj _).map
          ((leftDerivedUpperStarComp A h r r' hr'.symm).inv.app K)) := by
  apply ((derivedUpperStarLowerStarAdjunction A c').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    map_kunnethMap_comp_counit, Adjunction.counit_naturality,
    map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit_assoc]
  dsimp only [Functor.comp_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.id_obj]
  conv_rhs => rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  erw [(leftDerivedUpperStarComp A h c c' hc'.symm).hom.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp_assoc]
  rw [Functor.map_comp L((c)^*[A]), Category.assoc, Adjunction.counit_naturality,
    Functor.map_comp L((c)^*[A]), Category.assoc, Adjunction.counit_naturality_assoc,
    map_kunnethMap_comp_counit_assoc]
  simp only [Functor.map_comp, Category.assoc, NatTrans.comp_app,
    map_rightDerivedLowerStarProjectionMap_comp_counit'_assoc,
    leftDerivedUpperStarTensorComparison_naturality_left_assoc,
    leftDerivedUpperStarTensorComparison_naturality_right_assoc]
  rw [← leftDerivedUpperStarTensorComparison_comp_derivedTensor_assoc A h c c' hc'.symm]
  congr 1
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp]
  congr 2
  · rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit]
    have := leftDerivedUpperStarComp_hom_app_map_counit_comp_derivedSquareUpperStarIso A j aX aU hj
      q c hq p h sq c' hc' hp F
    simp only [Functor.map_comp, Category.assoc] at this ⊢
    exact this
  · have := leftDerivedUpperStarComp_hom_app_map_counit_comp A h r aY c r' c' hr hr' hc' hr'c K
    simp only [Functor.map_comp, Category.assoc] at this ⊢
    exact this


/-- The exchange map `β : Lq^* Rj_* F ⟶ Rh_* Lp^* F` of the square of
`AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap` becomes an isomorphism after `Rc_*`
as soon as the Künneth maps of `(X, Y)` at `(Rj_* F, Λ_Y)` and of `(U, Y)` at `(F, Λ_Y)` are
isomorphisms: by `lemma-kunneth-finite-direct-image--1`, `Rc_*(β ⊗ᴸ Lr^* Λ_Y)` is then an
isomorphism, the projection map of `h` being an isomorphism at the unit. -/
theorem isIso_rightDerivedLowerStar_map_derivedBaseChangeMap_of_isIso_kunnethMap
    (aX : X ⟶ S) (aY : Y ⟶ S) (aU : U ⟶ S)
    (q : W ⟶ X) (r : W ⟶ Y) (c : W ⟶ S) (hq : q ≫ aX = c) (hr : r ≫ aY = c)
    (j : U ⟶ X) (hj : j ≫ aX = aU) (p : V ⟶ U) (h : V ⟶ W) (sq : CommSq p h j q)
    (r' : V ⟶ Y) (hr' : h ≫ r = r') (c' : V ⟶ S) (hc' : h ≫ c = c')
    (hp : p ≫ aU = c') (hr'c : r' ≫ aY = c')
    (F : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (hX : IsIso (kunnethMap A q r aX aY c hq hr (R((j)_*[A]).obj F) (𝟙_ _)))
    (hU : IsIso (kunnethMap A p r' aU aY c' hp hr'c F (𝟙_ _))) :
    IsIso (R((c)_*[A]).map ((derivedBaseChangeMap A sq).app F)) := by
  have e := kunnethMap_derivedBaseChangeMap A aX aY aU q r c hq hr j hj p h sq r' hr' c' hc' hp
    hr'c F (𝟙_ _)
  have h₁ := IsIso.of_isIso_fac_left e.symm
  rw [isIso_comp_right_iff, Functor.map_comp] at h₁
  have : IsIso (((rightDerivedLowerStarProjectionMap A h).app (L((p)^*[A]).obj F)).app
      (L((r)^*[A]).obj (𝟙_ _))) :=
    (NatTrans.isIso_app_iff_of_iso ((rightDerivedLowerStarProjectionMap A h).app _)
      (leftDerivedUpperStarUnitIso A r)).2
      (isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit A h _)
  rw [isIso_comp_right_iff] at h₁
  have h₂ : IsIso (R((c)_*[A]).map
      (((-⊗ᴸ-(W)[A]).map ((derivedBaseChangeMap A sq).app F)).app (𝟙_ _))) :=
    (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight ((-⊗ᴸ-(W)[A]).map ((derivedBaseChangeMap A sq).app F))
        R((c)_*[A])) (leftDerivedUpperStarUnitIso A r)).1 h₁
  have hρ : (derivedBaseChangeMap A sq).app F = (ρ_ _).inv ≫
      ((-⊗ᴸ-(W)[A]).map ((derivedBaseChangeMap A sq).app F)).app (𝟙_ _) ≫ (ρ_ _).hom := by
    simp [derivedTensor]
  rw [hρ, Functor.map_comp, Functor.map_comp]
  infer_instance

end General

section Point

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- The projective case of the proof of blueprint `corollary-open-direct-image-over-field--2`.

Let `k` be a separably closed field, `Λ` a ring which is torsion as an additive group,
`j : U ⟶ X` an open immersion of `k`-schemes, `X` of finite type over `k`, `Y` a proper (e.g.
projective) `k`-scheme, `W = X ×_k Y` with projections `q`, `r`, and `V = U ×_X W` with
projections `p : V ⟶ U`, `h : V ⟶ W`. For every `E ∈ D(U_ét, Λ)` the exchange map
`β : Lq^* Rj_* E ⟶ Rh_* Lp^* E` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`) induces an
isomorphism `RΓ(W, Lq^* Rj_* E) ≅ RΓ(W, Rh_* Lp^* E)`.

Following the blueprint, both sides are computed by the Künneth formula with the proper factor
`Y` (`AlgebraicGeometry.Etale.isIso_kunnethMap_of_isProper`,
`corollary-open-direct-image-over-field--2`) with the unit `Λ_Y` on `Y`, and the two Künneth maps
are related by `AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap`
(`lemma-kunneth-finite-direct-image--1`). -/
theorem isIso_rightDerivedGlobalSections_map_derivedBaseChangeMap_of_isProper
    (hΛ : IsAddTorsion Λ) {X Y U W V : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsProper aY]
    (q : W ⟶ X) (r : W ⟶ Y) (sqW : IsPullback q r aX aY)
    (j : U ⟶ X) [IsOpenImmersion j] (p : V ⟶ U) (h : V ⟶ W) (sq : IsPullback p h j q)
    (E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app E)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have sqV : IsPullback p (h ≫ r) (j ≫ aX) aY := (sq.flip.paste_horiz sqW.flip).flip
  have hc' : h ≫ q ≫ aX = p ≫ j ≫ aX := by rw [← Category.assoc, ← sq.w, Category.assoc]
  have := isIso_rightDerivedLowerStar_map_derivedBaseChangeMap_of_isIso_kunnethMap
    (ModuleCat.{u + 1} Λ) aX aY (j ≫ aX) q r (q ≫ aX) rfl sqW.w.symm j rfl p h sq.toCommSq
    (h ≫ r) rfl (p ≫ j ≫ aX) hc' rfl sqV.w.symm E
    (isIso_kunnethMap_of_isProper Λ hΛ aX aY q r sqW _ _)
    (isIso_kunnethMap_of_isProper Λ hΛ (j ≫ aX) aY p (h ≫ r) sqV _ _)
  exact (NatIso.isIso_map_iff
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ (q ≫ aX)) _).1
    (by rw [Functor.comp_map]; infer_instance)

end Point

end Etale

end AlgebraicGeometry
