/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekCompactificationBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The base change isomorphism of the extension by zero as a mate

Let `j : U ⟶ Z` be an open immersion. On the unbounded derived categories of pro-étale sheaves,
the extension by zero `j_!` is left adjoint to the derived pullback `Lj^*`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`).

For a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the mate of the
base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`) along
these adjunctions is the square isomorphism `Lj^* Lg'^* ≅ L(g'')^* Lj'^*` of derived pullbacks.
This is an input for the compatibility of the compact-support exchange maps with the change of
coefficients (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`:
  the adjunction `j_! ⊣ Lj^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section SquareIso

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The square isomorphism `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*` of pullbacks of a commutative square
`g' ≫ j = j' ≫ g''` is conjugate to the square isomorphism of pushforwards. -/
lemma conjugateEquiv_upperStarCompIso_hom (sq : CommSq g' j' j g'') :
    conjugateEquiv ((upperStarLowerStarAdjunction A g'').comp (upperStarLowerStarAdjunction A j'))
      ((upperStarLowerStarAdjunction A j).comp (upperStarLowerStarAdjunction A g'))
      (upperStarCompIso A sq.w).hom = (ProEtale.squareLowerStarIso A sq).hom := by
  have hc : (upperStarCongr A sq.w).hom = (upperStarCongr A sq.w.symm).inv := by
    simp [upperStarCongr]
  rw [upperStarCompIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (g' ≫ j)),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (j' ≫ g'')), hc,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarCongr_inv,
    conjugateEquiv_upperStarComp_inv]
  simp [ProEtale.squareLowerStarIso]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The weakly étale base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` is the mate, along the
adjunctions `g''^* ⊣ g''_*` and `g'^* ⊣ g'_*`, of the square isomorphism of pullbacks. -/
lemma baseChangeMap_eq_mateEquiv (sq : CommSq g' j' j g'') :
    ProEtale.baseChangeMap A sq =
      (mateEquiv (upperStarLowerStarAdjunction A g'') (upperStarLowerStarAdjunction A g')
        (upperStarCompIso A sq.w).hom) := by
  have h := iterated_mateEquiv_conjugateEquiv (upperStarLowerStarAdjunction A g'')
    (upperStarLowerStarAdjunction A g') (upperStarLowerStarAdjunction A j)
    (upperStarLowerStarAdjunction A j') (upperStarCompIso A sq.w).hom
  rw [conjugateEquiv_upperStarCompIso_hom A sq] at h
  rw [ProEtale.baseChangeMap]
  rw [Equiv.symm_apply_eq]
  exact (congrArg (TwoSquare.mk _ _ _ _) h).symm

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The base change map `j'_! g'^* ⟶ g''^* j_!` of the extension by zero is the mate, along the
adjunctions `j_! ⊣ j^*` and `j'_! ⊣ j'^*`, of the square isomorphism of pullbacks. -/
lemma mateEquiv_openImmersionLowerShriekBaseChangeMap [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq g' j' j g'') :
    mateEquiv (openImmersionLowerShriekUpperStarAdjunction A j)
        (openImmersionLowerShriekUpperStarAdjunction A j')
        (openImmersionLowerShriekBaseChangeMap A sq) =
      (upperStarCompIso A sq.w).hom := by
  apply (mateEquiv (upperStarLowerStarAdjunction A g'')
    (upperStarLowerStarAdjunction A g')).injective
  have h := iterated_mateEquiv_conjugateEquiv (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j') (upperStarLowerStarAdjunction A g')
    (upperStarLowerStarAdjunction A g'') (openImmersionLowerShriekBaseChangeMap A sq)
  have hc : conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction A j).comp
        (upperStarLowerStarAdjunction A g''))
      ((upperStarLowerStarAdjunction A g').comp (openImmersionLowerShriekUpperStarAdjunction A j'))
      (openImmersionLowerShriekBaseChangeMap A sq) = ProEtale.baseChangeMap A sq := by
    rw [openImmersionLowerShriekBaseChangeMap, Equiv.apply_symm_apply]
  rw [hc, baseChangeMap_eq_mateEquiv] at h
  apply NatTrans.ext
  funext X
  exact NatTrans.congr_app h X

/-- The transport `Lf^* ≅ Lg^*` along `f = g` is induced by `f^* ≅ g^*`. -/
lemma leftDerivedUpperStarCongr_inv_app_eq_mapDerivedCategory {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedUpperStarCongr A h).inv.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A g).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarCongr A h.symm)).hom.app K ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A f).inv.app K := by
  subst h
  simp [upperStarCongr, Functor.mapDerivedCategoryNatIso_refl]

/-- The square isomorphism `Lj^* Lg'^* ≅ L(g'')^* Lj'^*` of derived pullbacks is induced by the
square isomorphism `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*` of pullbacks. -/
lemma leftDerivedUpperStarSquareIso_inv_app (sq : CommSq g' j' j g'')
    (Y : DerivedCategory (Sheaf (ProEt.topology Z) A)) :
    L((g')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y) ≫
        (leftDerivedUpperStarSquareIso A sq).inv.app Y ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app (L((g'')^*[A]).obj Y) =
      (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app (D((j)^*[A]).obj Y) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarCompIso A sq.w)).hom.app Y ≫
        D((j')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A g'').inv.app Y) := by
  have hnat := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y)
  simp only [leftDerivedUpperStarSquareIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso, upperStarCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Category.assoc, Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    leftDerivedUpperStarCongr_inv_app_eq_mapDerivedCategory]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

end SquareIso

section Adjunction

variable {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]

/-- The adjunction `j_! ⊣ Lj^*` between the extension by zero along an open immersion `j` and the
derived pullback on the unbounded derived categories of pro-étale sheaves: the adjunction
`D(j_!) ⊣ D(j^*)` (`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`)
transported along `Lj^* ≅ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction :
    D((j)_!open[A]) ⊣ L((j)^*[A]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory A j).symm

end Adjunction

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The derived base change isomorphism of the extension by zero is the mate of the square
isomorphism induced by `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*`, for the adjunctions `Dj_! ⊣ Dj^*`. -/
lemma unit_map_derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf (ProEt.topology U) A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (D((g')^*[A]).obj K) ≫
        D((j')^*[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      D((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarCompIso A hsq.toCommSq.w)).hom.app
          (D((j)_!open[A]).obj K) :=
  Adjunction.mapDerivedCategoryAdjunction_mate (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j') (upperStarCompIso A hsq.toCommSq.w)
    (openImmersionLowerShriekBaseChangeIso A hsq) (fun F ↦ by
      have h := unit_mateEquiv (openImmersionLowerShriekUpperStarAdjunction A j)
        (openImmersionLowerShriekUpperStarAdjunction A j')
        (openImmersionLowerShriekBaseChangeMap A hsq.toCommSq) F
      rw [mateEquiv_openImmersionLowerShriekBaseChangeMap] at h
      exact h.symm) K

/-- The mate of the base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*` of the extension by zero
along the adjunctions `j_! ⊣ Lj^*` and `j'_! ⊣ Lj'^*` is the square isomorphism
`Lj^* Lg'^* ≅ L(g'')^* Lj'^*` of derived pullbacks. -/
theorem mateEquiv_leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_inv
    (hsq : IsPullback g' j' j g'') :
    mateEquiv (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j')
        (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso A hsq).inv =
      (leftDerivedUpperStarSquareIso A hsq.toCommSq).inv := by
  refine mateEquiv_eq_of_unit _ _ _ _ fun K ↦ ?_
  rw [← cancel_mono ((leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app
    (L((g'')^*[A]).obj (D((j)_!open[A]).obj K)))]
  simp only [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.whiskerRight_app, Category.assoc]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K)
  dsimp at hn
  erw [NatIso.naturality_1 (leftDerivedUpperStarIsoMapDerivedCategory A j')]
  rw [Functor.map_comp_assoc, leftDerivedUpperStarSquareIso_inv_app,
    reassoc_of% hn, ← reassoc_of% (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso A hsq K),
    Functor.map_comp]
  erw [Adjunction.unit_naturality_assoc]
  rw [Functor.map_comp]

end BaseChange

end AlgebraicGeometry.ProEtale
