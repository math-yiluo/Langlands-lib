/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportBaseChange

/-!
# The base change map and the finite-coefficient comparison

Let `T` be a finite discrete commutative ring and `Φ_X = ProEtale.finiteCoefficientModEquivalence`
the equivalence between module objects over `Λ_X = p_X^* T̲` and pro-étale sheaves of
`T`-modules, with derived functor `D(Φ_X)`. For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

`D(Φ_{Y'})` of the base change map `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over `T̲`
(`ProEtale.CondensedRing.baseChangeMap`) and the derived base change map
`ProEtale.derivedBaseChangeMap` of pro-étale sheaves of `T`-modules at `D(Φ_X) M` are isomorphic
arrows (`ProEtale.nonempty_arrowIso_map_baseChangeMap_finiteCoefficient`).

The proof follows the residue field case
(`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap`): the derived
comparisons `ProEtale.finiteCoefficientDerivedUpperStarIso : Lh^* ⋙ D(Φ) ≅ D(Φ) ⋙ Lh^*` are
compatible with the composition of derived pullbacks
(`ProEtale.finiteCoefficientDerivedUpperStarIso_compCoherence`, from the underived
`ProEtale.upperStarFiniteCoefficientModEquivalenceIso_compCoherence`), hence with the pullback
square comparisons, and the cube law of mates
(`CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app`) applies, the comparisons of
the derived pushforwards being invertible since `D(Φ)` is an equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

section Iso

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullbacks commute with the derived comparisons `D(Φ)` between module objects over
`T̲` and pro-étale sheaves of `T`-modules: `Lf^* ⋙ D(Φ_X) ≅ D(Φ_Y) ⋙ Lf^*`, induced by
`upperStarFiniteCoefficientModEquivalenceIso`. This is
`leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`, stated with `D(Φ)` rather than
`finiteCoefficientDerivedEquivalence`. -/
noncomputable def finiteCoefficientDerivedUpperStarIso :
    L((f)^*⟦Profinite.continuousMapRingObj.{u} T⟧) ⋙
        (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory ≅
      (finiteCoefficientModEquivalence Y T).functor.mapDerivedCategory ⋙
        L((f)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) :=
  Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.continuousMapRingObj.{u} T) f) _ ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso f T) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ f).symm

/-- The comparison `Rf_* ⋙ D(Φ_Y) ⟶ D(Φ_X) ⋙ Rf_*` between the derived pushforwards: the mate
of the inverse of `finiteCoefficientDerivedUpperStarIso` along the derived adjunctions. -/
noncomputable def finiteCoefficientDerivedPushHom :
    R((f)_*⟦Profinite.continuousMapRingObj.{u} T⟧) ⋙
        (finiteCoefficientModEquivalence Y T).functor.mapDerivedCategory ⟶
      (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory ⋙
        R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) :=
  (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.continuousMapRingObj.{u} T) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction _ f)
    (finiteCoefficientDerivedUpperStarIso T f).inv)

/-- The comparison `finiteCoefficientDerivedPushHom` is an isomorphism, being the mate of an
isomorphism along equivalences. -/
instance isIso_finiteCoefficientDerivedPushHom : IsIso (finiteCoefficientDerivedPushHom T f) :=
  isIso_mateEquiv_of_isEquivalence _ _ _

end Iso

/-- **The derived finite-coefficient comparison is compatible with composition**: the
isomorphisms `finiteCoefficientDerivedUpperStarIso` are compatible with the composition
isomorphisms `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` of derived pullbacks. -/
theorem finiteCoefficientDerivedUpperStarIso_compCoherence {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) Z))) :
    (finiteCoefficientDerivedUpperStarIso T (p ≫ q)).hom.app M ≫
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) p q).hom.app
          ((finiteCoefficientModEquivalence Z T).functor.mapDerivedCategory.obj M) =
      (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.map
          ((CondensedRing.leftDerivedUpperStarComp
            (Profinite.continuousMapRingObj.{u} T) p q).hom.app M) ≫
        (finiteCoefficientDerivedUpperStarIso T p).hom.app
          (L((q)^*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M) ≫
        L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]).map
          ((finiteCoefficientDerivedUpperStarIso T q).hom.app M) := by
  -- As in `residueFieldDerivedUpperStarIsoCompCoherenceAt`, the unifications below only need
  -- to unfold reducible constants.
  with_reducible
    refine compCoherence_of_isoConj
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} T) q)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} T) p)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} T) (p ≫ q))
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) q)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) p)
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) (p ≫ q))
      ((Functor.mapDerivedCategoryCompIso
          ((q)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          (finiteCoefficientModEquivalence Y T).functor).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso q T)).hom ≫
        (Functor.mapDerivedCategoryCompIso (finiteCoefficientModEquivalence Z T).functor
          ((q)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).inv)
      ((Functor.mapDerivedCategoryCompIso
          ((p)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          (finiteCoefficientModEquivalence X T).functor).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso p T)).hom ≫
        (Functor.mapDerivedCategoryCompIso (finiteCoefficientModEquivalence Y T).functor
          ((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).inv)
      ((Functor.mapDerivedCategoryCompIso
          ((p ≫ q)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          (finiteCoefficientModEquivalence X T).functor).hom ≫
        (Functor.mapDerivedCategoryNatIso
          (upperStarFiniteCoefficientModEquivalenceIso (p ≫ q) T)).hom ≫
        (Functor.mapDerivedCategoryCompIso (finiteCoefficientModEquivalence Z T).functor
          ((p ≫ q)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).inv)
      ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp
        (Profinite.continuousMapRingObj.{u} T) p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          ((q)^*⟦Profinite.continuousMapRingObj.{u} T⟧)
          ((p)^*⟦Profinite.continuousMapRingObj.{u} T⟧)).inv)
      ((Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1} T)) p q)).hom ≫
        (Functor.mapDerivedCategoryCompIso
          ((q)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])
          ((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)])).inv)
      ?_ (finiteCoefficientDerivedUpperStarIso T q) (finiteCoefficientDerivedUpperStarIso T p)
      (finiteCoefficientDerivedUpperStarIso T (p ≫ q)) ?_ ?_ ?_
      (CondensedRing.leftDerivedUpperStarComp (Profinite.continuousMapRingObj.{u} T) p q)
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) p q)
      ?_ ?_ M
  · with_reducible
      exact Functor.mapDerivedCategory_compCoherence' _ _ _ _ _
        (upperStarFiniteCoefficientModEquivalenceIso_compCoherence T p q)
  · intro M
    delta finiteCoefficientDerivedUpperStarIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  · intro M
    delta finiteCoefficientDerivedUpperStarIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  · intro M
    delta finiteCoefficientDerivedUpperStarIso
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  · intro M
    delta CondensedRing.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]
  · intro M
    delta ProEtale.leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
      Functor.leftDerivedFunctorCompIso ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The isomorphisms `finiteCoefficientDerivedUpperStarIso` commute with the transports along an
equality `u = v` of morphisms of schemes. -/
lemma finiteCoefficientDerivedUpperStarIso_hom_app_leftDerivedUpperStarCongr {X Y : Scheme.{u}}
    {u v : X ⟶ Y} (e : u = v)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) Y))) :
    (finiteCoefficientDerivedUpperStarIso T u).hom.app M ≫
        (leftDerivedUpperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} T)) e).hom.app
          ((finiteCoefficientModEquivalence Y T).functor.mapDerivedCategory.obj M) =
      (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.map
          (eqToHom (by rw [e] :
            L((u)^*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M =
              L((v)^*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M)) ≫
        (finiteCoefficientDerivedUpperStarIso T v).hom.app M := by
  subst e
  simp

private lemma inv_inv_comp_eq_comp_inv_inv {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (i₁ : O₂ ≅ O₁) (i₂ : O₃ ≅ O₂) (x : O₃ ⟶ O₄) (y : O₁ ⟶ O₅) (j₁ : O₆ ≅ O₅) (j₂ : O₄ ≅ O₆)
    (h : x ≫ j₂.hom ≫ j₁.hom = i₂.hom ≫ i₁.hom ≫ y) :
    i₁.inv ≫ i₂.inv ≫ x = y ≫ j₁.inv ≫ j₂.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, ← reassoc_of% h]
  simp

private lemma cube_aux {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ Q₁ Q₂ Q₃ Q₄ : C}
    (t₁ : O₁ ⟶ O₂) (t₂ : O₂ ⟶ O₃) (t₃ : O₃ ⟶ O₄) (u₁ : O₄ ⟶ O₅) (u₂ : O₅ ⟶ O₆) (v₁ : O₁ ⟶ Q₁)
    (v₂ : Q₁ ⟶ Q₂) (w₁ : Q₂ ⟶ Q₃) (w₂ : Q₃ ⟶ Q₄) (w₃ : Q₄ ⟶ O₆) (P₁ : O₂ ⟶ Q₃) (P₂ : O₃ ⟶ Q₄)
    (s : O₂ ⟶ O₁) (s' : Q₃ ⟶ Q₂) (hs : t₁ ≫ s = 𝟙 O₁) (hs' : s' ≫ w₁ = 𝟙 Q₃)
    (H₁ : P₁ ≫ s' = s ≫ v₁ ≫ v₂) (H₂ : P₂ ≫ w₃ = t₃ ≫ u₁ ≫ u₂) (H₃ : P₁ ≫ w₂ = t₂ ≫ P₂) :
    t₁ ≫ t₂ ≫ t₃ ≫ u₁ ≫ u₂ = v₁ ≫ v₂ ≫ w₁ ≫ w₂ ≫ w₃ := by
  have h : t₁ ≫ P₁ = v₁ ≫ v₂ ≫ w₁ := by
    rw [← Category.comp_id P₁, ← hs', reassoc_of% H₁, reassoc_of% hs]
  rw [← H₂, reassoc_of% H₃.symm, reassoc_of% h]

variable {T} {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The cube condition of `CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app` for
the derived pullbacks of module objects over `T̲` and of sheaves of `T`-modules along a
commutative square. -/
lemma finiteCoefficientDerivedUpperStarIso_cube (sq : CommSq g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) Y))) :
    L((f')^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]).map
        ((finiteCoefficientDerivedUpperStarIso T g).inv.app M) ≫
        (finiteCoefficientDerivedUpperStarIso T f').inv.app
          (L((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M) ≫
        (finiteCoefficientModEquivalence X' T).functor.mapDerivedCategory.map
          ((pullbackSquareComparison (Profinite.continuousMapRingObj.{u} T) sq).hom.app M) =
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq).hom.app
          ((finiteCoefficientModEquivalence Y T).functor.mapDerivedCategory.obj M) ≫
        L((g')^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]).map
          ((finiteCoefficientDerivedUpperStarIso T f).inv.app M) ≫
        (finiteCoefficientDerivedUpperStarIso T g').inv.app
          (L((f)^*⟦Profinite.continuousMapRingObj.{u} T⟧).obj M) := by
  -- As in `residueFieldDerivedUpperStarIso_cube`, the unifications with
  -- `inv_inv_comp_eq_comp_inv_inv` and `cube_aux` only need to unfold reducible constants.
  simp only [← Iso.app_inv, ← Functor.mapIso_inv]
  with_reducible refine inv_inv_comp_eq_comp_inv_inv _ _ _ _ _ _ ?_
  have H₁ := finiteCoefficientDerivedUpperStarIso_compCoherence T f' g M
  have H₂ := finiteCoefficientDerivedUpperStarIso_compCoherence T g' f M
  have H₃ := finiteCoefficientDerivedUpperStarIso_hom_app_leftDerivedUpperStarCongr T sq.w.symm M
  simp only [Iso.app_hom, Functor.mapIso_hom, pullbackSquareComparison_hom_app, Functor.map_comp,
    Category.assoc, leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  with_reducible
    exact cube_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [← Functor.map_comp]) (by simp) H₁ H₂ H₃

/-- **The exchange morphisms and the finite-coefficient comparison.** For a commutative square
of schemes, `D(Φ_{Y'})` of the exchange morphism of the pullback square comparison of module
objects over `T̲` at `M` and the exchange morphism of `leftDerivedUpperStarSquareIso` for
pro-étale sheaves of `T`-modules at `D(Φ_X) M` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_exchangeRight_finiteCoefficient (sq : CommSq g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X))) :
    Nonempty (Arrow.mk ((finiteCoefficientModEquivalence Y' T).functor.mapDerivedCategory.map
        ((Adjunction.exchangeRight
          (CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.continuousMapRingObj.{u} T) f)
          (CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.continuousMapRingObj.{u} T) f')
          (pullbackSquareComparison (Profinite.continuousMapRingObj.{u} T) sq)).app M)) ≅
      Arrow.mk ((Adjunction.exchangeRight
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f')
        (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq)).app
        ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.obj M))) := by
  have key := Adjunction.nonempty_arrowIso_map_exchangeRight_app
    (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj.{u} T) f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj.{u} T) f')
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f')
    (pullbackSquareComparison (Profinite.continuousMapRingObj.{u} T) sq)
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq)
    (finiteCoefficientDerivedUpperStarIso T f) (finiteCoefficientDerivedUpperStarIso T f')
    (finiteCoefficientDerivedUpperStarIso T g) (finiteCoefficientDerivedUpperStarIso T g')
    ?_ (finiteCoefficientDerivedPushHom T f) rfl (finiteCoefficientDerivedPushHom T f') rfl M
    inferInstance inferInstance
  · exact key
  · exact finiteCoefficientDerivedUpperStarIso_cube sq

omit [DiscreteTopology T] [Finite T] in
/-- The base change map of module objects over `T̲` is the exchange morphism of the pullback
square comparison. The two sides only differ by the unfolding of `CondensedRing.baseChangeMap`,
whose instance arguments were elaborated for a general condensed ring (comparing them at default
transparency times out). -/
lemma baseChangeMap_finiteCoefficient_eq_exchangeRight (sq : CommSq g' f' f g) :
    CondensedRing.baseChangeMap (Profinite.continuousMapRingObj.{u} T) sq =
      Adjunction.exchangeRight
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} T) f)
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} T) f')
        (pullbackSquareComparison (Profinite.continuousMapRingObj.{u} T) sq) := by
  delta CondensedRing.baseChangeMap
  with_reducible_and_instances rfl

/-- Isomorphic arrows `P(α_X)` and `β_{X'}` stay isomorphic when the natural transformations `α`
and `β` are replaced by equal ones. -/
private lemma nonempty_arrowIso_map_app_of_eq {C D E C' : Type*} [Category* C] [Category* D]
    [Category* E] [Category* C'] {F G : C ⥤ D} {α α' : F ⟶ G} {F' G' : C' ⥤ E}
    {β β' : F' ⟶ G'} (P : D ⥤ E) (hα : α = α') (hβ : β = β') (X : C) (X' : C')
    (e : Nonempty (Arrow.mk (P.map (α.app X)) ≅ Arrow.mk (β.app X'))) :
    Nonempty (Arrow.mk (P.map (α'.app X)) ≅ Arrow.mk (β'.app X')) := by
  subst hα hβ
  exact e

/-- **The base change map and the finite-coefficient comparison.** For a commutative square of
schemes, `D(Φ_{Y'})` of the base change map `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over
`T̲` and the derived base change map of pro-étale sheaves of `T`-modules at `D(Φ_X) M` are
isomorphic arrows. -/
theorem nonempty_arrowIso_map_baseChangeMap_finiteCoefficient (sq : CommSq g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X))) :
    Nonempty (Arrow.mk ((finiteCoefficientModEquivalence Y' T).functor.mapDerivedCategory.map
        ((CondensedRing.baseChangeMap (Profinite.continuousMapRingObj.{u} T) sq).app M)) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq).app
        ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.obj M))) :=
  nonempty_arrowIso_map_app_of_eq (finiteCoefficientModEquivalence Y' T).functor.mapDerivedCategory
    (baseChangeMap_finiteCoefficient_eq_exchangeRight sq).symm
    (exchangeRight_leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq) M
    ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.obj M)
    (nonempty_arrowIso_map_exchangeRight_finiteCoefficient sq M)


/-- **The base change map and the finite-coefficient comparison.** The base change map of module
objects over `T̲` is invertible at `M` if and only if the derived base change map of pro-étale
sheaves of `T`-modules is invertible at `D(Φ_X) M`. -/
theorem isIso_baseChangeMap_app_finiteCoefficient_iff (sq : CommSq g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X))) :
    IsIso ((CondensedRing.baseChangeMap (Profinite.continuousMapRingObj.{u} T) sq).app M) ↔
      IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq).app
        ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.obj M)) := by
  obtain ⟨i⟩ := nonempty_arrowIso_map_baseChangeMap_finiteCoefficient sq M
  refine ⟨fun h ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff i).1 ?_, fun h ↦ ?_⟩
  · exact Functor.map_isIso _ _
  · have := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff i).2 h
    exact isIso_of_reflects_iso _ (finiteCoefficientModEquivalence Y' T).functor.mapDerivedCategory

end AlgebraicGeometry.ProEtale
