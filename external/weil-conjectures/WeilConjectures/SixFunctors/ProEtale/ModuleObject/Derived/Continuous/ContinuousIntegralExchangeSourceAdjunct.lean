/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private lemma coefficient_counit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
    {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
    {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
    {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
    (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (M : A) :
    U₂.map ((Adjunction.pushHomOfComapIso adj₁ adj₂ e).app M) ≫
      adjS.counit.app (E₁.obj M) =
    (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv.app (L₁.obj M) ≫
      E₁.map (adjR.counit.app M) := by
  have hm := iterated_mateEquiv_conjugateEquiv_symm adjR adjS adj₂ adj₁
    (TwoSquare.mk _ _ _ _ e.inv)
  have hc := mateEquiv_counit_symm adjR adjS
    (TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso adj₁ adj₂ e)) M
  rw [show (mateEquiv adjR adjS).symm
      (TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso adj₁ adj₂ e)) =
    TwoSquare.mk _ _ _ _
      (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv from hm] at hc
  exact hc

private lemma source_normal_form
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (θ : G ⋙ L' ≅ L ⋙ H) (β : R ⋙ G ⟶ H ⋙ R')
    (N : D) (M : C) (A : C') (s : A ⟶ G.obj M) (δ : M ⟶ R.obj N)
    (Q : D) (q : L.obj M ⟶ Q) (r : Q ⟶ N)
    (hβ : β = Adjunction.squareExchange a b G H θ)
    (hc : L.map δ ≫ a.counit.app N = q ≫ r) :
    (b.homEquiv A (H.obj N)).symm ((s ≫ G.map δ) ≫ β.app N) =
      L'.map s ≫ θ.hom.app M ≫ H.map q ≫ H.map r := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
    Adjunction.squareExchange_map_counit_of_eq a b G H θ hβ N]
  simp only [Functor.map_comp, Category.assoc]
  have hn := θ.hom.naturality δ
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [← H.map_comp, hc, H.map_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- `E̲` with the topology and ring structure of the normed field `F`, the coefficient ring of
`integralScalarConstructible`. -/
private noncomputable abbrev normedRing (F : Type) [NormedField F] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj.{u} F

/-- The counit of the restriction of `Lf^* ⊣ Rf_*` to bounded constructible complexes, along a
proof `hf` that `Rf_*` preserves them, is the derived counit. -/
private lemma restricted_counit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U)
    (hf : ∀ K : Dᵇc(T.left)⟦Λ⟧,
      boundedConstructible (condensedRingObj Λ U.left) ((R((h.left)_*⟦Λ⟧)).obj K.obj))
    (K : Dᵇc(T.left)⟦Λ⟧) :
    ((Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ h.left)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ h).symm
      (ObjectProperty.liftCompιIso _ _ hf).symm).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ h.left).counit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ h.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ h).symm
    (ObjectProperty.liftCompιIso _ _ hf).symm K).trans ?_
  simp only [boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, ObjectProperty.lift_obj_obj,
    Iso.symm_inv, Iso.refl_hom, NatTrans.id_app]
  exact (Category.id_comp _).trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))

/-- The `O̲`-coefficient adjunction `Lf^* ⊣ Rf_*` is the restricted derived adjunction. -/
private lemma unitBall_adjunction_eq {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U) :
    UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
        h =
      Adjunction.restrictFullyFaithful
        (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) h.left)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility (integralCoeff ℓ E) ℓ h).symm
        (ObjectProperty.liftCompιIso _ _
          (UnitBallRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ
            (continuousIntegers ℓ E) h)).symm :=
  rfl

/-- The `E̲`-coefficient adjunction `Lf^* ⊣ Rf_*` is the restricted derived adjunction. -/
private lemma continuousMap_adjunction_eq {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U) :
    ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h =
      Adjunction.restrictFullyFaithful
        (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) h.left)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ h).symm
        (ObjectProperty.liftCompιIso _ _
          (ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E h)).symm :=
  rfl

private lemma bounded_counit_hom_unitBall
    (K : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)) :
    ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
      (f.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f).counit.app K.obj :=
  (congrArg (fun a ↦ (a.counit.app K).hom)
    (unitBall_adjunction_eq ℓ E k (f.asOver (Spec (.of k))))).trans
    (restricted_counit_hom ℓ k _ (f.asOver (Spec (.of k))) _ K)

private lemma bounded_counit_hom_continuousMap
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (normedRing E) f).counit.app K.obj :=
  (congrArg (fun a ↦ (a.counit.app K).hom)
    (continuousMap_adjunction_eq ℓ E k (f.asOver (Spec (.of k))))).trans
    (restricted_counit_hom ℓ k _ (f.asOver (Spec (.of k))) _ K)

private lemma upperStar_map_hom {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {A B : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) U)} (φ : A ⟶ B) :
    ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (h.asOver (Spec (.of k)))).map φ).hom = (L((h)^*⟦normedRing E⟧)).map φ.hom :=
  rfl

private lemma integral_push_counit (K : integralConstructible ℓ E X) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (f.asOver (Spec (.of k)))).map
        (integralConstructiblePushHom ℓ E k f K) ≫
      (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
        (f.asOver (Spec (.of k)))).counit.app
          ((integralScalarConstructible ℓ E X).obj K) =
    (integralConstructiblePullIso ℓ E k f
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
        (f.asOver (Spec (.of k)))).obj K)).inv ≫
      (integralScalarConstructible ℓ E X).map
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ
          (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).counit.app K) := by
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) X) :=
    ProEtale.isCommMonObj_condensedRingObj _ X
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) Y) :=
    ProEtale.isCommMonObj_condensedRingObj _ Y
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  simp only [bounded_counit_hom_continuousMap ℓ E k f, upperStar_map_hom ℓ E k f]
  simp only [integralScalarConstructible, integralConstructiblePushHom,
    integralConstructiblePullIso, ObjectProperty.homMk_hom, ObjectProperty.isoMk_inv]
  simp only [bounded_counit_hom_unitBall ℓ E k f]
  simp only [derivedPushHom, derivedPullIso, integralScalarExtension, OverClass.asOverHom_left,
    UnitBallRingObj.boundedConstructibleLowerStar, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, Iso.app_inv]
  have hcc := coefficient_counit
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) Y))
    (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f)
    (derivedUpperStarLowerStarAdjunction _ f)
    (derivedComapLowerStarIso (integralScalarMap ℓ E) f) K.obj
  with_reducible exact hcc

private lemma continuous_baseChange_eq_squareExchange (sq : CommSq g' f' f g) :
    ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E (sq.asOver (Spec (.of k))) =
      Adjunction.squareExchange
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
          (f.asOver (Spec (.of k))))
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
          (f'.asOver (Spec (.of k))))
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g.asOver (Spec (.of k))))
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k))))
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
          (sq.asOver (Spec (.of k)))) :=
  (ContinuousMapRingObj.boundedConstructibleBaseChange_eq_exchangeRight ℓ E _).trans
    (Adjunction.squareExchange_eq_unit_square_counit _ _ _ _ _).symm

/-- Normal form for the source side after the bounded f′ adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean derived comparisons
and the specified unit-square-counit exchange construction.
(blueprint: lem-weil-pbc-continuous-integral-exchange-source-adjunct).

Proof. Apply the bounded f′ adjunction to the source composite. Expand functoriality, then
replace the exchange adjunct by square transport followed by the f counit. Naturality of the
square comparison moves the f push comparison past it. The iterated mate/conjugation identity
identifies pullback of that push comparison followed by the E counit with the inverse pull
comparison followed by scalar extension of the integral counit. These substitutions give exactly
the displayed composite. -/
theorem integralConstructible_exchange_source_adjunct
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k)))).homEquiv _ _).symm
      (integralConstructibleSourceHom ℓ E k f g K ≫
        (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
          (sq.asOver (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E X).obj K)) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k)))).map
        (integralConstructiblePullHom ℓ E k g
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
              (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
        (sq.asOver (Spec (.of k)))).hom.app
          ((integralScalarConstructible ℓ E Y).obj
            ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
              (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).map
        (integralConstructiblePullIso ℓ E k f
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).obj K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).map
        ((integralScalarConstructible ℓ E X).map
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ
            (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).counit.app K)) := by
  exact source_normal_form
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k))))
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k))))
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k))))
    (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
      (sq.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E (sq.asOver (Spec (.of k))))
    ((integralScalarConstructible ℓ E X).obj K)
    ((integralScalarConstructible ℓ E Y).obj
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
          (f.asOver (Spec (.of k)))).obj K))
    ((integralScalarConstructible ℓ E Y').obj
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullHom ℓ E k g
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
          (f.asOver (Spec (.of k)))).obj K))
    (integralConstructiblePushHom ℓ E k f K)
    ((integralScalarConstructible ℓ E X).obj
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullIso ℓ E k f
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
          (f.asOver (Spec (.of k)))).obj K)).inv
    ((integralScalarConstructible ℓ E X).map
      ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
        (f.asOver (Spec (.of k)))).counit.app K))
    (continuous_baseChange_eq_squareExchange ℓ E k f g f' g' sq)
    (integral_push_counit ℓ E k f K)

end AlgebraicGeometry.ProEtale.CondensedRing

-- The concrete identity's inferred instances make Lean's two premise-index export passes
-- expensive. Its name is used explicitly by `ContinuousIntegralExchangeEquality`; exclude just
-- this identity from suggestions using Lean's documented API.
run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "integralConstructible_exchange_source_adjunct"
