/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
public import WeilConjectures.CategoryTheory.ProperBaseChange.CoefficientExchangeCoherence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPullComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralExchangeTargetAdjunct

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

open CategoryTheory

section Diagrams
private lemma coefficientCube_of_iso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {lf : B ⥤ A} {lg : B ⥤ D} {lp : D ⥤ C} {gp : A ⥤ C}
    {Lf : B' ⥤ A'} {Lg : B' ⥤ D'} {Lp : D' ⥤ C'} {Gp : A' ⥤ C'}
    {tA : A ⥤ A'} {tB : B ⥤ B'} {tC : C ⥤ C'} {tD : D ⥤ D'}
    (αf : ∀ V, tA.obj (lf.obj V) ≅ Lf.obj (tB.obj V))
    (αg : ∀ V, tD.obj (lg.obj V) ≅ Lg.obj (tB.obj V))
    (αp : ∀ V, tC.obj (lp.obj V) ≅ Lp.obj (tD.obj V))
    (αq : ∀ V, tC.obj (gp.obj V) ≅ Gp.obj (tA.obj V))
    (sqE : lg ⋙ lp ≅ lf ⋙ gp) (sqΩ : Lg ⋙ Lp ≅ Lf ⋙ Gp) (V : B)
    (h : tC.mapIso (sqE.app V) ≪≫ αq (lf.obj V) ≪≫ Gp.mapIso (αf V) =
      αp (lg.obj V) ≪≫ Lp.mapIso (αg V) ≪≫ sqΩ.app (tB.obj V)) :
    coefficientPullbackCube αf αg αp αq sqE.hom sqΩ.hom V := by
  simpa only [coefficientPullbackCube, Category.assoc] using
    inverse_mapped_square Gp (αp (lg.obj V)) (αf V)
      (tC.map (sqE.hom.app V)) (αq (lf.obj V)).hom
      (Lp.map (αg V).hom ≫ sqΩ.hom.app (tB.obj V)) (congrArg Iso.hom h)

end Diagrams

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

section CompositionCalculation
attribute [local irreducible] constructibleToPadicAlgCl constructibleToQbarPullIso
  boundedConstructibleUpperStarComp

set_option maxHeartbeats 150000 in
-- The canonical module-object comparisons require repeated exactness instance inference.
/-- Composition coherence of the restricted coefficient pull comparison.
Source: ChangeOfCoefficients.lean, derivedPullIso; ContinuousIntegralPullComposition.lean,
derived_pull_comp and bounded_comp_hom (blueprint: lem-weil-pbc-qbar-condensed-pullback-cube).

Proof in words. Apply faithfulness of the bounded-constructible inclusion to the hom
components. The map of scalar extension is the ambient derived extension map, and the
bounded pullback composition maps have the ambient leftDerivedUpperStarComp components.
The composition equation derived_pull_comp, evaluated at K.obj, is precisely the resulting
ambient equation after removing the identity associator components. -/
private theorem qbarPullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : PadicSubfieldConstructible V ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ
          (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app K) ≪≫
      constructibleToQbarPullIso ℓ k E h
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (j.asOver (Spec (.of k)))).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (h.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E j K) =
    constructibleToQbarPullIso ℓ k E (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app
        ((constructibleToPadicAlgCl V ℓ E).obj K) := by
  set_option backward.isDefEq.respectTransparency false in
  apply Iso.ext
  apply ObjectProperty.hom_ext
  dsimp only [Iso.trans, Functor.mapIso, Iso.app,
    ObjectProperty.FullSubcategory.comp_hom]
  unfold constructibleToPadicAlgCl constructibleToQbarPullIso
  dsimp only [boundedConstructibleUpperStar,
    constructibleToQbarPullIso, ObjectProperty.lift, ObjectProperty.isoMk,
    ObjectProperty.homMk, Functor.comp_map, ObjectProperty.ι_map]
  conv_lhs =>
    lhs
    arg 2
    rw [bounded_comp_hom ℓ k (Profinite.continuousMapRingObj E) h j K]
  conv_rhs =>
    rhs
    erw [bounded_comp_hom ℓ k (Profinite.padicAlgClRingObj ℓ) h j _]
  have he := congr_app
    (derived_pull_comp (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h j) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at he
  convert he using 1 <;>
    dsimp only [constructibleToPadicAlgCl, ObjectProperty.lift_obj_obj,
      Functor.comp_obj, ObjectProperty.ι_obj, Iso.app_hom,
      derivedExtendScalarsToPadicAlgCl,
      padicSubfieldRingObjToPadicAlgCl, Scheme.Hom.asOver, OverClass.asOverHom,
      OverClass.asOver, Over.homMk, CostructuredArrow.homMk,
      Over.mk, CostructuredArrow.mk, Over.Hom.left]

end CompositionCalculation

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

set_option backward.isDefEq.respectTransparency true in
private lemma qbarPull_eq
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (j : T ⟶ U) [j.IsOver (Spec (.of k))] (w : h = j)
    (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((eqToIso (by subst j; rfl) :
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k))) ≅
            boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
              (j.asOver (Spec (.of k)))).app K) ≪≫
      constructibleToQbarPullIso ℓ k E j K =
    constructibleToQbarPullIso ℓ k E h K ≪≫
      (eqToIso (by subst j; rfl) :
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k))) ≅
          boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (j.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl U ℓ E).obj K) := by
  subst j
  change (constructibleToPadicAlgCl T ℓ E).mapIso (Iso.refl _) ≪≫ _ =
    _ ≪≫ Iso.refl _
  calc
    _ = Iso.refl _ ≪≫ constructibleToQbarPullIso ℓ k E h K :=
      congrArg (fun i ↦ i ≪≫ constructibleToQbarPullIso ℓ k E h K)
        ((constructibleToPadicAlgCl T ℓ E).mapIso_refl _)
    _ = _ := (Iso.refl_trans _).trans (Iso.trans_refl _).symm

section PullSquareCalculation
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] constructibleToPadicAlgCl
  constructibleToQbarPullIso
  boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarComp

/-- Paste composition coherence across the two paths of the commutative square.
Source: ContinuousIntegralExchangeTargetAdjunct.lean, mapped_iso_rectangle;
MorphismDefs.lean, boundedConstructiblePullbackSquareComparison_app
(blueprint: lem-weil-pbc-qbar-condensed-pullback-cube).

Proof in words. Apply qbarPullIso_comp to (g', f) and (f', g), and qbarPull_eq to the equal
composites, using sq.w.symm. Expand each pullback-square comparison into the inverse
composition comparison, equality transport and forward composition comparison. Paste
these three equations with mapped_iso_rectangle, cancelling the common composite
comparison. This proves the displayed equality of isomorphisms. -/
private lemma qbarPull_square_cube_iso
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).mapIso
        ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
          (sq.asOver (Spec (.of k)))).app M) ≪≫
      constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (f.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (g'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E f M) =
    constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E g M) ≪≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl Y ℓ E).obj M) := by
  have h₁ := qbarPullIso_comp ℓ k E g' f M
  have h₂ := qbarPullIso_comp ℓ k E f' g M
  have he := qbarPull_eq ℓ k E (f' ≫ g) (g' ≫ f) sq.w.symm M
  have hp := mapped_iso_rectangle (constructibleToPadicAlgCl X' ℓ E)
    _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ he
  have te := boundedConstructiblePullbackSquareComparison_app
    (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k))) M
  have tOmega := boundedConstructiblePullbackSquareComparison_app
    (Profinite.padicAlgClRingObj ℓ) ℓ (sq.asOver (Spec (.of k)))
    ((constructibleToPadicAlgCl Y ℓ E).obj M)
  have heq := congrArg (fun t ↦
    (constructibleToPadicAlgCl X' ℓ E).mapIso t ≪≫
      constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (f.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (g'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E f M)) te
  have hoq := congrArg (fun t ↦
    constructibleToQbarPullIso ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E g M) ≪≫ t) tOmega
  exact heq.trans (hp.trans hoq.symm)

end PullSquareCalculation
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] constructibleToPadicAlgCl constructibleToQbarPullIso
  boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarComp boundedConstructiblePullbackSquareComparison
  coefficientPullbackCube

/-- Coefficient pullback comparisons commute with the specified geometric square comparison.
Source: ChangeOfCoefficients.lean, derivedPullIso and derivedComapLowerStarIso;
UpperLowerStar/Defs.lean, upperStarComp; Derived/UpperLowerStar.lean, leftDerivedUpperStarComp;
TwoColimit.lean, final transport paragraph
(blueprint: lem-weil-pbc-qbar-condensed-pullback-cube).

Proof in words. Restriction of scalars followed by geometric direct image and geometric
direct image followed by restriction have the same underlying sheaf functor; the natural
isomorphism comapLowerStarIso is the identity on underlying sheaves. Its compatibility
with direct-image composition follows by forgetting the action, which is faithful, and
using associativity of direct-image composition. The change-of-coefficients square for
the coefficient maps follows from their naturality. Derive these commuting diagrams using
K-injective resolutions: restriction is exact and preserves K-injectives since its left
adjoint is exact, and direct images preserve K-injectives. The universal property of the
right derived functor identifies the resulting comparison with derivedComapLowerStarIso
and preserves its composition equation. Conjugate that equation along the two geometric
adjunctions and the extension/restriction adjunctions. Conjugation respects composition
and associators, giving compatibility of derivedPullIso with geometric composition.
The geometric composition maps are the specified leftDerivedUpperStarComp: derive the
underived adjunction-conjugate composition equation and use uniqueness of derived
adjunctions, with exact pullbacks computed termwise. Apply this composition equation to
(f', g) and (g', f), transport along sq.w, and cancel the common comparison for the equal
composite. Naturality under equality and proof irrelevance handle the commutativity proof.
This gives the pullback cube in the displayed inverse-alpha_f' orientation. Restrict along
the fully faithful bounded constructible inclusions, whose composition constraints are
restrictions of these same maps. This proof uses no base-change exchange morphism, no
push comparison, and no properness or Cartesianity. For identity morphisms the equation
reduces to the unit coherence; for a zero object both sides are its unique morphism. -/
theorem constructibleToQbar_pullback_cube
    (sq : CommSq g' f' f g) (V : PadicSubfieldConstructible Y ℓ E) :
    coefficientPullbackCube
    (A := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (X.asOver (Spec (.of k))).left))
    (B := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (Y.asOver (Spec (.of k))).left))
    (C := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (X'.asOver (Spec (.of k))).left))
    (D := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E) (Y'.asOver (Spec (.of k))).left))
    (A' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (X.asOver (Spec (.of k))).left))
    (B' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (Y.asOver (Spec (.of k))).left))
    (C' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (X'.asOver (Spec (.of k))).left))
    (D' := AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (Y'.asOver (Spec (.of k))).left))
    (lf := boundedConstructibleUpperStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (f.asOver (Spec (.of k))))
    (lg := boundedConstructibleUpperStar (k := k)
      (X := Y'.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (g.asOver (Spec (.of k))))
    (lp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k))))
    (gp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := X.asOver (Spec (.of k)))
        (Profinite.continuousMapRingObj E) ℓ
      (g'.asOver (Spec (.of k))))
    (Lf := boundedConstructibleUpperStar (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (f.asOver (Spec (.of k))))
    (Lg := boundedConstructibleUpperStar (k := k)
      (X := Y'.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (g.asOver (Spec (.of k))))
    (Lp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := Y'.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (f'.asOver (Spec (.of k))))
    (Gp := boundedConstructibleUpperStar (k := k)
      (X := X'.asOver (Spec (.of k))) (Y := X.asOver (Spec (.of k)))
        (Profinite.padicAlgClRingObj ℓ) ℓ
      (g'.asOver (Spec (.of k))))
    (tA := constructibleToPadicAlgCl X ℓ E)
    (tB := constructibleToPadicAlgCl Y ℓ E)
    (tC := constructibleToPadicAlgCl X' ℓ E)
    (tD := constructibleToPadicAlgCl Y' ℓ E)
    (fun V ↦ constructibleToQbarPullIso ℓ k E f V)
    (fun V ↦ constructibleToQbarPullIso ℓ k E g V)
    (fun V ↦ constructibleToQbarPullIso ℓ k E f' V)
    (fun V ↦ constructibleToQbarPullIso ℓ k E g' V)
    (boundedConstructiblePullbackSquareComparison (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k)))).hom
    (boundedConstructiblePullbackSquareComparison (k := k)
      (X := X.asOver (Spec (.of k))) (Y := Y.asOver (Spec (.of k)))
      (X' := X'.asOver (Spec (.of k))) (Y' := Y'.asOver (Spec (.of k)))
      (Profinite.padicAlgClRingObj ℓ) ℓ (sq.asOver (Spec (.of k)))).hom
    V := by
  exact coefficientCube_of_iso _ _ _ _ _ _ V
    (qbarPull_square_cube_iso ℓ k E f g f' g' sq V)

end AlgebraicGeometry.ProEtale.CondensedRing
