/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Specified compact-support base-change maps

Source: blueprint proposition-composition-base-change-rf-shriek--4, definitions used in clauses
(1)--(3). These are the existing constructions, separated so refinement pasting can use their exact
maps. (blueprint: def-sfb-compact-support-base-change-maps).
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace CategoryTheory.Functor

/-- The two-factor exchange with its component API.
Source: blueprint beta is the proper exchange followed by the image of the open comparison.
(blueprint: def-sfb-compact-support-base-change-maps). -/
structure CompactSupportExchangeData
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (J : A ⥤ B) (P : B ⥤ C) (V : C ⥤ D)
    (W : B ⥤ E) (Q : E ⥤ D) (U : A ⥤ F) (J' : F ⥤ E)
    (b : P ⋙ V ⟶ W ⋙ Q) (o : J ⋙ W ≅ U ⋙ J') where
  map : (J ⋙ P) ⋙ V ⟶ U ⋙ J' ⋙ Q
  component (K : A) : map.app K = b.app (J.obj K) ≫ Q.map (o.hom.app K)
  isIso (K : A) : IsIso (b.app (J.obj K)) → IsIso (map.app K)

/-- Construct the two-factor exchange and prove its component properties.
Source: the displayed proper/open composite defining beta.
(blueprint: def-sfb-compact-support-base-change-maps). -/
def compactSupportExchangeData
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (J : A ⥤ B) (P : B ⥤ C) (V : C ⥤ D)
    (W : B ⥤ E) (Q : E ⥤ D) (U : A ⥤ F) (J' : F ⥤ E)
    (b : P ⋙ V ⟶ W ⋙ Q) (o : J ⋙ W ≅ U ⋙ J') :
    CompactSupportExchangeData J P V W Q U J' b o where
  map := whiskerLeft J b ≫ whiskerRight o.hom Q
  component _ := rfl
  isIso K h := IsIso.comp_isIso' h (Functor.map_isIso Q (o.hom.app K))

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

/-- The module-object derived pullback used in the base-change statement.
Source: the module-object six-functor definitions
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
noncomputable abbrev detSfDerivedPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} (h : A ⟶ B) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)) :=
  L((h)^*⟦Λ⟧)

/-- The derived lower-shriek functor attached to a compactification.
Source: the module-object six-functor definitions
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
noncomputable abbrev detSfCompactSupport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} {h : A ⟶ B}
    (d : Compactification h) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)) :=
  rightDerivedLowerShriekOfCompactification Λ d

/-- The specified Cartesian realization of the literal proper pullback square.
Source: blueprint proposition-composition-base-change-rf-shriek--4, proper exchange.
(blueprint: def-sfb-compact-support-base-change-maps). -/
def detSfProperBaseChangeSquare
    {Z Y Y' : Scheme.{u}} (p : Z ⟶ Y) (v : Y' ⟶ Y) :
    ChosenCartesianSquare (pullback.fst p v) (pullback.snd p v) p v :=
  { toCommSq := ⟨pullback.condition⟩
    isoPullback := Iso.refl _
    hom_fst := Category.id_comp _
    hom_snd := Category.id_comp _ }

/-- The published ambient base-change mate for the literal proper pullback square.
This abbreviation only supplies the identity identification with the chosen fibre product;
it makes no new choice of exchange map. Source: blueprint
 proposition-composition-base-change-rf-shriek--4, proof step 4
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
noncomputable abbrev detSfProperBaseChangeMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z Y Y' : Scheme.{u}} (p : Z ⟶ Y) (v : Y' ⟶ Y) :
    (R((p)_*⟦Λ⟧) ⋙ detSfDerivedPullback Λ v) ⟶
      (detSfDerivedPullback Λ (pullback.fst p v) ⋙ R((pullback.snd p v)_*⟦Λ⟧)) :=
  condensedAmbientExchange Λ (detSfProperBaseChangeSquare p v)

/-- The canonical open exchange arrow, in the inverse direction to clause (1).
Source: blueprint proposition-composition-base-change-rf-shriek--4, proof steps 1--2. Insert the
open unit, transport the pullback square, and contract the base-changed open counit. Thus an
isomorphism whose inverse equals this arrow has a specified normalization
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
def detSfOpenBaseChangeMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    (detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧)) ⟶
      (D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v)) :=
  let sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  let θ := condensedAmbientPullbackComparison Λ
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).unit
      (detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧)) ≫
    (Functor.squareTransport D((c.i)_!open⟦Λ⟧) D(((c.baseChange v).i)_!open⟦Λ⟧)
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ c.i).symm
          (detSfDerivedPullback Λ (pullback.fst f v)) ≪≫
        θ.symm ≪≫
        Functor.isoWhiskerLeft (detSfDerivedPullback Λ (pullback.fst c.g v))
          (leftDerivedUpperStarIsoMapDerivedCategory Λ (c.baseChange v).i))).hom ≫
    Functor.whiskerLeft (D((c.i)_!open⟦Λ⟧) ⋙
        detSfDerivedPullback Λ (pullback.fst c.g v))
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (c.baseChange v).i).counit ≫
    (Functor.rightUnitor _).hom

/-- Regard a compactification of a quasi-compact morphism as an object of the published
boundary-refinement category. Its open is quasi-compact by the existing factorization lemma.
Source: blueprint proposition-composition-base-change-rf-shriek--4, proof step 5
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
def detSfBoundaryCompactification
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    Compactification.BoundaryCompactification f :=
  ⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩

/-- The canonical, common-dense-refinement-normalized comparison family of the recorded
coherence theorem, evaluated on the existing compactification objects. The theorem determines
this family uniquely by its equation against every common dense refinement; identity and
cocycle laws alone would not determine it. No comparison on the whole unbounded category is
chosen. Source: blueprint proposition-construction-independence-rf-shriek and
 proposition-composition-base-change-rf-shriek--4, proof steps 5 and 8
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
noncomputable def detSfCanonicalCompactificationComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) :
    ((localizingClosureProEtale Λ X).ι ⋙ detSfCompactSupport Λ c₁) ≅
      ((localizingClosureProEtale Λ X).ι ⋙ detSfCompactSupport Λ c₂) :=
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  letI : X.Over (Spec (.of k)) := ⟨f ≫ (Y ↘ Spec (.of k))⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))))
  haveI : QuasiCompact (X ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (f ≫ (Y ↘ Spec (.of k))))
  haveI : IsSeparated (X ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (f ≫ (Y ↘ Spec (.of k))))
  haveI : f.IsOver (Spec (.of k)) := ⟨rfl⟩
  Classical.choose (compactification_coherence_cocycle Λ ℓ hΛ k f)
    (detSfBoundaryCompactification c₁) (detSfBoundaryCompactification c₂)

attribute [local irreducible] derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStarLowerStarAdjunction condensedAmbientPullbackComparison
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  condensedAmbientExchange upperStar lowerStar openImmersionLowerShriek
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Package the specified map with its component properties.
Source: blueprint proposition-composition-base-change-rf-shriek--4, displayed beta.
(blueprint: def-sfb-compact-support-base-change-maps). -/
noncomputable def detSfCompactSupportExchangeData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (c : Compactification f) (o :
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙
          D(((c.baseChange v).i)_!open⟦Λ⟧)) :
    Functor.CompactSupportExchangeData
    D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧) (detSfDerivedPullback Λ v)
    (detSfDerivedPullback Λ (pullback.fst c.g v)) R((pullback.snd c.g v)_*⟦Λ⟧)
    (detSfDerivedPullback Λ (pullback.fst f v)) D(((c.baseChange v).i)_!open⟦Λ⟧)
    (detSfProperBaseChangeMap Λ c.g v) o :=
  Functor.compactSupportExchangeData
    D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧) (detSfDerivedPullback Λ v)
    (detSfDerivedPullback Λ (pullback.fst c.g v)) R((pullback.snd c.g v)_*⟦Λ⟧)
    (detSfDerivedPullback Λ (pullback.fst f v)) D(((c.baseChange v).i)_!open⟦Λ⟧)
    (detSfProperBaseChangeMap Λ c.g v) o

/-- The specified compact-support exchange composite: the published proper-base-change mate
followed by `Rp'_*` applied to the normalized open/base-change comparison.
Source: blueprint proposition-composition-base-change-rf-shriek--4, clause (2) and proof steps 3--4
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
noncomputable def detSfCompactSupportBaseChangeComposite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (c : Compactification f) (o :
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙
          D(((c.baseChange v).i)_!open⟦Λ⟧)) :
    (detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ v) ⟶
      (detSfDerivedPullback Λ (pullback.fst f v) ⋙
        detSfCompactSupport Λ (c.baseChange v)) :=
  (detSfCompactSupportExchangeData Λ f v c o).map

end AlgebraicGeometry.ProEtale.CondensedRing
