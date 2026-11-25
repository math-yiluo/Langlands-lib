/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

import WeilConjectures.AlgebraicGeometry.RationalP1.AffineLineAdjunctionAssembly
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction

/-!
# Rational affine-line compact-support adjunction

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-cor-affine-space-rational/sk-cor-affine-space-rational-line.md`
(blueprint: theorem-f-shriek-ell-adic-coefficients).

## Main declarations

* `rationalLocalizingCategory`, `rationalLocalizingInclusion`: literal Loc(Dbc) and inclusion.
* `rationalTwistFunctor`: the existing derived tensor specialized to a Tate line.
* `affineLineChosenCompactification`: the published Nagata choice for the affine projection.
* `affineLineRationalAssertion`: the three clauses for one coefficient convention.
* `det_cor_affine_space_rational_line`: both rational coefficient cases.

The statement records the standard affine chart of the relative projective line, the
compactification lower-shriek functor, and the Tate-twisted shifted pullback.  The two
coefficient constructors below are the finite-subextension and finite-subextension-valued
algebraic-closure conventions of the source.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme MonoidalCategory
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar Functor.leftDerivedFunctor Functor.mapDerivedCategory

/-- The recorded Nagata choice for the affine projection as a morphism over k.
The instance arguments are the existing affine-space and composition instances, written
explicitly because typeclass search does not unfold the Over-object projections here.
Source: blueprint `sk-def-sfb-dc-setting`, chosen compactification convention
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
noncomputable def affineLineChosenCompactification
    (k : Type u) [Field k] (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))] :
    Compactification (𝔸(PUnit.{u + 1}; V) ↘ V) :=
  @compactificationOverField k _
    (Over.mk ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k))))
    (Over.mk (V ↘ Spec (.of k)))
    (inferInstanceAs (LocallyOfFiniteType
      ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact
      ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (IsSeparated
      ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact (V ↘ Spec (.of k))))
    (inferInstanceAs (IsSeparated (V ↘ Spec (.of k))))
    (Over.homMk (𝔸(PUnit.{u + 1}; V) ↘ V) rfl)

attribute [local irreducible] affineLineChosenCompactification

/-- The complete assertion for one of the two rational coefficient conventions.
Source: blueprint `sk-cor-affine-space-rational-line`
(blueprint: theorem-f-shriek-ell-adic-coefficients).
The comparison isomorphisms to the ambient derived categories make every displayed functor
be the specified module-object functor, rather than an unrelated functor between subcategories.
-/
noncomputable def affineLineRationalAssertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (V : Scheme.{u})
    (c : Compactification (𝔸(PUnit.{u + 1}; V) ↘ V))
    (twist : ∀ X : Scheme.{u},
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) : Prop :=
  ∃ (J : rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)) ⥤
        rationalLocalizingCategory Λ (ProjectiveLine V))
    (R : rationalLocalizingCategory Λ (ProjectiveLine V) ⥤
        rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)))
    (_hJ : J ⋙ rationalLocalizingInclusion Λ (ProjectiveLine V) ≅
      rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ⋙
        D((ProjectiveLine.affineChart V)_!open⟦Λ⟧))
    (_hR : R ⋙ rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ≅
      rationalLocalizingInclusion Λ (ProjectiveLine V) ⋙
        D((ProjectiveLine.affineChart V)^*⟦Λ⟧))
    (_adjJ : J ⊣ R)
    (F : rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)) ⥤
        rationalLocalizingCategory Λ V)
    (Q : rationalLocalizingCategory Λ (ProjectiveLine V) ⥤
        rationalLocalizingCategory Λ V)
    (_hF : F ⋙ rationalLocalizingInclusion Λ V ≅
      rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ⋙
        rightDerivedLowerShriekOfCompactification Λ c)
    (_hQ : Q ⋙ rationalLocalizingInclusion Λ V ≅
      rationalLocalizingInclusion Λ (ProjectiveLine V) ⋙
        R((ProjectiveLine V ↘ V)_*⟦Λ⟧))
    (_hcomp : F ≅ J ⋙ Q)
    (P : rationalLocalizingCategory Λ V ⥤
        rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)))
    (_hP : P ⋙ rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ≅
      rationalLocalizingInclusion Λ V ⋙
        (CondensedRing.upperStar Λ (𝔸(PUnit.{u + 1}; V) ↘ V)).leftDerivedFunctor ⋙
          twist (𝔸(PUnit.{u + 1}; V)) ⋙ shiftFunctor _ (2 : ℤ))
    (adjP : CategoryTheory.Adjunction F P),
    ∀ (G : rationalLocalizingCategory Λ V ⥤
        rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)))
      (adjG : CategoryTheory.Adjunction F G),
    ∃! (e : G ≅ P), (∀ N,
      F.map (e.hom.app N) ≫ adjP.counit.app N = adjG.counit.app N)

private theorem rationalClosureEq
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    localizingClosureProEtale (RationalP1.coefficient ℓ c).X X =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X X) := by
  apply (localizingClosure_ctf_equals_bc ℓ X (RationalP1.coefficient ℓ c).X ?_).1.2.2.2.1
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | some E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))

private theorem rationalAdmissible
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ)) :
    IsLocalizingAdmissibleCoefficient ℓ (RationalP1.coefficient.{u} ℓ c).X := by
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  | some E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))

private theorem rationalOpenAdjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    ∃ (J : rationalLocalizingCategory (RationalP1.coefficient ℓ c).X U ⥤
          rationalLocalizingCategory (RationalP1.coefficient ℓ c).X X)
      (R : rationalLocalizingCategory (RationalP1.coefficient ℓ c).X X ⥤
          rationalLocalizingCategory (RationalP1.coefficient ℓ c).X U),
      Nonempty (J ⋙ rationalLocalizingInclusion (RationalP1.coefficient ℓ c).X X ≅
        rationalLocalizingInclusion (RationalP1.coefficient ℓ c).X U ⋙
          (openImmersionLowerShriek (RationalP1.coefficient ℓ c).X j).mapDerivedCategory) ∧
      Nonempty (R ⋙ rationalLocalizingInclusion (RationalP1.coefficient ℓ c).X U ≅
        rationalLocalizingInclusion (RationalP1.coefficient ℓ c).X X ⋙
          (upperStar (RationalP1.coefficient ℓ c).X j).mapDerivedCategory) ∧
      Nonempty (J ⊣ R) := by
  unfold rationalLocalizingCategory rationalLocalizingInclusion
  rw [← rationalClosureEq ℓ c U, ← rationalClosureEq ℓ c X]
  obtain ⟨he, hs, _, adj, _⟩ := mateOpenImmersion (RationalP1.coefficient ℓ c).X ℓ k
    (ringChar k) (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ)
    (rationalAdmissible ℓ c) j
  exact ⟨mateOpenExtension _ j he, mateOpenPullback _ j hs,
    ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨adj⟩⟩

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [-instance] RationalP1.internalMonoidal RationalP1.internalTensorCommShift
  supportModules_grothendieck hasTensor_cochainComplex monoidalCategoryStruct_cochainComplex
  monoidalCategory_cochainComplex in
section

attribute [local irreducible] RationalP1.line RationalP1.lineComparison
  monoidal_leftDerivedUpperStar Functor.singleFunctorCompLeftDerivedFunctorIso
  RationalP1.coefficient upperStarFromPoint DerivedCategory.singleFunctors
  Mod.monoidalClosed DerivedCategory.monoidalClosed
  RationalP1.push RationalP1.exceptional

@[irreducible] private noncomputable def shiftedTensorPullIso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.Monoidal] [F.CommShift ℤ]
    (L : C) (M : D) (e : F.obj L ≅ M) :
    (tensorRight L ⋙ shiftFunctor C (2 : ℤ)) ⋙ F ≅
      F ⋙ tensorRight M ⋙ shiftFunctor D (2 : ℤ) :=
  Functor.isoWhiskerLeft (tensorRight L) (F.commShiftIso (2 : ℤ)) ≪≫
    Functor.isoWhiskerRight ((Functor.Monoidal.commTensorRight F L).symm ≪≫
      Functor.isoWhiskerLeft F ((curriedTensor D).flip.mapIso e))
      (shiftFunctor D (2 : ℤ))

@[irreducible] private noncomputable def pullSingleLineIso
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    (moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f).obj
      ((DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c Y)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X) :=
  ((upperStar (RationalP1.coefficient ℓ c).X f).singleFunctorCompLeftDerivedFunctorIso.app _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (RationalP1.lineComparison ℓ c f)

@[irreducible] private noncomputable def rationalTwistPullIso
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    RationalP1.twist (RationalP1.coefficient ℓ c).X Y (RationalP1.line ℓ c Y) ⋙
      (upperStar (RationalP1.coefficient ℓ c).X f).mapDerivedCategory ≅
    (upperStar (RationalP1.coefficient ℓ c).X f).leftDerivedFunctor ⋙
      RationalP1.twist (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X) := by
  let Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
    (RationalP1.coefficient ℓ c).X
  let F : DerivedCategory (DiagonalCoefficients.Modules Λ Y) ⥤
      DerivedCategory (DiagonalCoefficients.Modules Λ X) := moduleObjectDerivedPullback Λ f
  let : F.Monoidal := monoidal_leftDerivedUpperStar Λ f
  let : F.CommShift ℤ := unboundedLocalizingPullbackCommShift Λ f
  let LY := (DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c Y)
  let LX := (DerivedCategory.singleFunctor _ 0).obj (RationalP1.line ℓ c X)
  let e : F.obj LY ≅ LX :=
    pullSingleLineIso ℓ c f
  dsimp only [RationalP1.twist, rationalTwistFunctor, derivedTensor]
  exact Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ≪≫
    shiftedTensorPullIso F LY LX e

private theorem counitCompatibleUnique
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {P G : D ⥤ C}
    (adjP : F ⊣ P) (adjG : F ⊣ G) :
    ∃! e : G ≅ P, ∀ N, F.map (e.hom.app N) ≫ adjP.counit.app N = adjG.counit.app N := by
  refine ⟨adjG.rightAdjointUniq adjP, fun N ↦
    adjG.rightAdjointUniq_hom_app_counit adjP N, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (adjP.homEquiv _ N).symm.injective
  exact (he N).trans (adjG.homEquiv_symm_rightAdjointUniq_hom_app adjP N).symm

/-- Compose the open and projective-line adjunctions for a unified rational coefficient. -/
private theorem rationalAffineLineOne
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (c : Option (PadicAlgCl.FiniteIntermediateField ℓ)) :
      affineLineRationalAssertion (RationalP1.coefficient ℓ c).X V
        (affineLineChosenCompactification k V)
        (fun X ↦ rationalTwistFunctor (RationalP1.coefficient ℓ c).X X
          (RationalP1.line ℓ c X)) := by
  let Λ := (RationalP1.coefficient ℓ c).X
  let A := 𝔸(PUnit.{u + 1}; V)
  let B := ProjectiveLine V
  let p : A ⟶ V := A ↘ V
  let q : B ⟶ V := B ↘ V
  let j : A ⟶ B := ProjectiveLine.affineChart V
  let : A.Over (Spec (.of k)) := ⟨p ≫ (V ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (A ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ (V ↘ Spec (.of k))))
  have : QuasiCompact (A ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (p ≫ (V ↘ Spec (.of k))))
  have : IsSeparated (A ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (p ≫ (V ↘ Spec (.of k))))
  have : LocallyOfFiniteType (B ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (q ≫ (V ↘ Spec (.of k))))
  have : QuasiCompact (B ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (q ≫ (V ↘ Spec (.of k))))
  have : IsSeparated (B ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (q ≫ (V ↘ Spec (.of k))))
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of k))
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace V :=
    quasiSeparatedSpace_of_quasiSeparated (V ↘ Spec (.of k))
  have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
  have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated q
  have : QuasiCompact j := quasiCompact_of_compactSpace j
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian
    (V ↘ Spec (.of k))
  have : IsNoetherian V := ⟨⟩
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian B := ⟨⟩
  have : CompactSpace (diagonalSurface V) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst q q)
  have : IsLocallyNoetherian (diagonalSurface V) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst q q)
  have : IsNoetherian (diagonalSurface V) := ⟨⟩
  obtain ⟨J, R, ⟨hJ⟩, ⟨hR⟩, ⟨adjJ⟩⟩ := rationalOpenAdjunction ℓ c k j
  let Q := RationalP1.push ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ) V
  let S := RationalP1.exceptional ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ) V
  obtain ⟨adjQ⟩ := RationalP1.rationalP1_adjunction_assembly ℓ c k V
  let F := J ⋙ Q
  let P := S ⋙ R
  have hQ : Q ⋙ rationalLocalizingInclusion Λ V ≅
      rationalLocalizingInclusion Λ B ⋙ (lowerStar Λ q).rightDerivedFunctor := by
    unfold Q RationalP1.push
    exact Iso.refl _
  have hS : S ⋙ rationalLocalizingInclusion Λ B ≅
      rationalLocalizingInclusion Λ V ⋙ (upperStar Λ q).leftDerivedFunctor ⋙
        RationalP1.twist Λ B (RationalP1.line ℓ c B) := by
    unfold S RationalP1.exceptional
    exact Iso.refl _
  let standard : Compactification p :=
    { Z := B, g := q, i := j, comm := (ProjectiveLine.affineChart_over V).symm,
      isProper := inferInstance, isOpenImmersion := inferInstance }
  let c₀ : Compactification.BoundaryCompactification p :=
    ⟨⟨affineLineChosenCompactification k V,
      (affineLineChosenCompactification k V).quasiCompact_openImmersion inferInstance⟩⟩
  let c₁ : Compactification.BoundaryCompactification p := ⟨⟨standard, inferInstance⟩⟩
  have : p.IsOver (Spec (.of k)) := ⟨rfl⟩
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ (rationalAdmissible ℓ c) k p
  have hA := rationalClosureEq ℓ c A
  let I : rationalLocalizingCategory Λ A ⥤ (localizingClosureProEtale Λ A).FullSubcategory :=
    (localizingClosureProEtale Λ A).lift (rationalLocalizingInclusion Λ A)
      (fun K ↦ hA.symm ▸ K.property)
  have hF : F ⋙ rationalLocalizingInclusion Λ V ≅
      rationalLocalizingInclusion Λ A ⋙
        rightDerivedLowerShriekOfCompactification Λ (affineLineChosenCompactification k V) :=
    Functor.isoWhiskerLeft J hQ ≪≫
      Functor.isoWhiskerRight hJ (lowerStar Λ q).rightDerivedFunctor ≪≫
        Functor.isoWhiskerLeft I (φ c₁ c₀)
  let : ∀ x : A, Invertible (ℓ : A.residueField x) := fun x ↦
    (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
      A (A ↘ Spec (.of k)) x).invertible
  let : ∀ x : B, Invertible (ℓ : B.residueField x) := fun x ↦
    (RationalP1.residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
      B (B ↘ Spec (.of k)) x).invertible
  have hcomp : (upperStar Λ q).leftDerivedFunctor ⋙
      (upperStar Λ j).leftDerivedFunctor ≅ (upperStar Λ p).leftDerivedFunctor :=
    (leftDerivedUpperStarComp Λ j q).symm ≪≫
      eqToIso (congrArg (fun f : A ⟶ V ↦ moduleObjectDerivedPullback Λ f)
        (ProjectiveLine.affineChart_over V))
  have hP : P ⋙ rationalLocalizingInclusion Λ A ≅
      rationalLocalizingInclusion Λ V ⋙ (upperStar Λ p).leftDerivedFunctor ⋙
        RationalP1.twist Λ A (RationalP1.line ℓ c A) :=
    Functor.isoWhiskerLeft S hR ≪≫
      Functor.isoWhiskerRight hS (upperStar Λ j).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (rationalLocalizingInclusion Λ V ⋙
        (upperStar Λ q).leftDerivedFunctor) (rationalTwistPullIso ℓ c j) ≪≫
      Functor.isoWhiskerLeft (rationalLocalizingInclusion Λ V)
        (Functor.isoWhiskerRight hcomp (RationalP1.twist Λ A (RationalP1.line ℓ c A)))
  let adjP : F ⊣ P := adjJ.comp adjQ
  exact ⟨J, R, hJ, hR, adjJ, F, Q, hF, hQ, Iso.refl _, P, hP, adjP,
    fun G adjG ↦ counitCompatibleUnique adjP adjG⟩

end

attribute [local semireducible] RationalP1.coefficient RationalP1.line

/-- Rational affine-line compact-support adjunction, for every finite coefficient
subextension and for the finite-subextension-valued algebraic closure.  The three assertions
are respectively clauses (1), (2), and (3) of the source statement.
Source: blueprint `sk-cor-affine-space-rational-line`
(blueprint: theorem-f-shriek-ell-adic-coefficients).

Proof (the ten steps of the DAG node):
1. The standard-chart theorem gives j and qj = p; finite-coordinate projective-space
properness gives proper q (`lemma-nagata-relative-affine-space-open-immersion`,
`lemma-nagata-projective-space-base-change-proper`).
2. On Spec R the affine projection is Spec R[t] -> Spec R, hence affine and locally of
finite type (`def-nagata-relative-affine-space`, `def-weil-finite-type-morphism`).
3. Affine-morphism permanence gives p quasi-compact and separated; proper q is separated
and quasi-compact. The qcqs-over-affine and qcqs permanence nodes give quasi-compact
V, affine line and projective line (`lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-qcqs-over-affine`, `lem-weil-pbc-qcqs-morphism-permanence`).
4. Composition preserves separatedness and local finite type; quasi-compactness over
Spec k follows from its quasi-separatedness. Both total spaces are separated finite-type
k-schemes and qcqs (`lem-weil-pbc-proper-fp-permanence`,
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-qcqs-morphism-permanence`).
5. A map from a quasi-compact scheme to a quasi-separated scheme is quasi-compact, so j
is quasi-compact and (j,q) is a compactification (`definition-compactification-refinement`).
6. For these rational coefficients Dctf = Dbc and their localizing closures agree.
Apply clause 1 of `proposition-composition-open-restriction-compactifications-f` and transport
across this equality (`det-def-localizing-closure-ctf-equals-bc`). This proves preservation and J
adjoint R.
7. For (j,q), lower shriek is Rq_* j_! by definition. Compare the chosen compactification
to this one by `proposition-construction-independence-rf-shriek`, then use step 6 to obtain F
isomorphic JQ.
8. Strong monoidality of derived pullback, its single-functor comparison and the
canonical rational Tate-line pullback identify tensoring with the pulled-back line.
The pullback CommShift comparison moves shift two, and derived pullback composition
identifies the result with p-star followed by the Tate twist and shift two.
9. Supply the canonical diagonal data to the projective-line triangle theorem through
`lem-sfb-rational-p1-adjunction-assembly`. Compose its adjunction Q adjoint S with
J adjoint R to obtain JQ adjoint SR. Steps 7 and 8 identify the ambient functors.
10. For any other right adjoint G of F, Mathlib's `Adjunction.rightAdjointUniq` gives
the isomorphism G to P and the counit identity. Injectivity of the adjunction Hom
bijection proves uniqueness, component by component.
-/
theorem det_cor_affine_space_rational_line
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      affineLineRationalAssertion (Profinite.continuousMapRingObj E.1) V
        (affineLineChosenCompactification k V)
        (fun X ↦ rationalTwistFunctor (Profinite.continuousMapRingObj E.1) X
          (spRationalTwist X ℓ E))) ∧
    affineLineRationalAssertion (Profinite.padicAlgClRingObj ℓ) V
      (affineLineChosenCompactification k V)
      (fun X ↦ rationalTwistFunctor (Profinite.padicAlgClRingObj ℓ) X
        (spQbarTwist X ℓ)) := by
  constructor
  · intro E
    simpa only [RationalP1.coefficient, RationalP1.line] using
      rationalAffineLineOne ℓ k V (some E)
  · simpa only [RationalP1.coefficient, RationalP1.line] using
      rationalAffineLineOne ℓ k V none

end AlgebraicGeometry.ProEtale.CondensedRing
