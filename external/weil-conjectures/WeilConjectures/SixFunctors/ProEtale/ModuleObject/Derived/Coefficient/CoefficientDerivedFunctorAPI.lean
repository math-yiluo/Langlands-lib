/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.ProperBaseChange.FiniteDiscreteThreeStepComparison.FiniteDiscreteRealizationCore

/-! # Derived functor interfaces for condensed coefficient comparisons

Source: the existing internal-module derived adjunction and pullback composition
isomorphisms (blueprint: def-weil-pbc-coefficient-derived-functor-api).
The four functor definitions are moved verbatim from FiniteDiscreteDerivedCoefficientData.
The partial comparison record keeps only inverse-image data and square coherence.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance coefficientProfiniteEssentiallySmall :
    EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section DerivedFunctorAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S T : Scheme.{u}} (h : S ⟶ T)

/-- The derived pullback with its derivability instances fixed at a generic coefficient ring. -/
noncomputable def coefficientDerivedUpperStar :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :=
  L((h)^*⟦Λ⟧)

/-- The derived pushforward with its derivability instances fixed at a generic coefficient ring. -/
noncomputable def coefficientDerivedLowerStar :
    DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  R((h)_*⟦Λ⟧)

/-- The derived coefficient adjunction, with the cached derived functor interfaces. -/
@[no_expose, irreducible] noncomputable def coefficientDerivedAdjunction :
    coefficientDerivedUpperStar Λ h ⊣ coefficientDerivedLowerStar Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

/-- Equation for the cached coefficient adjunction. -/
theorem coefficientDerivedAdjunction_eq : coefficientDerivedAdjunction Λ h =
    derivedUpperStarLowerStarAdjunction Λ h := by
  unfold coefficientDerivedAdjunction
  rfl

end DerivedFunctorAPI

/-- Composition of derived pullbacks, with the cached functors in its signature. -/
noncomputable def coefficientDerivedUpperStarComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    coefficientDerivedUpperStar Λ (f ≫ g) ≅
      coefficientDerivedUpperStar Λ g ⋙ coefficientDerivedUpperStar Λ f :=
  leftDerivedUpperStarComp Λ f g

/-- Compose three natural isomorphisms through their objectwise components. -/
noncomputable def coefficientIsoTransThree
    {C D : Type*} [Category C] [Category D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) : F₀ ≅ F₃ :=
  NatIso.ofComponents (fun N ↦ a.app N ≪≫ b.app N ≪≫ c.app N) (by
    intro N M k
    simp only [Iso.trans_hom, Iso.app, Category.assoc]
    rw [a.hom.naturality_assoc, b.hom.naturality_assoc, c.hom.naturality])

/-- The objectwise composite is the usual composite of natural isomorphisms. -/
theorem coefficientIsoTransThree_eq
    {C D : Type*} [Category C] [Category D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) :
    coefficientIsoTransThree a b c = a ≪≫ b ≪≫ c := by
  ext N
  rfl

/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[no_expose, irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
    (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
    (coefficientDerivedUpperStarComp Λ g' f)

/-- Equation for the objectwise construction of the cached ambient square. -/
theorem coefficientAmbientSquare_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientAmbientSquare Λ sq =
      coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
        (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
        (coefficientDerivedUpperStarComp Λ g' f) := by
  unfold coefficientAmbientSquare
  rfl

/-- Square coherence for functor comparisons between two families of categories. -/
def FunctorComparisonSquare
    {K : Type*} [Category K] {C D : K → Type*}
    [∀ X, Category (C X)] [∀ X, Category (D X)]
    (E : ∀ {X Y : K}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ {X Y : K}, (X ⟶ Y) → D Y ⥤ D X)
    (F : ∀ X, C X ⥤ D X)
    (p : ∀ {X Y : K} (f : X ⟶ Y), E f ⋙ F X ≅ F Y ⋙ I f)
    (θ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X}, CommSq g' f' f g → (E g ⋙ E f' ≅ E f ⋙ E g'))
    (φ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X}, CommSq g' f' f g → (I g ⋙ I f' ≅ I f ⋙ I g')) : Prop :=
  ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (N : C Y),
    (F X').map ((θ sq).hom.app N) ≫ (p g').hom.app ((E f).obj N) ≫
      (I g').map ((p f).hom.app N) =
    (p f').hom.app ((E g).obj N) ≫ (I f').map ((p g).hom.app N) ≫
      (φ sq).hom.app ((F Y).obj N)

/-- The family of inverse-image comparisons, with generic coefficient interfaces cached. -/
def CoefficientPullbackFamily (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) : Type _ :=
  ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F S ≅
      F T ⋙
        coefficientDerivedUpperStar Λ h

/-- Square coherence for a specified family of inverse-image comparisons. -/
def CoefficientPullbackSquare (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)))
    (pullback : CoefficientPullbackFamily B Λ F) : Prop :=
  @FunctorComparisonSquare Scheme.{u} _
    (fun T ↦ FiniteDiscreteEtalePlus B T)
    (fun T ↦ DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun {_ _} h ↦
      D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h))
    (fun {_ _} h ↦ coefficientDerivedUpperStar Λ h) F pullback
    (fun {_ _ _ _} {_ _ _ _} sq ↦
      Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq)
    (fun {_ _ _ _} {_ _ _ _} sq ↦ coefficientAmbientSquare Λ sq)

/-- Inverse-image data and square coherence, without a condition on right mates. -/
structure CoefficientCoherentPullbackData (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : CoefficientPullbackFamily B Λ F
  square : CoefficientPullbackSquare B Λ F pullback

/-- Coherent inverse-image data for a finite-discrete realization family. -/
abbrev FiniteDiscreteCoherentPullbacks (B : Type) [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B]
    (E : ∀ T : Scheme.{u},
      FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T) :=
  CoefficientCoherentPullbackData B (Profinite.continuousMapRingObj B)
    (fun T ↦ finiteDiscreteRealization B T (E T))

end AlgebraicGeometry.ProEtale.CondensedRing
