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

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.UnboundedBaseChangeExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import WeilConjectures.Compactification.CommonDenseRefinement

/-!
# Base change for `Rf_!` on the localizing category

Source: the blueprint of the Weil conjectures, chapter `chap-Construction-of-f`, unit
`proposition-composition-base-change-rf-shriek--1` (blueprint:
proposition-composition-base-change-rf-shriek--4); Stacks Project, Tag 09AH.

The statement uses the published module-object definitions of derived pullback and derived
lower shriek, the literal compactification base-change construction, and the localizing closure
of bounded constructible finite-Tor objects. The coefficient parameter is a commutative
condensed ring satisfying the published `IsLocalizingAdmissibleCoefficient ℓ Λ` predicate.
-/

@[expose] public section
set_option linter.privateModule false

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

attribute [local irreducible] derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStarLowerStarAdjunction condensedAmbientPullbackComparison
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory condensedAmbientExchange
  upperStar lowerStar openImmersionLowerShriek
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private theorem comparison_cancel
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₁ A₂ A₀ : C} {B₁ B₂ B₀ : D}
    (φ : A₁ ⟶ A₂) (ρ₁ : A₁ ⟶ A₀) (ρ₂ : A₂ ⟶ A₀)
    (ψ : B₁ ⟶ B₂) (σ₁ : B₁ ⟶ B₀) (σ₂ : B₂ ⟶ B₀)
    (β₁ : F.obj A₁ ⟶ B₁) (β₂ : F.obj A₂ ⟶ B₂) (δ : F.obj A₀ ⟶ B₀)
    [Mono σ₂] (hφ : φ ≫ ρ₂ = ρ₁) (hψ : ψ ≫ σ₂ = σ₁)
    (h₁ : F.map ρ₁ ≫ δ = β₁ ≫ σ₁) (h₂ : F.map ρ₂ ≫ δ = β₂ ≫ σ₂) :
    F.map φ ≫ β₂ = β₁ ≫ ψ := by
  apply (cancel_mono σ₂).1
  rw [Category.assoc, ← h₂, ← Category.assoc, ← F.map_comp, hφ, h₁,
    Category.assoc, hψ]

private theorem openExchange_isIso
    {C A B E : Type*} [Category C] [Category A] [Category B] [Category E]
    (F : C ⥤ A) (G : A ⥤ C) (R : A ⥤ E) (P : C ⥤ B)
    (J : B ⥤ E) (H : E ⥤ B) (a : F ⊣ G) (b : J ⊣ H)
    (θ : G ⋙ P ≅ R ⋙ H) [IsIso a.unit]
    (hc : ∀ K, IsIso (b.counit.app (R.obj (F.obj K)))) :
    IsIso ((Functor.leftUnitor (P ⋙ J)).inv ≫
      Functor.whiskerRight a.unit (P ⋙ J) ≫
      (Functor.squareTransport F J θ).hom ≫
      Functor.whiskerLeft (F ⋙ R) b.counit ≫ (Functor.rightUnitor (F ⋙ R)).hom) := by
  have : IsIso (Functor.whiskerLeft (F ⋙ R) b.counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hc
  infer_instance

set_option backward.isDefEq.respectTransparency false in
local instance baseChangeOpen {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) : IsOpenImmersion (c.baseChange v).i :=
  (c.baseChange v).isOpenImmersion

attribute [local irreducible] Compactification.inf Compactification.infFst
  Compactification.infSnd

private theorem ambientExchange_of_preservation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {g' : A ⟶ B} {p' : A ⟶ C} {p : B ⟶ D} {g : C ⟶ D}
    (sq : ChosenCartesianSquare g' p' p g)
    (hp : ProperLocalizingHypotheses Λ p) (hp' : ProperLocalizingHypotheses Λ p')
    (hg : UnboundedLocalizingPullback Λ g) (hg' : UnboundedLocalizingPullback Λ g')
    (hgen : ∀ M, (constantModelBoundedConstructible Λ B M ∧
      _root_.DerivedCategory.finiteTorAmplitude _ M) →
        IsIso ((condensedAmbientExchange Λ sq).app M))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)))
    (hK : localizingClosureProEtale Λ B K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  let := condensedAmbientExchange_isoLocus_triangulated Λ sq
  exact extend_iso _
    (localizingClosure_exists Λ B
      (constantModelBoundedConstructible Λ B ⊓ fun M ↦
        _root_.DerivedCategory.finiteTorAmplitude _ M)).2.2.2.1
    _ _ (condensedAmbientExchange Λ sq) (composite_sums_small Λ hp hp' hg hg') hgen K hK

private theorem properExchange_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (hp' : ProperLocalizingHypotheses Λ q')
    (hv : UnboundedLocalizingPullback Λ v) (ha : UnboundedLocalizingPullback Λ a)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (hK : localizingClosureProEtale Λ Z K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  exact ambientExchange_of_preservation Λ sq
    (properLocalizingHypotheses_admissible ℓ Λ hΛ k q) hp' hv ha
    (fun M hM ↦ properBaseChange_admissible_generators ℓ Λ hΛ k q v sq M hM) K hK

attribute [local irreducible] detSfCompactSupportBaseChangeComposite
  detSfCanonicalCompactificationComparison

end AlgebraicGeometry.ProEtale.CondensedRing
