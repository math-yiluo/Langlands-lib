/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
import all WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison

/-!
# Coefficient-isomorphism invariance of condensed base change

The normalized scalar-pullback comparison and its right mate identify geometric
exchange after an isomorphism of coefficient rings. This is the coefficient
transport step in proper base change on the admissible generators.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] finiteProperCache2 finiteProperCache3 finiteProperCache4

local instance essentiallySmallProfinite : EssentiallySmall.{u + 1} Profinite.{u} :=
  essentiallySmallSelf.{0} _

noncomputable local instance condensedAbMonoidalCategory :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.monoidalCategory _ _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  condensedAmbientExchange CategoryTheory.mateEquiv CategoryTheory.Functor.mapDerivedCategory

attribute [local instance] finiteProperCache2 finiteProperCache3 finiteProperCache4
  finiteProperCache5 finiteProperCache6 finiteProperCache7 finiteProperCache8
  finiteProperCache9 finiteProperCache10 finiteProperCache12

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeAdjunction residueExchangeUpperStarComp

open QuotientChange

-- Keep tensor-model caches local to the scalar proof. Later finite-Tor hypotheses
-- use the canonical tensor structure of the published constructible subcategory.
section CachedScalarModels

attribute [local instance] modulesClosed modulesSymmetric modulesFlat

private theorem scalar_extension_equivalence
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (T : Scheme.{u}) :
    (extension φ T).IsEquivalence := by
  have : IsIso (coefficientMap φ T) := by dsimp [coefficientMap]; infer_instance
  have : (Mod.comap (asIso (coefficientMap φ T)).inv).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso (coefficientMap φ T)).inverse.IsEquivalence)
  exact Functor.isEquivalence_of_iso
    (Mod.extendScalarsIsoComapInv (coefficientMap φ T)).symm

private theorem scalar_derived_equivalence
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (T : Scheme.{u}) :
    (D φ T).IsEquivalence := by
  have := scalar_extension_equivalence φ T
  unfold D
  infer_instance

private theorem scalar_coefficientIso_ctf
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) (Z : Scheme.{u})
    (K : ConstantModelConstructibleFiniteTor R Z) :
    (constantModelBoundedConstructible S Z ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      ((D e.hom.hom Z).obj K.obj) := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have : (extension e.hom.hom Z).IsEquivalence := scalar_extension_equivalence _ _
  have : IsIso (coefficientMap e.hom.hom Z) := by
    dsimp [coefficientMap]; infer_instance
  have hi : inv (coefficientMap e.hom.hom Z) = coefficientMap e.inv.hom Z := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← coefficientMap_comp]
    change coefficientMap ((Mon.forget _).map (e.hom ≫ e.inv)) Z = _
    rw [Iso.hom_inv_id]
    change coefficientMap (𝟙 R) Z = 𝟙 _
    exact coefficientMap_id Z
  have ed : D e.hom.hom Z ≅
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (coefficientMap e.inv.hom Z)).mapDerivedCategory := by
    unfold D
    exact (extension e.hom.hom Z).leftDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso
        (Mod.extendScalarsIsoComapInv (coefficientMap e.hom.hom Z) ≪≫ Mod.comapCongr hi)
  have : (constantModelBoundedConstructible S Z).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined S Z).2.1
  exact ObjectProperty.prop_of_iso _ (ed.app K.obj).symm
    (constantModelCtf_coefficientIso e Z K)

private noncomputable def scalar_coefficientIso_object
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) (Z : Scheme.{u})
    (K : ConstantModelConstructibleFiniteTor R Z) : ConstantModelConstructibleFiniteTor S Z := by
  refine ⟨(D e.hom.hom Z).obj K.obj, ?_⟩
  have ht := scalar_coefficientIso_ctf e Z K
  refine Eq.mp ?_ ht
  run_tac coefficientCongrGoal

private theorem scalar_coefficientIso_object_obj
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) (Z : Scheme.{u})
    (K : ConstantModelConstructibleFiniteTor R Z) :
    (scalar_coefficientIso_object e Z K).obj = (D e.hom.hom Z).obj K.obj := rfl

private theorem scalar_coefficientIso_component
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S)
    {A Z Y Y' : Scheme.{u}} {a : A ⟶ Z} {q' : A ⟶ Y'}
    {q : Z ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare a q' q v)
    (h : ∀ C : ConstantModelConstructibleFiniteTor S Z,
      IsIso ((condensedAmbientExchange S sq).app C.obj))
    (K : ConstantModelConstructibleFiniteTor R Z) :
    IsIso ((condensedAmbientExchange S sq).app ((D e.hom.hom Z).obj K.obj)) := by
  rw [← scalar_coefficientIso_object_obj e Z K]
  exact h (scalar_coefficientIso_object e Z K)

private noncomputable def chosenScalarPull
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] {U V : Scheme.{u}} (f : U ⟶ V) :
    D φ V ⋙ L S f ≅ L R f ⋙ D φ U := by
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R T) := sectionDerived R
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules S T) := sectionDerived S
  exact (internal_pull_normalization_exists φ f).choose

private theorem chosenScalarPull_normalized
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] {U V : Scheme.{u}} (f : U ⟶ V) :
    PullNormalized φ f (chosenScalarPull φ f) := by
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R T) := sectionDerived R
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules S T) := sectionDerived S
  exact (internal_pull_normalization_exists φ f).choose_spec

private theorem chosenScalarPull_mate_iso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] {U V : Scheme.{u}} (f : U ⟶ V) :
    IsIso (rho φ f (chosenScalarPull φ f)) := by
  have hD (T : Scheme.{u}) : (D φ T).IsEquivalence := scalar_derived_equivalence φ T
  unfold rho
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adj R f) (adj S f) (D φ V) (D φ U) (chosenScalarPull φ f)

/-- Exchange is an isomorphism on constant-model constructible finite-Tor objects
if it is so after an isomorphism of coefficients.

Source: the coefficient-transport step in the proper base-change argument in
blueprint `proposition-composition-base-change-rf-shriek--1`, proof (2). Scalar extension along the
coefficient isomorphism is an equivalence and agrees with exact restriction along
its inverse. It therefore preserves the constant-model constructible finite-Tor
subcategory. Choose the normalized pullback comparisons; their right mates are
isomorphisms because both scalar functors are equivalences. The scalar/geometric
exchange rectangle identifies the image of the exchange map with a composite of
these comparisons and the exchange map over the second coefficient ring. This
composite is an isomorphism by the hypothesis. Finally the scalar equivalence
reflects isomorphisms.
(blueprint: lem-sfb-condensed-coefficient-iso-exchange) -/
theorem condensedAmbientExchange_coefficientIso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S)
    {A Z Y Y' : Scheme.{u}} {a : A ⟶ Z} {q' : A ⟶ Y'}
    {q : Z ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare a q' q v)
    (h : ∀ C : ConstantModelConstructibleFiniteTor S Z,
      IsIso ((condensedAmbientExchange S sq).app C.obj))
    (K : ConstantModelConstructibleFiniteTor R Z) :
    IsIso ((condensedAmbientExchange R sq).app K.obj) := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have hD (T : Scheme.{u}) : (D e.hom.hom T).IsEquivalence :=
    scalar_derived_equivalence e.hom.hom T
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R T) := sectionDerived R
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules S T) := sectionDerived S
  have hraw :=
    generic_condensed_exchange_iso R S e.hom.hom (chosenScalarPull e.hom.hom) sq K.obj
      (IntegralQuotient.internal_rectangle e.hom.hom (chosenScalarPull e.hom.hom)
        (chosenScalarPull_normalized e.hom.hom) sq)
      (chosenScalarPull_mate_iso _ q) (chosenScalarPull_mate_iso _ q')
      (by
        have ht := scalar_coefficientIso_component e sq h K
        refine Eq.mp ?_ ht
        run_tac coefficientCongrGoal)
  have hmap : IsIso ((D e.hom.hom Y').map ((condensedAmbientExchange R sq).app K.obj)) := by
    refine Eq.mp ?_ hraw
    run_tac coefficientCongrGoal
  exact isIso_of_reflects_iso ((condensedAmbientExchange R sq).app K.obj) (D e.hom.hom Y')

end CachedScalarModels

end AlgebraicGeometry.ProEtale.CondensedRing
