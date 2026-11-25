/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleStratifiedCounit

import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleStratifiedEssentialImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-!

# Constructible sheaves on the small pro-étale site

This file defines the intrinsic notion of constructibility of sheaves of `Λ`-modules on the
small pro-étale site of a scheme `X` (blueprint `definition-constructible-sheaves`): a
sheaf is constructible if, on the strata of a stratification of `X`, it is locally constant with
finitely generated stalks. Locally constant with finitely generated stalks means that the
pullbacks along the members of a pro-étale covering family are constant sheaves of finitely
generated `Λ`-modules.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant`: locally constant with finitely
  generated stalks.
- `AlgebraicGeometry.ProEtale.IsConstructible`: constructible.

## Main statements

- `AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj`: the comparison
  pullback `ν^*` of a finite locally constant étale sheaf is locally constant with finitely
  generated stalks.
- `AlgebraicGeometry.ProEtale.isConstructible_comparisonUpperStar_obj`: `ν^*` preserves
  constructibility.
- `ProEtale.isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`
  (`theorem-comparison-constructible-sheaves` (i)): a pro-étale sheaf is constructible if and only
  if it is `ν^*` of a constructible étale sheaf.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `definition-constructible-sheaves`: a sheaf `F` of `Λ`-modules on the
small pro-étale site of `X` is *locally constant with finitely generated stalks* if there is a
pro-étale covering family `g i : W i ⟶ X` such that every pullback `(g i)^* F` is the constant
sheaf of a finitely generated `Λ`-module (Stacks 09AJ). -/
def IsFiniteLocallyConstant {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
    Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
      ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M ∧
        Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
          (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)

/-- Blueprint `definition-constructible-sheaves`: a sheaf `F` of `Λ`-modules on the
small pro-étale site of `X` is *constructible* if there is a finite partition of `X` into
locally closed constructible subschemes on each of which the restriction of `F` is locally
constant with finitely generated stalks. -/
def IsConstructible {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstant Λ (((S.immersion i))^*[ModuleCat.{u + 1} Λ].obj F)

section Comparison

variable {Λ}

/-- Being locally constant with finitely generated stalks is invariant under isomorphism. -/
theorem isFiniteLocallyConstant_of_iso {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsFiniteLocallyConstant Λ F) : IsFiniteLocallyConstant Λ G := by
  obtain ⟨ι, W, g, hg, h⟩ := hF
  refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e'⟩⟩ := h i
  exact ⟨M, hM, ⟨((g i)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫ e'⟩⟩

/-- Being constructible is invariant under isomorphism. -/
theorem isConstructible_of_iso {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsConstructible Λ F) : IsConstructible Λ G :=
  have ⟨S, hS⟩ := hF
  ⟨S, fun i ↦ isFiniteLocallyConstant_of_iso
    (((S.immersion i))^*[ModuleCat.{u + 1} Λ].mapIso e) (hS i)⟩

variable (Λ) in
/-- The comparison pullback `ν^*` sends constant étale sheaves to constant pro-étale sheaves:
`constantSheaf ⋙ ν^*` and `constantSheaf` are both left adjoint to the global sections, as the
inclusion of sites sends the terminal object `X` of `X_ét` to the terminal object `X` of
`X_proét`. -/
noncomputable def comparisonUpperStarConstantSheafIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ ν^*(X)[ModuleCat.{u + 1} Λ] ≅
      constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (Etale.isTerminalMkId X)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)).ofNatIsoRight
    ((toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso (ModuleCat.{u + 1} Λ)
      X.smallEtaleTopology (Scheme.ProEt.topology X)
        (op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) (ProEt.isTerminalMkId X))

/-- The comparison pullback `ν^*` of a finite locally constant étale sheaf is locally constant
with finitely generated stalks. An étale cover trivialising `G` is a pro-étale cover, `ν^*`
commutes with the pullbacks along its members and sends constant sheaves to constant sheaves; the
values of the constant sheaves are finitely generated on the nonempty members, as `G` has finitely
generated stalks. -/
theorem isFiniteLocallyConstant_comparisonUpperStar_obj {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstant Λ ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) := by
  obtain ⟨⟨𝒰₀, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  let 𝒰 := 𝒰₀.nonemptyMembers
  refine ⟨ULift.{u + 1} 𝒰.I₀, fun i ↦ 𝒰.X i.down, fun i ↦ 𝒰.f i.down, ?_, ?_⟩
  · have h : Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down)
        (fun i ↦ 𝒰.f i.down) = 𝒰.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
      exact Presieve.ofArrows.mk (ι := ULift.{u + 1} 𝒰.I₀) (Y := fun i ↦ 𝒰.X i.down) ⟨i⟩
    rw [h]
    exact etalePrecoverage_le_proetalePrecoverage _ 𝒰.mem₀
  · rintro ⟨⟨i, hi⟩⟩
    have hc : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰₀.f i)).obj G).IsConstant
        (𝒰₀.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar _ (𝒰₀.etalePrecoverageToEtale i) G).mp (h𝒰 i)
    obtain ⟨M, ⟨e⟩⟩ :=
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰₀.f i)).obj G).mem_essImage_of_isConstant
    have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        ((constantSheaf (𝒰₀.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (𝒰₀.f i) G
      IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) e.symm
    have : Nonempty (𝒰₀.X i) := hi
    have : Module.Finite Λ M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := 𝒰₀.X i) M
    exact ⟨M, this,
      ⟨(comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (𝒰₀.f i)).app G ≪≫
        (ν^*(𝒰₀.X i)[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫
        (comparisonUpperStarConstantSheafIso Λ (𝒰₀.X i)).app M⟩⟩

/-- The comparison pullback `ν^*` of a constructible étale sheaf is constructible: on the strata
of a stratification for `G`, it is `ν^*` of a finite locally constant sheaf, `ν^*` commuting with
the pullbacks to the strata. -/
theorem isConstructible_comparisonUpperStar_obj {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructible Λ ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S, fun i ↦ ?_⟩
  have := hS i
  exact isFiniteLocallyConstant_of_iso
    ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (S.immersion i)).app G).symm
    (isFiniteLocallyConstant_comparisonUpperStar_obj _)

/-- At a finite coefficient ring, the values of a locally constant sheaf with finitely generated
stalks are finite. -/
theorem IsFiniteLocallyConstant.exists_finite [Finite Λ] {X : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstant Λ F) :
    ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
            (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨ι, W, g, hg, h⟩ := hF
  refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨M, _, e⟩ := h i
  exact ⟨M, Module.finite_of_finite Λ, e⟩

variable (Λ) in
/-- Compatibility required from `chap-The-pro-etale-site` (to be proved there):
blueprint `theorem-comparison-constructible-sheaves`.
Blueprint `theorem-comparison-constructible-sheaves`: Constructible pro-étale coefficients are
of étale origin, clause (i).

At a finite coefficient ring `Λ`, the comparison pullback `ν^*` induces an equivalence between
the constructible sheaves of `Λ`-modules on the small étale site of `T` and the constructible
sheaves on its small pro-étale site. As `ν^*` is fully faithful
(`AlgebraicGeometry.ProEtale.full_comparisonUpperStar`,
`AlgebraicGeometry.ProEtale.faithful_comparisonUpperStar`), this says that a pro-étale sheaf is
constructible if and only if it is `ν^*` of a constructible étale sheaf. That `ν^*` preserves
constructibility is `isConstructible_comparisonUpperStar_obj`; the essential surjectivity is the
content of the lemma (Stacks, Tag 09AK, which holds for Noetherian `Λ`; the proof here uses
that `Λ` is finite). -/
theorem isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj [Finite Λ]
    {T : Scheme.{u}} {F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)} :
    IsConstructible Λ F ↔
      ∃ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), Scheme.IsConstructibleSheaf G ∧
        Nonempty ((ν^*(T)[ModuleCat.{u + 1} Λ]).obj G ≅ F) := by
  constructor
  · rintro ⟨S, hS⟩
    let G := (ν_*(T)[ModuleCat.{u + 1} Λ]).obj F
    have := isIso_comparison_counit_of_finite_stratification Λ S F fun i ↦ (hS i).exists_finite
    let e : (ν^*(T)[ModuleCat.{u + 1} Λ]).obj G ≅ F :=
      asIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).counit.app F)
    refine ⟨G, ⟨S, fun i ↦ ?_⟩, ⟨e⟩⟩
    apply isFiniteLocallyConstantSheaf_of_comparison_finite_models Λ
    apply IsFiniteLocallyConstant.exists_finite
    apply isFiniteLocallyConstant_of_iso
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ)
        (S.immersion i)).app G)
    exact isFiniteLocallyConstant_of_iso
      (((S.immersion i)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm) (hS i)
  · rintro ⟨G, hG, ⟨e⟩⟩
    exact isConstructible_of_iso e (isConstructible_comparisonUpperStar_obj G)

variable (Λ) in
/-- A constructible pro-étale sheaf is `ν^*` of a constructible étale sheaf
(`theorem-comparison-constructible-sheaves` (i)). -/
theorem exists_isConstructibleSheaf_iso_comparisonUpperStar_obj [Finite Λ] {T : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)} (hF : IsConstructible Λ F) :
    ∃ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), Scheme.IsConstructibleSheaf G ∧
      Nonempty ((ν^*(T)[ModuleCat.{u + 1} Λ]).obj G ≅ F) :=
  (isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ).1 hF

end Comparison

end AlgebraicGeometry.ProEtale
