/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import WeilConjectures.AlgebraicGeometry.System.SystemBlockRepetition
/-! # Section normalization for semilinear open localization -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOpenReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The semilinear calculus can use the literal section identification at the given open.
Source: Stacks sites-modules.tex, Tags 03DI--03DJ, and sites-cohomology.tex Tag 0941;
the section-normalized localization in lem-coef-semilinear-derived-sections.
(blueprint: lem-sf-normalized-open-section-existence).

Proof: choose semilinearDerivedSections. Apply blockRepeat_extensionByZero to
SystemBlockMap.id and the systemBlockRepetition package at that map. Its first
open-localization package has restriction evaluation equal to the identity on
sections. Choose this normalized package at every open and replace the localization field
of the chosen sections calculus by that family, keeping every other field. No field of that
calculus requires compatibility between localization and its other operations,
so this is a record update. Its evaluation at the specified open is the
chosen normalized package. The identity block has finite singleton
fibers, including index zero. The argument also covers the empty and identity opens. -/
theorem normalizedOpenSections :
    ∃ sections : SemilinearSections.SemilinearDerivedSectionsData.{t+1, t, max u (t+1)}
        (ProEt.topology X) (rings l E X) (transitions l E X),
      ∀ (n : ℕ) N V x,
        HEq ((((sections.localization (openObject j)).restrictionEvaluation n).hom.app N).val.app
          V x) x := by
  classical
  let : EssentiallySmall.{max u (t + 1)} X.ProEt :=
    essentiallySmallSelf.{u, t, t + 1} X.ProEt
  let J := ProEt.topology X
  let B := rings l E X
  let τ := transitions l E X
  obtain ⟨sections⟩ :=
    SemilinearSections.semilinearDerivedSections.{t + 1, t, max u (t + 1)} J B τ
  obtain ⟨R⟩ :=
    SemilinearSections.systemBlockRepetition.{t + 1, t, max u (t + 1)} J B τ
    SemilinearSections.SystemBlockMap.id
  have existsNormalized (V : X.ProEt) :
      ∃ O : SemilinearSections.OpenSystems.{t + 1, t, max u (t + 1)} J B τ V,
        ∀ (n : ℕ) N W x,
          HEq ((((O.restrictionEvaluation n).hom.app N).val.app W) x) x := by
    obtain ⟨O, _OD, hO, _hOD, _⟩ :=
      SemilinearSections.blockRepeat_extensionByZero.{t + 1, t, max u (t + 1)}
        J SemilinearSections.SystemBlockMap.id B τ V R
    exact ⟨O, hO⟩
  choose O hO using existsNormalized
  exact ⟨{ sections with localization := O }, hO (openObject j)⟩

end WeilConjectures.IntegralOpenReduction
