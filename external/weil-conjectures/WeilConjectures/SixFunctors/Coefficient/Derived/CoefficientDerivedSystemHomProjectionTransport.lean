/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemGammaProjectionTransport

/-! # Degree-zero coefficient gamma projection transport

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08JA, 0D6E and 0941;
the H⁰ specialization of `enrichedSequenceProjectionFormula`
(blueprint: lem-coef-derived-system-hom-projection-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The H⁰ clause of the enriched sequence projection theorem transports to the
actual coefficient gamma map and its finite mapping-limit projections.

Source: Stacks 07A6, 08JA, 0D6E and 0941, together with
`SheafOfModules.EnrichedSequenceProjection.enrichedSequenceProjectionFormula`.
Proof: take degree zero in the transported enriched projection identity; use the
recorded additive H⁰ Hom equivalences and their naturality, then apply
`H.scalar_hom_zero` to identify the finite scalar adjunct. Naturality of
`S.reductionEvaluation` and the counit projection rewrite the result as the
specified composite in `CoefficientHomProjection`.
(blueprint: lem-coef-derived-system-hom-projection-transport)
-/
theorem coefficientDerivedSystemHomProjectionTransport
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientHomProjection l E W S := by
  intro P N hN h n
  have hγ := coefficientDerivedSystemGammaProjectionTransport l E W S D H P N hN n
  have hh := congrArg (fun z =>
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map z) hγ
  simp only [coefficientGammaZeroMap, coefficientGammaZero, Functor.map_comp]
  have hh' := hh
  simp only [Functor.map_comp] at hh'
  rw [hh']
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0
  have hi := (coefficientHomZeroEquiv_exists.{u, t+1, t}
    (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).choose_spec.1.1
  have hf := (coefficientHomZeroEquiv_exists.{u, t+1, t}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).choose_spec.1.1
  let M := (coefficientSequenceDerivedEvaluation l E W n).obj N
  let x := H₀.map
      ((coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op P)) ((coefficientSequenceProjection l E W n).app N)))
      ((coefficientIntegralHomEquiv l E W P
        ((coefficientSequenceLimit l E W).obj N)).symm h)
  let y := H₀.map
      ((coefficientIntegralSections l E W).map
        (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
          (coefficientFiniteDerivedExtension l E W n)
          (coefficientFiniteAdjunction l E W n) (S.finiteTensor n) P M) ≫
        (D.scalarSections n).hom.app
          ((coefficientFiniteInternalHom l E W n).obj
            (op ((coefficientFiniteDerivedExtension l E W n).obj P), M))) x
  have hs := H.scalar_hom_zero n P M x
  change ↑(H₀.obj ((coefficientFiniteGlobalHom l E W n).obj
    (op ((coefficientFiniteDerivedExtension l E W n).obj P), M))) at y
  have hfin := hf _ _ _ _ ((S.reductionEvaluation n).hom.app P)
    (𝟙 M) y
  simp only [H₀, x, y, Functor.map_comp, AddCommGrpCat.comp_apply] at hs hfin ⊢
  change coefficientFiniteHomEquiv l E W n
      ((coefficientSequenceDerivedEvaluation l E W n).obj (S.reduction.obj P)) M _ = _ at hfin
  erw [hfin]
  erw [hs]
  simp only [Category.comp_id]
  have hproj := S.counit_projection N n
  let k := (coefficientFiniteAdjunction l E W n).homEquiv P M
    ((coefficientFiniteDerivedExtension l E W n).map h ≫
      (S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N))
  have hi' : (coefficientIntegralHomEquiv l E W P
      ((coefficientFiniteDerivedRestriction l E W n).obj M)) x = k := by
    have hx := hi P ((coefficientSequenceLimit l E W).obj N) P
      ((coefficientFiniteDerivedRestriction l E W n).obj M)
      (𝟙 P) ((coefficientSequenceProjection l E W n).app N)
      ((coefficientIntegralHomEquiv l E W P
        ((coefficientSequenceLimit l E W).obj N)).symm h)
    have hx' : (coefficientIntegralHomEquiv l E W P
        ((coefficientFiniteDerivedRestriction l E W n).obj M)) x =
        h ≫ (coefficientSequenceProjection l E W n).app N := by
      simpa [x, coefficientIntegralHomEquiv, coefficientHomZeroEquiv, H₀,
        coefficientIntegralGlobalHom, coefficientIntegralSections] using hx
    rw [← hproj] at hx'
    rw [← (coefficientFiniteAdjunction l E W n).homEquiv_naturality_left] at hx'
    exact hx'.trans rfl
  rw [hi']
  dsimp only [k]
  rw [Equiv.symm_apply_apply]

end WeilConjectures
