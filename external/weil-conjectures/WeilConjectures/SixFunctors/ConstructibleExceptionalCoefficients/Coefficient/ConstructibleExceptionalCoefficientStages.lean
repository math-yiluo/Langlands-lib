/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingStageAssembly
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ExceptionalFieldStageCompletion

/-! # A geometric step in normalized exceptional coefficient assembly

The output fields retain literal rationalized integral objects and maps. The common-stage
record includes its action on every transition followed by a stage arrow, as constructed
by the pair-category representative formula. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The representative action at an identity arrow gives the transition square. -/
private theorem representativeAction_transition
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Fj : B ⥤ D) (FΩ : E ⥤ H)
    (TX : A ⥤ B) (TY : C ⥤ D) (IXi : A ⥤ E) (IXj : B ⥤ E)
    (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY ≅ TX ⋙ Fj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi)
    (ha : representativeAction Fi Fj FΩ TX TY IXi IXj IYi IYj q qi qj tauX tauY)
    (K : A) :
    qi.hom.app K ≫ FΩ.map (tauX.inv.app K) =
      tauY.inv.app (Fi.obj K) ≫ IYj.map (q.hom.app K) ≫ qj.hom.app (TX.obj K) := by
  have hr := ha K (TX.obj K) (𝟙 _)
  dsimp only [CategoryTheory.Functor.comp_obj] at hr ⊢
  erw [IXj.map_id, CategoryTheory.Category.comp_id, Fj.map_id, IYj.map_id,
    CategoryTheory.Category.id_comp] at hr
  rw [hr]
  erw [← CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id_app,
    CategoryTheory.Category.id_comp]

/-- Construct the coefficient stages before choosing any refinement maps.
Source: Zheng, Lemma 5.22, Proposition 5.24 and the exceptional coefficient construction,
steps 1--5 (blueprint: lem-sf-constructible-exceptional-coefficient-stages).

Proof: restrict the finite etale compact-support adjunction to bounded constructible
finite-Tor objects and transport by the canonical site comparison. Use the adjoint
right shift and the coefficient-independent dimension bounds. Literal derived scalar
restrictions give finite scalars, and the proper/open projection mate and its counit
transpose give the invertible q and b. Use the actual strict-system adjunction and
normalized reduction/limit equivalence to construct the integral operations. Identify
its left functor with the prescribed integral compact support using the canonical
ambient realization. Completed scalar extension and cofinal ramified reduction give
integral scalars and all allowed composites. The tensor unitor and associator give
scalar identity and composition maps independently of compactification. Transport
linear Hom bijections through this prescribed left identification, localize the
integral adjunctions and scalar maps, then descend over common finite fields. Take
rational and closed left objects to be their literal represented compact-support
objects; the rationalization q is identity there. Define the closed left functor on
pair-category arrows through the common-stage transitions and the rational scalar q, so
it sends each transition isomorphism to that q (commonTransitionNatural). Choose the
localization and inclusion shifts from the coefficient functors themselves, so they are independent
of compactification. All ring left realizations commute with these inherited shifts.
Empty schemes give zero functors; repeated levels give tensor unitors. No refinement
map, refinement unit equation or refinement counit equation is constructed here. -/
theorem exists_coefficient_stages (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f),
      ∃ F : CoefficientConstructionFields.{u, v} l Ω D hl R,
        ∃ M : CoefficientConstructionCommon.{u, v} l Ω D hl R F,
          CoefficientConstructionNormalization.{u, v} l Ω D hl R F M := by
  obtain ⟨A⟩ := exists_ring_stage_assembly.{u, v} l Ω D hl f
  obtain ⟨rational, closed, rationalLeft, F, M, hx, hy, hi, hcx, hcy⟩ :=
    exists_field_stage_completion.{u, v} l Ω D hl f A
  let R := A.complete l Ω D hl rational closed rationalLeft
  refine ⟨R, F, M, ?_⟩
  refine {
    leftShift := ?_
    localizationShiftX := hx
    localizationShiftY := hy
    localizationIdentity := hi
    commonShiftX := hcx
    commonShiftY := hcy
    commonTransitionNatural := ?_ }
  · intro c s
    cases s with
    | finite E n => exact A.leftShift c (.finite E n)
    | integral E => exact A.leftShift c (.integral E)
  · intro c i j h K
    exact representativeAction_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (M.common_morphism_normalized c i j h) K

end WeilConjectures.ConstructibleExceptionalCoefficients
