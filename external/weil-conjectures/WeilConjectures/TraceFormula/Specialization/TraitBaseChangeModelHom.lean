/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Base change of morphisms of models and the projections

For a morphism of models `φ : P ⟶ M` over the trait `S = Spec k'⟦t⟧` and compatible base changes
along `v : Spec K⟦t⟧ ⟶ Y`, the induced morphism of base changes
`φ'' : P'' ⟶ M''` (`NearbyCyclesModel.Hom.baseChange`) is compatible with the projections
`P'' ⟶ P` and `M'' ⟶ M` (`NearbyCyclesModel.baseChangeHom`) on total spaces, geometric generic
fibres and special fibres (`NearbyCyclesModel.Hom.baseChange_total_comp`,
`NearbyCyclesModel.Hom.baseChange_generic_comp`, `NearbyCyclesModel.Hom.baseChangeSpecial_comp`).
These are the hypotheses of the compatibility of the Künneth map of nearby cycles with pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) for the projections from the
geometric slice of a product.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X Z : Scheme.{u}} {X' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {P : NearbyCyclesModel Z Z'.left} {f : Z ⟶ X} {f' : Z'.left ⟶ X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qP : P.total ⟶ trait k'} {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hP : P.IsTraitModelOver qP gP)
  {YM YP : Scheme.{u}} {bM : M.total ⟶ YM} {pM : YM ⟶ trait k'} (hbM : bM ≫ pM = qM)
  {vM : trait K ⟶ YM} (hvM : vM ≫ pM = traitMap k' K)
  {bP : P.total ⟶ YP} {pP : YP ⟶ trait k'} (hbP : bP ≫ pP = qP)
  {vP : trait K ⟶ YP} (hvP : vP ≫ pP = traitMap k' K)
  (φ : P.Hom M f f') (κ : YP ⟶ YM) (hκb : bP ≫ κ = φ.total ≫ bM) (hκv : vP ≫ κ = vM)

/-- The morphism of base changes commutes with the projections on total spaces. -/
lemma Hom.baseChange_total_comp (hgP : gP = φ.generic ≫ gM) :
    (φ.baseChange hM hP hbM hvM hbP hvP κ hκb hκv hgP).total ≫
        (baseChangeHom hM bM hbM vM hvM).total =
      (baseChangeHom hP bP hbP vP hvP).total ≫ φ.total :=
  pullback.lift_fst _ _ _

/-- The morphism of base changes commutes with the projections on geometric generic fibres. -/
lemma Hom.baseChange_generic_comp (hgP : gP = φ.generic ≫ gM) :
    (φ.baseChange hM hP hbM hvM hbP hvP κ hκb hκv hgP).generic ≫
        (baseChangeHom hM bM hbM vM hvM).generic =
      (baseChangeHom hP bP hbP vP hvP).generic ≫ φ.generic := by
  refine hM.isPullback_j.hom_ext ?_ ?_
  · simp [φ.comm_j]
  · simp [← hgP]

/-- The morphism of base changes commutes with the projections on special fibres. -/
lemma Hom.baseChangeSpecial_comp :
    φ.baseChangeSpecial κ hκb hκv ≫ baseChangeSpecialMap hM bM hbM vM hvM =
      baseChangeSpecialMap hP bP hbP vP hvP ≫ f' := by
  have h₁ : (φ.baseChangeSpecial κ hκb hκv ≫ baseChangeSpecialMap hM bM hbM vM hvM) ≫ M.i =
      (baseChangeSpecialMap hP bP hbP vP hvP ≫ f') ≫ M.i := by
    simp [Hom.baseChangeSpecial, φ.comm_i]
  refine hM.isPullback_i.hom_ext h₁ ?_
  have : IsClosedImmersion (traitClosedPoint k') :=
    IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩
  rw [← cancel_mono (traitClosedPoint k')]
  simp only [Category.assoc, ← hM.isPullback_i.w]
  simpa only [Category.assoc] using congrArg (· ≫ qM) h₁

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
