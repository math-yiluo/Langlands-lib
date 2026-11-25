/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Linearity of completed restriction from a coefficient sequence

Source: the constant-section scalar calculation in the proof of the coherent
compact-support reduction tower, step 8; Stacks Tags 03DA and 0941.
(blueprint: lem-weil-compact-support-sequence-restriction-linearity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem scalarRestrictionHomTransport
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M M' N N' : SheafOfModules.{u + 1} R}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : ∀ V : Cᵒᵖ, HEq (fun x ↦ f.val.app V x) (fun x ↦ g.val.app V x)) :
    f = eqToHom hM ≫ g ≫ eqToHom hN.symm := by
  subst M' N'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext V x
  exact congrFun (eq_of_heq (h V)) x

/-- Completed restriction preserves scalar actions whose section formulas agree.

Source: coherent compact-support reduction tower, step 8; Stacks 03DA, 0941.
(blueprint: lem-weil-compact-support-sequence-restriction-linearity).

Proof: linearity reduces to preservation of scalar multiples of identity maps.
Evaluate the strict tower at a level. The specified restriction functor preserves
underlying section maps, up to its specified object equalities. The two normalized
scalar formulas and their projection compatibility give equality on every section.
Transport across the object equalities, then use sheaf-module and tower
extensionality. No assertion of faithfulness on derived towers is used. -/
theorem compactSupportSequenceRestriction_linear_of_sections
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (sX : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E W))
    (sS : Linear (Padic.coefficientExtensionIntegers l E)
      (coefficientSequenceModules.{u, u} l E W))
    (hX : @IsCompactSupportScalarAction l _ E _ _ _ W sX)
    (aS : Padic.coefficientExtensionIntegers l E →
      ∀ V : (ℕ × W.ProEt)ᵒᵖ,
        (((coefficientSequenceCommRingSheaf.{u, u} l E W).obj ⋙
          forget₂ CommRingCat RingCat).obj V))
    (hS : letI := sS
      ∀ (M : coefficientSequenceModules.{u, u} l E W)
        (a : Padic.coefficientExtensionIntegers l E) (n : ℕ) (V : W.ProEtᵒᵖ)
        (x : M.val.obj (op (n, V.unop))),
        (a • 𝟙 M).val.app (op (n, V.unop)) x = aS a (op (n, V.unop)) • x)
    (hc : ∀ (a : Padic.coefficientExtensionIntegers l E) (n : ℕ) (V : W.ProEtᵒᵖ),
      aS a (op (n, V.unop)) =
        ((eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm).hom.app V)
          (((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V)
            (compactSupportConstantScalar l E W V a))) :
    letI := sX
    letI := sS
    (coefficientSequenceRestriction.{u, u} l E W).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  let := sX
  let := sS
  unfold IsCompactSupportScalarAction at hX
  rw [Functor.linear_iff]
  intro M a
  apply NatTrans.ext
  funext n
  rcases n with ⟨n⟩
  let h := (coefficientSequenceRestriction_exists.{u, u} l E W).exists.choose_spec
  let e := h.1 M n
  have hm := scalarRestrictionHomTransport e e
    (((coefficientSequenceRestriction.{u, u} l E W).map (a • 𝟙 M)).app (op n))
    (a • 𝟙 ((scalarReductionRestriction l E W n).obj
      ((coefficientSequenceEvaluation l E W n).obj M))) (fun V ↦ by
        have he := h.2.2 (a • 𝟙 M) n V
        apply he.trans
        simp only [hS, hX]
        apply heq_of_eq
        funext x
        change aS a (op (n, V.unop)) • x =
          ((eqToHom (coefficientSequenceEvaluationRing_eq.{u, u} l E W n).symm).hom.app V)
            (((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V)
              (compactSupportConstantScalar l E W V a)) • x
        rw [hc])
  dsimp only [coefficientSequenceRestriction] at hm ⊢
  simpa only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Category.comp_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl, Functor.map_id, NatTrans.id_app,
    NatTrans.app_smul] using hm

end WeilConjectures
