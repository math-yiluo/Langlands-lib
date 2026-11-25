/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTransitions
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionRestrictionCoherence
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Identity and composition for actual integral reduction transitions

Source: blueprint coefficient datum, normalized quotient maps; Stacks 06YY.
(blueprint: lem-pur-integral-reduction-transition-cocycles).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
attribute [local instance] normalizedDVREffectivityLocal1 normalizedDVREffectivityLocal2
  normalizedDVREffectivityLocal3

universe v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

private theorem transition_unit
    {C : Type v₁} [Category.{w₁} C] {A : Type v₂} [Category.{w₂} A]
    {L : C ⥤ A} {R : A ⥤ C} (adj : L ⊣ R) (S : A ⥤ A)
    (e : S ⋙ R ≅ R) (u : S ≅ 𝟭 A) (M : C)
    (h : e.inv.app (L.obj M) ≫ R.map (u.hom.app (L.obj M)) = 𝟙 _) :
    (adj.homEquiv M _).symm (adj.unit.app M ≫ e.inv.app (L.obj M)) ≫
      u.hom.app (L.obj M) = 𝟙 _ := by
  apply (adj.homEquiv M _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Category.assoc, h]
  rw [Adjunction.homEquiv_unit]
  exact congrArg (fun k ↦ adj.unit.app M ≫ k) (R.map_id (L.obj M)).symm

private theorem transition_comp
    {C : Type v₁} [Category.{w₁} C] {A : Type v₂} [Category.{w₂} A]
    {B : Type v₃} [Category.{w₃} B] {T : Type v₄} [Category.{w₄} T]
    {Lc : C ⥤ A} {Rc : A ⥤ C} {Lb : C ⥤ B} {Rb : B ⥤ C}
    {La : C ⥤ T} {Ra : T ⥤ C}
    (ac : Lc ⊣ Rc) (ab : Lb ⊣ Rb) (aa : La ⊣ Ra)
    (S : B ⥤ A) (V : T ⥤ B) (Q : T ⥤ A)
    (ecb : S ⋙ Rc ≅ Rb) (eba : V ⋙ Rb ≅ Ra) (eca : Q ⋙ Rc ≅ Ra)
    (c : V ⋙ S ≅ Q) (M : C)
    (h : eba.inv.app (La.obj M) ≫ ecb.inv.app (V.obj (La.obj M)) ≫
      Rc.map (c.hom.app (La.obj M)) = eca.inv.app (La.obj M)) :
    (ac.homEquiv M _).symm (ab.unit.app M ≫ ecb.inv.app (Lb.obj M)) ≫
      S.map ((ab.homEquiv M _).symm (aa.unit.app M ≫ eba.inv.app (La.obj M))) ≫
      c.hom.app (La.obj M) =
    (ac.homEquiv M _).symm (aa.unit.app M ≫ eca.inv.app (La.obj M)) := by
  let t := (ab.homEquiv M _).symm (aa.unit.app M ≫ eba.inv.app (La.obj M))
  apply (ac.homEquiv M _).injective
  rw [ac.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Functor.map_comp]
  change (ab.unit.app M ≫ ecb.inv.app (Lb.obj M)) ≫
    Rc.map (S.map t) ≫ Rc.map (c.hom.app (La.obj M)) = _
  have he := ecb.inv.naturality t
  change Rb.map t ≫ ecb.inv.app _ = ecb.inv.app _ ≫ Rc.map (S.map t) at he
  have ht : ab.unit.app M ≫ Rb.map t =
      aa.unit.app M ≫ eba.inv.app (La.obj M) :=
    (ab.homEquiv M _).apply_symm_apply _
  calc
    _ = (ab.unit.app M ≫ Rb.map t) ≫ ecb.inv.app (V.obj (La.obj M)) ≫
        Rc.map (c.hom.app (La.obj M)) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ ab.unit.app M ≫ k ≫ Rc.map (c.hom.app (La.obj M))) he.symm
    _ = _ := by
      rw [ht]
      simpa only [Category.assoc] using congrArg (fun k ↦ aa.unit.app M ≫ k) h

/-- The units of the normalized reduction adjunctions induce a coherent semilinear tower.
Source: blueprint coefficient datum and source-object argument, Step 7; Stacks 06YY
(blueprint: lem-pur-integral-reduction-transition-cocycles).

Proof: apply the Hom bijection of the scalar-extension/restriction adjunction at the
largest index. By definition the transpose of the transition to n is the reduction
unit at n followed by the inverse restriction compositor. At equal indices the
restriction unit identifies this with the unit at that same index, whose inverse
transpose is the identity. For three indices, naturality of the intermediate unit
and the adjunction triangle identities turn the transpose of the two transitions
into the smallest-index unit followed by the two inverse compositors. The canonical
restriction compositors satisfy their associativity equation: at the module level
all are the identity on sections, with the scalar action identified by composition
of the actual quotient maps; exact derived localization preserves the equation.
Thus this is the transpose of the direct transition. Injectivity of the Hom bijection
gives the composition equation. The argument uses no boundedness, constructibility,
completeness or normalization assumption on the object. -/
theorem integralReductionTransition_cocycles
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (M : completedIntegralDerivedCategory l E W D hl) :
    (∀ n : ℕ, normalizedDVRReductionTransition.{u, u, u} l E W D hl (Nat.le_refl n) M ≫
      (normalizedDVRResUnit.{u, u} l E W n).hom.app _ = 𝟙 _) ∧
    (∀ {c b a : ℕ} (hab : a ≤ b) (hbc : b ≤ c),
      normalizedDVRReductionTransition.{u, u, u} l E W D hl hbc M ≫
        (normalizedDVRRes.{u, u} l E W hbc).map
          (normalizedDVRReductionTransition.{u, u, u} l E W D hl hab M) ≫
        (normalizedDVRResComp.{u, u} l E W hbc hab).hom.app _ =
      normalizedDVRReductionTransition.{u, u, u} l E W D hl (hab.trans hbc) M) := by
  have hc := integralReductionRestriction_coherence D l hl E W
  constructor
  · intro n
    exact transition_unit (normalizedDVRIntegralAdjunction l E W n)
      (normalizedDVRRes l E W (Nat.le_refl n))
      (normalizedDVRResCompletedComp l E W D hl (Nat.le_refl n))
      (normalizedDVRResUnit l E W n) M (hc.1 n _)
  · intro c b a hab hbc
    exact transition_comp (normalizedDVRIntegralAdjunction l E W c)
      (normalizedDVRIntegralAdjunction l E W b) (normalizedDVRIntegralAdjunction l E W a)
      (normalizedDVRRes l E W hbc) (normalizedDVRRes l E W hab)
      (normalizedDVRRes l E W (hab.trans hbc))
      (normalizedDVRResCompletedComp l E W D hl hbc)
      (normalizedDVRResCompletedComp l E W D hl hab)
      (normalizedDVRResCompletedComp l E W D hl (hab.trans hbc))
      (normalizedDVRResComp l E W hbc hab) M (hc.2 hab hbc _)

end WeilConjectures
