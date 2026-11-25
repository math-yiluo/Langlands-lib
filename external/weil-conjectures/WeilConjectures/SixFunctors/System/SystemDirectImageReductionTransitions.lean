/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import all WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageRestrictionTransition
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SmoothPurity.Sf.SfNormalizedInputTransition

/-! # Actual transitions of reduction in the normalized finite presentation

Source: Zheng, Construction 4.1, Lemma 4.10 and Proposition 4.21;
Stacks 0941, 0944 and 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] proEtaleCoefficientRestrictScalars_preservesFiniteLimits
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits

private theorem sheaf_hom_transport_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N N' : SheafOfModules.{u + 1} R} (e : N = N') (f : M ⟶ N) (g : M ⟶ N')
    (hf : ∀ V : Cᵒᵖ, HEq (fun x ↦ f.val.app V x) (fun x ↦ g.val.app V x)) :
    f ≫ eqToHom e = g := by
  cases e
  ext V x
  exact congrFun (eq_of_heq (hf V)) x

section OrdinaryComparison

attribute [local irreducible] coefficientSequenceTransition

private theorem ordinary_transition_comparison (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceTransition.{u, u} l E W h ≫ Functor.whiskerLeft
        (coefficientSequenceEvaluation.{u, u} l E W n)
        (eqToIso (compactSupportModuleRes_eq l E W h) :
          normalizedDVRModuleRes l E W h ≅
            proEtaleCoefficientRestrictScalars W
              (compactSupportLevelQuotient l E m n h)).hom =
      compactSupportOrdinaryCoefficientTransition l E W h := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
  apply sheaf_hom_transport_eq
  intro V
  apply HEq.trans (b := (fun x : M.val.obj (Opposite.op (m, V.unop)) ↦
    M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
  · exact heq_of_eq (funext (fun x ↦ coefficientTransition_section l E W M h V x))
  · exact (compactSupportOrdinaryCoefficientTransition_sections l E W h M V).symm

end OrdinaryComparison

private theorem quotient_transition_comparison (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    let := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
      (compactSupportLevelQuotient l E m n h)
    let := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
      (compactSupportLevelQuotient l E m n h)
    let ρ := Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W h))
    coefficientSequenceDerivedTransition l E W h ≫
        Functor.whiskerLeft (coefficientSequenceDerivedEvaluation l E W n) ρ.hom =
      compactSupportCoefficientTransition l E W h := by
  let := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  let := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  dsimp only
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))
  intro P
  apply (cancel_mono
    ((proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
        ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P) ≫
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso
      (eqToIso (compactSupportModuleRes_eq l E W h))).hom.naturality
        ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P)]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  rw [reassoc_of% (transition_rep l E W h P), compactSupportCoefficientTransition_fac]
  rw [← DerivedCategory.Q.map_comp]
  apply congrArg (fun z ↦
    (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map z)
  apply HomologicalComplex.hom_ext
  intro i
  exact NatTrans.congr_app (ordinary_transition_comparison l E W h) (P.X i)

/-- The scalar-adjunction quotient transformation in the normalized finite presentation.
Source: Zheng Construction 4.1 and Proposition 4.21.
(blueprint: lem-weil-system-reduction-quotient-transitions). -/
def systemReductionQuotient (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  coefficientQuotientNatTrans (coefficientFiniteAdjunction l E W m)
    (coefficientFiniteAdjunction l E W n) (normalizedDVRRes l E W h)
    (compactSupportSystemRestrictionComp l E W h)

private theorem quotient_mate_change
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (P Q : B ⥤ A) (ρ : P ≅ Q)
    (c : P ⋙ Rm ≅ Rn) (d : Q ⋙ Rm ≅ Rn)
    (hc : c = Functor.isoWhiskerRight ρ Rm ≪≫ d) (K : C) :
    (coefficientQuotientNatTrans am an P c).app K ≫ ρ.hom.app (Ln.obj K) =
      (coefficientQuotientNatTrans am an Q d).app K := by
  apply (am.homEquiv _ _).injective
  rw [am.homEquiv_naturality_right]
  dsimp only [coefficientQuotientNatTrans, Functor.comp_obj]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hc]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Category.assoc, ← Rm.map_comp, Iso.inv_hom_id_app, Rm.map_id]
  erw [Category.comp_id]

private theorem restriction_comp_change (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    let := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
      (compactSupportLevelQuotient l E m n h)
    let := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
      (compactSupportLevelQuotient l E m n h)
    compactSupportSystemRestrictionComp l E W h =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W h)))
        (scalarReductionDerivedRestriction l E W m) ≪≫
      compactSupportRestrictionComp l E W m n h := by
  let := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  let := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  let e := compactSupportModuleRes_eq l E W h
  let h₀ := coefficientRestrictionComp l E W h
  have h₁ : proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h) ⋙
        scalarReductionRestriction l E W m = scalarReductionRestriction l E W n :=
    (congrArg (fun F ↦ F ⋙ scalarReductionRestriction l E W m) e).symm.trans h₀
  have he : pbcRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E W m)
      (compactSupportLevelSheafQuotient l E W m n h)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportProjection_comp l E W m n h) = eqToIso h₁ := by
    apply scalarComp_eqToIso
  unfold compactSupportSystemRestrictionComp compactSupportRestrictionComp pbcDerivedRestrictComp
  rw [he]
  exact derivedComp_change _ _ _ _ _ (eqIso_comp _ e h₁ h₀)

/-- Reduction evaluations carry actual system transitions to scalar-adjunction quotient maps.
Source: Zheng Construction 4.1 and Proposition 4.21; Stacks 0941.
(blueprint: lem-weil-system-reduction-quotient-transitions).

Proof: compare the native and normalized ordinary transition maps on sections and
localize that equality. The reduction unit and total-limit projection equations
identify the native transition with its scalar-adjunction mate. Change the scalar
restriction compositor along the canonical presentation equality, then cancel the
comparison isomorphism. This works for every pair of levels, including equal ones. -/
theorem systemReductionQuotient_transitions (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    {m n : ℕ} (h : n ≤ m) (K : DerivedCategory (scalarReductionSource l E W)) :
    (coefficientSequenceDerivedTransition l E W h).app (S.reduction.obj K) ≫
        (normalizedDVRRes l E W h).map ((S.reductionEvaluation n).hom.app K) =
      (S.reductionEvaluation m).hom.app K ≫ (systemReductionQuotient l E W h).app K := by
  let := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  let := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  let ρ := Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W h))
  apply (cancel_mono (ρ.hom.app ((coefficientFiniteDerivedExtension l E W n).obj K))).mp
  simp only [Category.assoc]
  erw [ρ.hom.naturality ((S.reductionEvaluation n).hom.app K)]
  have ht := NatTrans.congr_app (quotient_transition_comparison l E W h) (S.reduction.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at ht
  rw [← Category.assoc]
  dsimp only [Functor.comp_obj] at *
  erw [ht, compactSupportReductionTransition l E W S.toCoefficientDerivedSystemReduction h K]
  have hq := quotient_mate_change (coefficientFiniteAdjunction l E W m)
    (coefficientFiniteAdjunction l E W n) (normalizedDVRRes l E W h)
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory ρ
    (compactSupportSystemRestrictionComp l E W h)
    (compactSupportRestrictionComp l E W m n h) (restriction_comp_change l E W h) K
  simpa only [systemReductionQuotient, coefficientQuotientNatTrans, coefficientFiniteAdjunction,
    compactSupportReductionMap, coefficientFiniteDerivedExtension,
    coefficientFiniteDerivedRestriction, Functor.comp_obj, Category.assoc] using
    congrArg (fun z ↦ (S.reductionEvaluation m).hom.app K ≫ z) hq.symm

end WeilConjectures
