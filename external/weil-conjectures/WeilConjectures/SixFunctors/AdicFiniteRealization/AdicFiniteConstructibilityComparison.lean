/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicInternalFiniteFreeCriterion
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicSectionFiniteFreeTransport
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteFreeScalarTransport
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Constructibility in finite adic module presentations

Source: BS Definitions 6.8.1 and 6.8.8; HRS Theorem 7.7 and Lemma 7.9.
(blueprint: lem-sf-adic-finite-constructibility-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

omit dT iT in
private theorem finite_shrink_isometry
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    letI := coefficientExtensionNormedField l (pbcFiniteField.{u} l (PadicAlgCl l) E)
    Isometry (show pbcFiniteField.{u} l (PadicAlgCl l) E → E.val from
      Shrink.algEquiv (Padic l) E.val) := by
  let := coefficientExtensionNormedField l (pbcFiniteField.{u} l (PadicAlgCl l) E)
  let σ : pbcFiniteField.{u} l (PadicAlgCl l) E ≃ₐ[Padic l] E.val :=
    Shrink.algEquiv (Padic l) E.val
  let v : AbsoluteValue (pbcFiniteField.{u} l (PadicAlgCl l) E) ℝ :=
    { toFun := fun x ↦ ‖σ x‖
      map_mul' := fun x y ↦ by simp only [map_mul, norm_mul]
      nonneg' := fun _ ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero]
      add_le' := fun x y ↦ by simpa only [map_add] using norm_add_le (σ x) (σ y) }
  apply AddMonoidHomClass.isometry_of_norm σ
  intro x
  exact spectralNorm_unique_field_norm_ext (f := v)
    (fun a ↦ by
      change ‖σ (algebraMap (Padic l) _ a)‖ = ‖a‖
      rw [σ.commutes]
      exact norm_algebraMap' E.val a) x

omit dT iT in
private def finite_chart_iso (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T)
      (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) ≅
        rationalCoefficientSheaf l T (pbcFiniteField.{u} l (PadicAlgCl l) E) := by
  letI := coefficientExtensionNormedField l (pbcFiniteField.{u} l (PadicAlgCl l) E)
  let σ : pbcFiniteField.{u} l (PadicAlgCl l) E ≃ₐ[Padic l] E.val :=
    Shrink.algEquiv (Padic l) E.val
  have hσ : Continuous σ := (finite_shrink_isometry l E).continuous
  have hσi : Continuous σ.symm :=
    ((finite_shrink_isometry l E).right_inv σ.right_inv).continuous
  letI : IsUltrametricDist E.val := IsUltrametricDist.of_normedAlgebra (Padic l)
  let A := AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E
  let D : Sheaf (ProEt.topology T) Ab.{u + 1} := (sheafCompose (ProEt.topology T)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (AlgebraicGeometry.ProEtale.continuousMapRingSheaf T E.val)
  let e : A ≅ D := asIso (AlgebraicGeometry.ProEtale.chartComparison T E.val)
  let e' : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T) A ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T) D :=
    { hom := AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T e.hom
      inv := AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T e.inv
      hom_inv_id := by
        ext U x
        change e.inv.hom.app U (e.hom.hom.app U x) = x
        exact ConcreteCategory.congr_hom (congrArg (fun f : A ⟶ A ↦ f.hom.app U)
          e.hom_inv_id) x
      inv_hom_id := by
        ext U x
        change e.hom.hom.app U (e.inv.hom.app U x) = x
        exact ConcreteCategory.congr_hom (congrArg (fun f : D ⟶ D ↦ f.hom.app U)
          e.inv_hom_id) x }
  let r := AlgebraicGeometry.ProEtale.CondensedRing.reconstructedRingIso T
    (AlgebraicGeometry.ProEtale.continuousMapRingSheaf T E.val)
  let τ : E.val ≃+* ULift.{u + 1, u} (pbcFiniteField.{u} l (PadicAlgCl l) E) :=
    σ.symm.toRingEquiv.trans ULift.ringEquiv.symm
  have hτ : Continuous τ := continuous_uliftUp.comp hσi
  have hτi : Continuous τ.symm := hσ.comp continuous_uliftDown
  let ec (U : T.ProEtᵒᵖ) : C(U.unop.left, E.val) ≃+*
      C(U.unop.left, ULift.{u + 1, u} (pbcFiniteField.{u} l (PadicAlgCl l) E)) :=
    { τ.toRingHom.compLeftContinuous U.unop.left hτ with
      invFun := τ.symm.toRingHom.compLeftContinuous U.unop.left hτi
      left_inv f := by
        apply ContinuousMap.ext
        intro x
        exact τ.symm_apply_apply (f x)
      right_inv f := by
        apply ContinuousMap.ext
        intro x
        exact τ.apply_symm_apply (f x) }
  let j : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T) D ≅
      rationalCoefficientSheaf l T (pbcFiniteField.{u} l (PadicAlgCl l) E) := by
    apply ObjectProperty.isoMk _
    refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · let er :
          ((InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (ProEt.topology T) D).obj.obj U) ≃+* ULift C(U.unop.left, E.val) :=
        Iso.ringCatIsoToRingEquiv
          (((sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}).mapIso r).app U)
      exact (er.trans (ULift.ringEquiv.trans (ec U))).toCommRingCatIso
    · intro U V f
      ext x
      rfl
  exact e' ≪≫ j

omit dT iT [AlgebraicGeometry.IsNoetherian T] in
private theorem finite_chart_normalization
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (U : T.ProEtᵒᵖ)
    (s : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology T) (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E)).obj.obj U)
    (x : U.unop.left) :
    (Shrink.algEquiv (Padic l) E.val)
      (rationalCoefficientValue l (pbcFiniteField.{u} l (PadicAlgCl l) E) T U
        ((finite_chart_iso l T E).hom.hom.app U s) x) =
      (((AlgebraicGeometry.ProEtale.chartComparison T E.val).hom.app U) s).down x := by
  change (Shrink.algEquiv (Padic l) E.val)
    ((Shrink.algEquiv (Padic l) E.val).symm
      ((((AlgebraicGeometry.ProEtale.chartComparison T E.val).hom.app U) s).down x)) = _
  exact (Shrink.algEquiv (Padic l) E.val).apply_symm_apply _

private theorem finite_chart_coefficient (C : Core l T) (B : ScalarData l T C)
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) :
    (finite_chart_iso l T E).hom ≫ (B.coefficient h).coefficient =
      AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap T l h) ≫
          (finite_chart_iso l T F).hom := by
  let := coefficientExtensionNormedField l (pbcFiniteField.{u} l (PadicAlgCl l) F)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext s : 1
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  apply (Shrink.algEquiv (Padic l) F.val).injective
  change (Shrink.algEquiv (Padic l) F.val)
    (rationalCoefficientValue l (pbcFiniteField.{u} l (PadicAlgCl l) F) T U
      ((B.coefficient h).coefficient.hom.app U
        ((finite_chart_iso l T E).hom.hom.app U s)) x) = _
  rw [(B.coefficient h).coefficient_normalization]
  change (Shrink.algEquiv (Padic l) F.val)
    ((Shrink.algEquiv (Padic l) F.val).symm
      ((IntermediateField.inclusion h)
        ((Shrink.algEquiv (Padic l) E.val)
          (rationalCoefficientValue l (pbcFiniteField.{u} l (PadicAlgCl l) E) T U
            ((finite_chart_iso l T E).hom.hom.app U s) x)))) =
    (Shrink.algEquiv (Padic l) F.val)
      (rationalCoefficientValue l (pbcFiniteField.{u} l (PadicAlgCl l) F) T U
        ((finite_chart_iso l T F).hom.hom.app U
          ((AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T
            (AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap T l h)).hom.app U s)) x)
  rw [AlgEquiv.apply_symm_apply]
  erw [finite_chart_normalization, finite_chart_normalization]
  have hn := AlgebraicGeometry.ProEtale.chartComparison_naturality T E.val F.val
    (IntermediateField.inclusion h).toRingHom (continuous_subtype_val.subtype_mk _)
  have h₁ := congrArg (fun f ↦ f.hom.app U) hn
  have hv := ConcreteCategory.congr_hom h₁ s
  exact (congrArg (fun a ↦ a.down x) hv).symm

private def finite_closure_data (C : Core l T) (B : ScalarData l T C) :
    ClosureData l T C B := by
  let e := finite_chart_iso l T
  let m (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T
      (AlgebraicGeometry.ProEtale.padicSubfieldRingObjToPadicAlgCl T l E)
  refine {
    leg := fun E ↦ (e E).inv ≫ m E
    finiteIso := e
    finite_normalization := finite_chart_normalization l T
    leg_normalization := fun E ↦ by
      simp only [Iso.hom_inv_id_assoc]
      rfl
    coefficient_normalization := finite_chart_coefficient l T C B
    cocone := ?_ }
  intro E F h
  dsimp only [e]
  apply (cancel_epi (finite_chart_iso l T E).hom).1
  rw [← Category.assoc, finite_chart_coefficient l T C B h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext s : 1
  change ((AlgebraicGeometry.ProEtale.padicSubfieldRingObjToPadicAlgCl T l F).hom.app U)
    (((AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap T l h).hom.app U) s) =
      ((AlgebraicGeometry.ProEtale.padicSubfieldRingObjToPadicAlgCl T l E).hom.app U) s
  have h₀ := AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgCl T l h
  have h₁ := congrArg (fun f ↦ f.hom.app U) h₀
  exact ConcreteCategory.congr_hom h₁ s

/-- Actual finite coefficient legs and the four constructibility comparisons.
Source: finite realization node, step 3; BS Definition 6.8.8; HRS 7.7 and 7.9
(blueprint: lem-sf-adic-finite-constructibility-comparison).

Proof:
1. The point-adjunction comparison identifies the section ring of the pulled-back
continuous E-ring with continuous E-valued functions. Compose with the spectral
coefficient equivalence Shrink.algEquiv to get finiteIso. Its formula on every
section and point gives finite_normalization. Define leg by finiteIso inverse
followed by sectionRingMap of the actual finite-subfield inclusion into Omega.
2. chartComparison naturality for field inclusions and the normalized coefficient
formula in B.coefficient give coefficient_normalization. SectionRingMap preserves
composition, so the two finite inclusions into Omega coincide. Cancel finiteIso
to obtain cocone; leg_normalization holds by its construction.
3. On each finite locally closed stratum, continuous finite-field lfp modules are
locally finite free by condensedField local triviality. The finite-subextension
Omega version is condensedQbar_lfp_locally_free. Conversely a finite free module
has the presentation with zero relations. Pullback to strata respects these
coefficient rings. Apply this in every cohomological degree to identify the internal
constructibility predicates. The bounded standard t-structure gives an ordered
interval by replacing the lower bound with the minimum of both bounds.
4. The section-module equivalence preserves underlying sheaves, finite free objects,
exact sequences and restrictions, hence the local finite free predicates. Its exact
derived equivalence preserves homology and both degree bounds. The exact equivalence
of extension along finiteIso preserves those same data. Transporting the preceding
internal criteria gives finite_sections and closure_sections. Covers allow rank zero
and the empty scheme; the Omega ring remains finite-subextension-valued throughout. -/
theorem adic_finite_constructibility_comparison (C : Core l T) (B : ScalarData l T C) :
    ∃ R : ClosureData l T C B,
      (∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K ↔
      internalFiniteFreeTarget T
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K) ∧
      (∀ K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K ↔
      internalFiniteFreeTarget T
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K) ∧
      (∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K ↔
      finiteFreeTarget T (rationalCoefficientSheaf l T
        (pbcFiniteField.{u} l (PadicAlgCl l) E))
        ((pbcDerivedExtend (R.finiteIso E).hom).obj
          ((sectionDerived T (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E)).obj K))) ∧
      (∀ K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K ↔
      finiteFreeTarget T (closureRing l T)
        ((sectionDerived T
          (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T)).obj K))
      := by
  let R := finite_closure_data l T C B
  refine ⟨R, finite_internal_constructibility T l, closure_internal_constructibility T l,
    ?_, ?_⟩
  · intro E K
    exact (finite_internal_constructibility T l E K).trans
      ((section_finiteFreeTarget T _ K).trans
        (finiteFreeTarget_coefficientIso (R.finiteIso E) _))
  · intro K
    exact (closure_internal_constructibility T l K).trans
      (section_finiteFreeTarget T _ K)

end WeilConjectures.AdicFiniteRealization
