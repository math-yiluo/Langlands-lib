/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # Signed powers and ordinary scalar extension

(blueprint: lem-pur-integral-line-power-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
attribute [local irreducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.scalarReductionExistence
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem line_cover
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [M.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (u + 1)) (V : I → X.ProEt), (ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (M.over (V i) ≅ SheafOfModules.unit
        (((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (V i))) := by
  classical
  obtain ⟨I, V, hV, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
      (M := M) (r := 1)).mp inferInstance
  exact ⟨I, V, hV, fun i ↦ ⟨(e i).some ≪≫ SheafOfModules.freeUniqueIso.{u + 1, u, u + 1} _⟩⟩

private theorem extension_iso_tmul
    (n : ℕ) (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
    (x : M.val.obj U) :
    ((eqToIso ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1}
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n) M).hom.val.app U)
        (sfReductionTensor l E X n M U a x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n) M U a x := by
  let α := completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj)
  have hn := adj.unit.naturality
    (SheafOfModules.ScalarHomOrdinary.extensionPresheafIso.{u + 1, u, u + 1} α M).hom
  have hh := congrArg (fun f ↦ f.app U
    (a ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l E X).obj.obj U,
      (α.hom.app U).hom] x)) hn
  let h := (scalarReductionExistence.{u, u} l E X n).choose_spec.choose M
  change (SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} α M).hom.val.app U
    (((eqToHom h.symm ≫ eqToHom h).val.app U) _) = _
  simp only [eqToHom_trans, eqToHom_refl]
  exact hh.symm

private theorem ordinary_power_comparisons
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ b : PowerComparisons l E X L, PowerFormula l E X L b := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  let S (n : ℕ) := integralCoefficientCommRingSheaf.{u, u} l E X n
  let α (n : ℕ) := completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n
  let c (n : ℕ) (M : scalarReductionSource.{u, u} l E X) :
      (scalarReductionExtension.{u, u} l E X n).obj M ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (α n) M :=
    eqToIso ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} (α n) M
  have hc (n : ℕ) (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
      (a : (S n).obj.obj U) (x : M.val.obj U) :
      (c n M).hom.val.app U (sfReductionTensor l E X n M U a x) =
        SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} (α n) M U a x :=
    extension_iso_tmul l E X n M U a x
  have hci (n : ℕ) (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
      (a : (S n).obj.obj U) (x : M.val.obj U) :
      (c n M).inv.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} (α n) M U a x) =
        sfReductionTensor l E X n M U a x := by
    rw [← hc]
    exact congrArg (fun f ↦ f.val.app U (sfReductionTensor l E X n M U a x))
      (c n M).hom_inv_id
  have hL : L.IsInvertible :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).2 inferInstance
  let := hL
  have hex (n : ℕ) := by
    haveI :
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (α n) L).IsInvertible :=
      (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1} R (S n) (α n) L).1
    haveI : (line l E X L n).IsInvertible :=
      SheafOfModules.IsInvertible.of_iso.{u + 1, u, u + 1} (c n L).symm
    haveI : (line l E X L n).IsFiniteLocallyFreeOfRank 1 :=
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
        (line l E X L n)).1 inferInstance
    have h := SheafOfModules.exists_signedLineComparison.{u + 1, u, u + 1} (α n) L (line l E X L n)
      (line_cover X R L) (line_cover X (S n) (line l E X L n)) (c n L).symm
    dsimp only [SheafOfModules.SignedLineComparisonNormalized,
      SheafOfModules.SignedLineBasisPowers] at h
    exact h
  choose B hB hneg hlocal using hex
  let b : PowerComparisons l E X L := fun m n ↦ c n (power l E X L m) ≪≫ B n m
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro n U a x
    change (B n 0).hom.val.app U
      ((c n (power l E X L 0)).hom.val.app U _) = _
    rw [hc]
    rw [(hB n).1]
    calc
      _ = a * (α n).hom.app U x :=
        SheafOfModules.scalarExtensionUnitIso_tmul.{u + 1, u, u + 1} (α n) U a x
      _ = _ := mul_comm a ((α n).hom.app U x)
  · intro n U a x
    change (B n 1).hom.val.app U ((c n L).hom.val.app U _) = _
    rw [hc, (hB n).2.1]
    exact hci n L U a x
  · intro r n U a x y
    change (B n (Int.ofNat (r + 2))).hom.val.app U
      ((c n (power l E X L (Int.ofNat (r + 2)))).hom.val.app U _) = _
    rw [hc]
    erw [(hB n).2.2.1 r U a x y]
    change SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ U _
      ((c n L).inv.val.app U _) = _
    rw [hci]
    rw [← hc]
    rfl
  · intro r n U a t φ x
    change (((B n (Int.negSucc r)).hom.val.app U
      ((c n (power l E X L (Int.negSucc r))).hom.val.app U _)).app
        (op (Over.mk (𝟙 U.unop))))
        ((B n (Int.ofNat (r + 1))).hom.val.app U
          ((c n (power l E X L (Int.ofNat (r + 1)))).hom.val.app U _)) = _
    rw [hc, hc]
    exact hneg n r U a t φ x

private theorem line_evaluation_tmul
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [M.IsFiniteLocallyFreeOfRank 1] (U : X.ProEtᵒᵖ) (x : M.val.obj U)
    (φ : (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} M (SheafOfModules.unit _)).val.obj U) :
    (SheafOfModules.lineEvalIso.{u} R M).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} M _ U x φ) =
        φ.app (op (Over.mk (𝟙 U.unop))) x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (𝟙 _)
  have h : adj.homEquiv _ _ (SheafOfModules.lineEvalIso.{u} R M).hom =
      PresheafOfModules.lineEval M.val (PresheafOfModules.unit _) := by
    change adj.homEquiv _ _ (_ ≫ adj.counit.app _) = _
    simp only [asIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] φ)) h

private theorem ordinary_evaluations
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ e : Evaluations l E X L, EvaluationFormula l E X L e := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  have hr (r : ℕ) :
      (SheafOfModules.scalarTensorPower.{u + 1, u, u + 1} R L
        (r + 1)).IsFiniteLocallyFreeOfRank 1 := by
    change (power l E X L (Int.ofNat (r + 1))).IsFiniteLocallyFreeOfRank 1
    rw [power_eq_coefficient]
    exact (signedLineTensor_equivalence X R L (Int.ofNat (r + 1))).1
  let ep (r : ℕ) :
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
          (SheafOfModules.scalarTensorPower.{u + 1, u, u + 1} R L (r + 1))
          (SheafOfModules.unit _))).obj
            (SheafOfModules.scalarTensorPower.{u + 1, u, u + 1} R L (r + 1)) ≅
        SheafOfModules.unit _ := by
    letI := hr r
    exact SheafOfModules.lineEvalIso.{u} R _
  let sw (P Q : scalarReductionSource.{u, u} l E X) :=
    (PresheafOfModules.sheafification
      (R := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
        (𝟙 _)).mapIso (SheafOfModules.scalarTensorSwapRawIso.{u + 1, u, u + 1} P.val Q.val)
  let e : Evaluations l E X L := fun m ↦ match m with
    | .ofNat 0 => SheafOfModules.scalarTensorLeftUnitor R (SheafOfModules.unit _)
    | .ofNat (r + 1) => ep r
    | .negSucc r => sw _ _ ≪≫ ep r
  refine ⟨e, ?_, ?_, ?_⟩
  · intro U a c
    exact SheafOfModules.scalarTensorLeftUnitor_tmul R (SheafOfModules.unit _) U a c
  · intro r U x φ
    let : (power l E X L (Int.ofNat (r + 1))).IsFiniteLocallyFreeOfRank 1 := hr r
    exact line_evaluation_tmul X R (power l E X L (Int.ofNat (r + 1))) U x φ
  · intro r U x φ
    let P := power l E X L (Int.ofNat (r + 1))
    let Q := power l E X L (Int.negSucc r)
    let : P.IsFiniteLocallyFreeOfRank 1 := hr r
    have hs : (sw Q P).hom.val.app U
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} Q P U φ x) =
          SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} P Q U x φ :=
      SheafOfModules.scalarSheafification_map_unit
        (SheafOfModules.scalarTensorSwapRawIso.{u + 1, u, u + 1}
          (R := R) Q.val P.val).hom U (φ ⊗ₜ[R.obj.obj U] x)
    change (ep r).hom.val.app U ((sw Q P).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} Q P U φ x)) = _
    rw [hs]
    exact line_evaluation_tmul X R P U x φ

/-- Signed powers commute with ordinary quotient extension, and opposite powers
have the prescribed sheaf evaluations.
Source: Stacks 03EL, 04TT; blueprint proof (3), local signed bases.
(blueprint: lem-pur-integral-line-power-comparisons).

Proof: trivialize L with a basis e. Its positive tensor powers have the tensor basis,
the zeroth power has basis 1, and its negative powers have the dual basis. Opposite
powers pair by multiplication in these bases; the inverse sends a to a times the
first basis tensored with the second. A basis change by a unit acts in degree m by
its mth power, so the pairings glue. On extension of scalars use the unit comparison
at zero and the identity at one. Recursively balance the positive tensor powers.
For a negative power extend the functional and precompose with the inverse positive
comparison. Evaluation cancels that inverse and gives residue(phi(x))*a*c. These
maps are isomorphisms in each basis and hence globally. Their positive formulas are
the binary balancing formulas, and the three evaluation formulas are multiplication
at zero and functional evaluation in the two orders. -/
theorem integral_line_power_comparisons
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ (b : PowerComparisons l E X L) (e : Evaluations l E X L),
      PowerFormula l E X L b ∧ EvaluationFormula l E X L e := by
  obtain ⟨b, hb⟩ := ordinary_power_comparisons l E X L
  obtain ⟨e, he⟩ := ordinary_evaluations l E X L
  exact ⟨b, e, hb, he⟩

end WeilConjectures.IntegralLineReduction
