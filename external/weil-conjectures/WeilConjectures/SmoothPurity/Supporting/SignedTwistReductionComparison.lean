/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import WeilConjectures.SmoothPurity.Supporting.FlatLineDerivedReduction
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Normalized reduction of signed completed Tate lines

Source: definition-tate-twists--10, proof steps 1 and 6.
(blueprint: lem-weil-signed-twist-reduction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local irreducible] WeilConjectures.scalarReductionExistence
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.sheafCompose
  SheafOfModules.unit PresheafOfModules.unit
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

private abbrev ReductionMaps (n : ℕ) := ∀ k : ℤ, integralTwistLine l E S k ⟶
  (scalarReductionRestriction.{u, u} l E S n).obj (finiteCoefficientTwist l E S n k)

private def ReductionNormalized (n : ℕ) (c : ReductionMaps l E S n) : Prop :=
(∀ (U : S.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted.{u, u} l E S).obj.obj U),
    (c 0).val.app U a =
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U),
    (c 1).val.app U x = ((((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E S n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient S l E n) (purTwistIntegralOne S l E))).app U)
      ((1 : (integralCoefficientSheaf l E S n).obj.obj U) ⊗ₜ[
        (purTwistIntegralConstant S l E).obj.obj U,
        ((purTwistIntegralQuotient S l E n).hom.app U).hom] x))) ∧
  (∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U)
      (y : (purTwistIntegralModule S l E).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
      (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := integralCoefficientCommRingSheaf.{u, u} l E S n) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine l E S (Int.negSucc k)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U),
    (((c (Int.negSucc k)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
      ((c (Int.ofNat (k + 1))).val.app U x) =
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

private def ReductionFormula (n : ℕ) (c : ReductionMaps l E S n) (k : ℤ)
    (a : (scalarReductionExtension.{u, u} l E S n).obj (integralTwistLine l E S k) ≅
      finiteCoefficientTwist l E S n k) : Prop :=
  ∀ (U : S.ProEtᵒᵖ) (r : (integralCoefficientCommRingSheaf.{u, u} l E S n).obj.obj U)
    (x : (integralTwistLine l E S k).val.obj U),
    a.hom.val.app U (sfReductionTensor l E S n (integralTwistLine l E S k) U r x) =
      r • (@id ((finiteCoefficientTwist l E S n k).val.obj U) ((c k).val.app U x))

omit [∀ x : S, Invertible (l : S.residueField x)] in
private theorem extension_iso_tmul
    (n : ℕ) (M : scalarReductionSource.{u, u} l E S) (U : S.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf.{u, u} l E S n).obj.obj U)
    (x : M.val.obj U) :
    ((eqToIso ((scalarReductionExistence.{u, u} l E S n).choose_spec.choose M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n) M).hom.val.app U)
        (sfReductionTensor l E S n M U a x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n) M U a x := by
  let α := completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralCoefficientCommRingSheaf.{u, u} l E S n)).obj)
  have hn := adj.unit.naturality
    (SheafOfModules.ScalarHomOrdinary.extensionPresheafIso.{u + 1, u, u + 1} α M).hom
  have hh := congrArg (fun f ↦ f.app U
    (a ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l E S).obj.obj U,
      (α.hom.app U).hom] x)) hn
  let h := (scalarReductionExistence.{u, u} l E S n).choose_spec.choose M
  change (SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} α M).hom.val.app U
    (((eqToHom h.symm ≫ eqToHom h).val.app U) _) = _
  simp only [eqToHom_trans, eqToHom_refl]
  exact hh.symm

private theorem reduction_line_cover
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [M.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (u + 1)) (V : I → S.ProEt), (ProEt.topology S).CoversTop V ∧
      ∀ i, Nonempty (M.over (V i) ≅ SheafOfModules.unit.{u, u + 1, u + 1}
        (((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (V i))) := by
  classical
  obtain ⟨I, V, hV, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
      (M := M) (r := 1)).mp inferInstance
  exact ⟨I, V, hV, fun i ↦ ⟨(e i).some ≪≫ SheafOfModules.freeUniqueIso.{u + 1, u, u + 1} _⟩⟩

private theorem reduction_exists (n : ℕ) :
    ∃ c : ReductionMaps l E S n, ReductionNormalized l E S n c ∧
      ∀ k : ℤ, ∃! a, ReductionFormula l E S n c k a := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S
  let Q := integralCoefficientCommRingSheaf.{u, u} l E S n
  let p := completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n
  let L := purTwistIntegralModule S l E
  let N := purTwistFiniteOne S l E n
  obtain ⟨b, hb⟩ := signedTwistFirstReduction l E S n
  obtain ⟨B, hB, heval, _⟩ := SheafOfModules.exists_signedLineComparison.{u + 1, u, u + 1}
    p L N (reduction_line_cover S R L) (reduction_line_cover S Q N) b
  let c : ReductionMaps l E S n := fun k ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} p (integralTwistLine l E S k) ≫
      (scalarReductionRestriction.{u, u} l E S n).map (B k).hom
  have hc (k : ℤ) (U : S.ProEtᵒᵖ) (x : (integralTwistLine l E S k).val.obj U) :
      (c k).val.app U x = (B k).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E S k) U 1 x) := rfl
  refine ⟨c, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro U a
    rw [hc, hB.1]
    exact (SheafOfModules.scalarExtensionUnitIso_tmul.{u + 1, u, u + 1}
      p U 1 a).trans (one_mul ((p.hom.app U).hom a))
  · intro U x
    rw [hc, hB.2.1]
    exact hb U x
  · intro k U x y
    rw [hc, hc, hc, hB.2.1]
    exact hB.2.2.1 k U 1 x y
  · intro k U f x
    rw [hc, hc]
    exact (heval k U 1 1 f x).trans
      ((mul_one (((p.hom.app U).hom _) * 1)).trans (mul_one ((p.hom.app U).hom _)))
  · intro k
    let A := eqToIso ((scalarReductionExistence.{u, u} l E S n).choose_spec.choose
        (integralTwistLine l E S k)) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} p (integralTwistLine l E S k)
    let a := A ≪≫ B k
    have ha : ReductionFormula l E S n c k a := by
      intro U r x
      change (B k).hom.val.app U (A.hom.val.app U _) = _
      rw [extension_iso_tmul]
      rw [show SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E S k) U r x =
        r • SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E S k) U 1 x by
          exact (SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
            p (integralTwistLine l E S k) U r 1 x).trans
              (congrArg (fun t ↦ SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
                p (integralTwistLine l E S k) U t x) (mul_one r)) |>.symm]
      exact ((B k).hom.val.app U).hom.map_smul r _
    refine ⟨a, ha, ?_⟩
    intro a' ha'
    apply Iso.ext
    apply (cancel_epi A.inv).mp
    apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
      p (integralTwistLine l E S k)
    intro U r x
    have hi : A.inv.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E S k) U r x) =
          sfReductionTensor l E S n (integralTwistLine l E S k) U r x := by
      have hh := extension_iso_tmul l E S n (integralTwistLine l E S k) U r x
      exact (congrArg (fun z ↦ A.inv.val.app U z) hh).symm.trans
        (congrArg (fun f ↦ f.val.app U
          (sfReductionTensor l E S n (integralTwistLine l E S k) U r x)) A.hom_inv_id)
    change a'.hom.val.app U (A.inv.val.app U _) = a.hom.val.app U (A.inv.val.app U _)
    exact (congrArg (fun z ↦ a'.hom.val.app U z) hi).trans
      ((ha' U r x).trans ((ha U r x).symm.trans
        (congrArg (fun z ↦ a.hom.val.app U z) hi).symm))

omit [∀ x : S, Invertible (l : S.residueField x)] in
private theorem reduction_positive_unique (n : ℕ) (c d : ReductionMaps l E S n)
    (hc : ReductionNormalized l E S n c) (hd : ReductionNormalized l E S n d) :
    ∀ k : ℕ, c (Int.ofNat k) = d (Int.ofNat k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (hc.1 U a).trans (hd.1 U a).symm
  | one =>
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hc.2.1 U x).trans (hd.2.1 U x).symm
  | more k _ ih =>
    apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1} _ _
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S)
    intro U x y
    calc
      _ = _ := hc.2.2.1 k U x y
      _ = _ := ?_
      _ = _ := (hd.2.2.1 k U x y).symm
    rw [ih]
    congr 1
    exact (hc.2.1 U y).trans (hd.2.1 U y).symm

omit [∀ x : S, Invertible (l : S.residueField x)] in
private theorem reduction_unique (n : ℕ) (c d : ReductionMaps l E S n)
    (hc : ReductionNormalized l E S n c) (hd : ReductionNormalized l E S n d)
    (hi : ∀ k : ℤ, ∃! a, ReductionFormula l E S n c k a) : d = c := by
  classical
  have hpos := reduction_positive_unique l E S n c d hc hd
  let p := completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n
  funext k
  cases k with
  | ofNat k => exact (hpos k).symm
  | negSucc k =>
    let P := coefficientTwistPower S
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E S) (purTwistIntegralModule S l E)
      (k + 1)
    obtain ⟨a, ha, _⟩ := hi (Int.ofNat (k + 1))
    let A := eqToIso ((scalarReductionExistence.{u, u} l E S n).choose_spec.choose P) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} p P
    let B := A.symm ≪≫ a
    have hB (U : S.ProEtᵒᵖ) (r : (integralCoefficientCommRingSheaf.{u, u} l E S n).obj.obj U)
        (x : P.val.obj U) :
        B.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p P U r x) =
          r • (@id ((finiteCoefficientTwist l E S n (Int.ofNat (k + 1))).val.obj U)
            ((c (Int.ofNat (k + 1))).val.app U x)) := by
      have hh : A.inv.val.app U
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p P U r x) =
          sfReductionTensor l E S n P U r x := by
        have hh0 := extension_iso_tmul l E S n P U r x
        exact (congrArg (fun z ↦ A.inv.val.app U z) hh0).symm.trans
          (congrArg (fun f ↦ f.val.app U (sfReductionTensor l E S n P U r x))
            A.hom_inv_id)
      change a.hom.val.app U (A.inv.val.app U _) = _
      exact (congrArg (fun z ↦ a.hom.val.app U z) hh).trans (ha U r x)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    let T := PresheafOfModules.restrictOver
      (integralCoefficientCommRingSheaf l E S n).obj U.unop
    have hT : IsIso (T.map B.hom.val) := by
      have : IsIso B.hom.val := by
        exact (SheafOfModules.forget _).map_isIso B.hom
      infer_instance
    apply (cancel_epi (T.map B.hom.val)).mp
    apply SheafOfModules.scalarDual_section_ext.{u + 1, u, u + 1} p P U
    intro W r x
    let V := Opposite.op W.unop.left
    let i := W.unop.hom.op
    have hrestrict (g : ReductionMaps l E S n) :
        ((g (Int.negSucc k)).val.app U f).app W
          ((c (Int.ofNat (k + 1))).val.app V x) =
        ((g (Int.negSucc k)).val.app V
          ((integralTwistLine l E S (Int.negSucc k)).val.map i f)).app
            (Opposite.op (Over.mk (𝟙 V.unop)))
              ((c (Int.ofNat (k + 1))).val.app V x) := by
      rw [PresheafOfModules.naturality_apply (g (Int.negSucc k)).val]
      change _ = ((g (Int.negSucc k)).val.app U f).app
        (Opposite.op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) _
      exact (PresheafOfModules.restrictOver_hom_app_congr
        ((g (Int.negSucc k)).val.app U f) (Category.id_comp W.unop.hom) _).symm
    change ((d (Int.negSucc k)).val.app U f).app W
        (B.hom.val.app V
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p P V r x)) =
      ((c (Int.negSucc k)).val.app U f).app W
        (B.hom.val.app V (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p P V r x))
    rw [hB]
    rw [map_smul, map_smul]
    congr 1
    change ((d (Int.negSucc k)).val.app U f).app W
        ((c (Int.ofNat (k + 1))).val.app V x) =
      ((c (Int.negSucc k)).val.app U f).app W
        ((c (Int.ofNat (k + 1))).val.app V x)
    refine (hrestrict d).trans (Eq.trans ?_ (hrestrict c).symm)
    calc
      _ = (completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n).hom.app V
          ((((integralTwistLine l E S (Int.negSucc k)).val.map i f).app
            (Opposite.op (Over.mk (𝟙 V.unop)))) x) := by
        rw [hpos (k + 1)]
        exact hd.2.2.2 k V _ x
      _ = _ := (hc.2.2.2 k V _ x).symm

/-- Reduction respects signed powers, dual evaluation, and exact derived line tensor.
Source: blueprint definition-tate-twists--10, proof steps 1 and 6
(blueprint: lem-weil-signed-twist-reduction-comparison).

Proof: the integral first line reduces to its prescribed finite line by the original
quotient tensor construction. The reduction of the unit is the coefficient projection.
Tensor these maps recursively to obtain the positive powers. For a negative power,
use the unique map of duals compatible with the evaluation pairing. On a cover
trivializing the integral line these maps are the quotient coefficient maps, and
the induced scalar extensions are the identity on the quotient coefficient unit.
Thus all induced extension maps are isomorphisms. They glue because their equations
on tensors and evaluations are independent of the local basis. These equations also
prove uniqueness, first at zero and one, then by induction on positive powers and
by nondegeneracy of the dual pairing at negative powers. For derived comparisons,
resolve K by a flat-term K-flat complex P. Exact line tensor preserves K-flatness
and flat terms. Reduction of P is K-flat over the quotient ring. Rebracketing sends
(x tensor y) tensor a to (x tensor a) tensor (y tensor 1), and its inverse multiplies
the two quotient coefficients. The balanced maps commute with differentials and
with every chain map, so descend to the displayed natural derived isomorphism.
The same computation on the flat degree-zero line gives the single-object comparison.
All formulas commute with quotient transitions and the unit augmentations. -/
theorem signedTwistReduction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ, ∃! c : (∀ k : ℤ, integralTwistLine l E S k ⟶
      (scalarReductionRestriction l E S n).obj (finiteCoefficientTwist l E S n k)),
    ((∀ (U : S.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U),
    (c 0).val.app U a = (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U),
    (c 1).val.app U x = ((((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E S n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient S l E n) (purTwistIntegralOne S l E))).app U)
      ((1 : (integralCoefficientSheaf l E S n).obj.obj U) ⊗ₜ[
        (purTwistIntegralConstant S l E).obj.obj U,
        ((purTwistIntegralQuotient S l E n).hom.app U).hom] x))) ∧
  (∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U)
      (y : (purTwistIntegralModule S l E).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
      (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := integralCoefficientCommRingSheaf l E S n) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine l E S (Int.negSucc k)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U),
    (((c (Int.negSucc k)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
      ((c (Int.ofNat (k + 1))).val.app U x) =
      (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)) ∧
    ∀ k : ℤ, ∃! α : (scalarReductionExtension l E S n).obj
        (integralTwistLine l E S k) ≅ finiteCoefficientTwist l E S n k,
      ∀ (U : S.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
          (x : (integralTwistLine l E S k).val.obj U),
        α.hom.val.app U (sfReductionTensor l E S n (integralTwistLine l E S k) U a x) =
          a • (@id ((finiteCoefficientTwist l E S n k).val.obj U) ((c k).val.app U x))) ∧
    (∀ k : ℤ, ∀ n : ℕ, Nonempty ((scalarReductionDerivedExtension l E S n).obj
      (sfIntegralTwistingObject l E S k) ≅
        (DerivedCategory.singleFunctor _ 0).obj (finiteCoefficientTwist l E S n k))) ∧
    ∀ (m : ℤ) (n : ℕ), Nonempty (sfIntegralTwistingFunctor l E S m ⋙
      scalarReductionDerivedExtension l E S n ≅
      scalarReductionDerivedExtension l E S n ⋙ finiteComplexTwist l E S n m) := by
  have hordinary : ∀ n : ℕ, ∃! c : ReductionMaps l E S n,
      ReductionNormalized l E S n c ∧ ∀ k : ℤ, ∃! a, ReductionFormula l E S n c k a := by
    intro n
    obtain ⟨c, hc, hi⟩ := reduction_exists l E S n
    refine ⟨c, ⟨hc, hi⟩, ?_⟩
    intro d hd
    exact reduction_unique l E S n c d hc hd.1 hi
  refine ⟨hordinary, ?_, ?_⟩
  · intro k n
    obtain ⟨c, hc, hi⟩ := (hordinary n).exists
    obtain ⟨a, _, _⟩ := hi k
    have := (signedLineTensor_equivalence S
      (completedIntegralCommRingSheafUnrestricted l E S) (purTwistIntegralModule S l E) k).1
    have := (signedLineTensor_equivalence S
      (integralCoefficientCommRingSheaf l E S n) (purTwistFiniteOne S l E n) k).1
    have hint := coefficientTwistLine_exact S
      (R := completedIntegralCommRingSheafUnrestricted l E S) (purTwistIntegralModule S l E) k
    have := hint.1
    have := hint.2.1
    have := hint.2.2
    have hex := coefficientTwistLine_exact S
      (R := integralCoefficientCommRingSheaf l E S n) (purTwistFiniteOne S l E n) k
    have := hex.1
    have := hex.2.1
    have := hex.2.2
    exact (flatLineDerivedReduction l E S n (integralTwistLine l E S k)
      (finiteCoefficientTwist l E S n k) a).1
  · intro k n
    obtain ⟨c, hc, hi⟩ := (hordinary n).exists
    obtain ⟨a, _, _⟩ := hi k
    have := (signedLineTensor_equivalence S
      (completedIntegralCommRingSheafUnrestricted l E S) (purTwistIntegralModule S l E) k).1
    have := (signedLineTensor_equivalence S
      (integralCoefficientCommRingSheaf l E S n) (purTwistFiniteOne S l E n) k).1
    have hint := coefficientTwistLine_exact S
      (R := completedIntegralCommRingSheafUnrestricted l E S) (purTwistIntegralModule S l E) k
    have := hint.1
    have := hint.2.1
    have := hint.2.2
    have hex := coefficientTwistLine_exact S
      (R := integralCoefficientCommRingSheaf l E S n) (purTwistFiniteOne S l E n) k
    have := hex.1
    have := hex.2.1
    have := hex.2.2
    exact (flatLineDerivedReduction l E S n (integralTwistLine l E S k)
      (finiteCoefficientTwist l E S n k) a).2

end WeilConjectures
