/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.Integral.IntegralPrincipalConeQuotientAugmentation

/-! # The normalized principal-cone comparison with integral quotients

Source: Stacks Tags 0A0E, 093M and 0941.
(blueprint: lem-pur-integral-principal-cone-quotient-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

private theorem principalConeComparison
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory A]
    {P : CochainComplex A ℤ} (μ : End P) (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (u : ∀ n : ℕ, P ⟶ C.obj (op n))
    (hv : Pi.lift u ≫ towerTransitionEndomorphism
      (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C) = 0)
    (a : ∀ n, CochainComplex.PrincipalCone.level μ n ⟶ C.obj (op n))
    (ha : ∀ n, QuasiIso (a n))
    (hs : ∀ n, CochainComplex.PrincipalCone.step μ n ≫ a n =
      a (n + 1) ≫ integralOperationsTowerStep C n)
    (hu : ∀ n, CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ a n = u n) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ) ≅
        DerivedCategory.Q.obj (integralOperationsRoos C),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ c.hom =
        DerivedCategory.Q.map (CochainComplex.mappingCocone.lift _ (Pi.lift u) 0
          (by simp [hv])) := by
  classical
  let p : (∏ᶜ fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)) ⟶
      ∏ᶜ (fun n ↦ C.obj (op n)) := Limits.Pi.map
    (f := fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n))
    (g := fun n ↦ C.obj (op n)) a
  let f := CochainComplex.PrincipalCone.oneSubShift μ
  let g := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
    (integralOperationsTowerStep C)
  have hfg : f ≫ p = p ≫ g := by
    exact (towerTransitionEndomorphism_natural_backward
      (K := fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n))
      (K' := fun n ↦ C.obj (op n))
      (CochainComplex.PrincipalCone.step μ) (integralOperationsTowerStep C) a
      (fun n ↦ (hs n).symm)).symm
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans
        (F := Discrete.functor (fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)))
        (G := Discrete.functor (fun n ↦ C.obj (op n)))
        (fun n ↦ a n.as)).app n) := ha n.as
  have hp : QuasiIso p := HomologicalComplex.quasiIso_limMap
    (Discrete.natTrans (F := Discrete.functor
      (fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)))
      (G := Discrete.functor (fun n ↦ C.obj (op n))) (fun n ↦ a n.as))
  let m := CochainComplex.mappingCone.map f g p p hfg
  let τ := CochainComplex.mappingCone.triangleMap f g p p hfg
  have hm : IsIso (DerivedCategory.Q.map m) :=
    Pretriangulated.isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished f)
      (DerivedCategory.mappingCone_triangle_distinguished g)
      (inferInstance : IsIso (DerivedCategory.Q.map p))
      (inferInstance : IsIso (DerivedCategory.Q.map p))
  have : QuasiIso m := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hm
  let b := m⟦(-1 : ℤ)⟧'
  have : QuasiIso b := inferInstance
  let c := asIso (DerivedCategory.Q.map b)
  have hn : (𝟙 P) ≫ Pi.lift u = CochainComplex.PrincipalCone.productUnit μ ≫ p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.id_comp, p, Category.assoc, Limits.Pi.map_π,
      CochainComplex.PrincipalCone.productUnit, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact (hu n).symm
  have hb : CochainComplex.PrincipalCone.unit μ ≫ b =
      CochainComplex.mappingCocone.lift g (Pi.lift u) 0 (by
        have hv' : Pi.lift u ≫ g = 0 := hv
        simp only [CochainComplex.HomComplex.δ_zero, zero_add, hv',
          CochainComplex.HomComplex.Cochain.ofHom_zero]) := by
    simpa only [Category.id_comp, CochainComplex.PrincipalCone.unit, b, m, f] using
      (completedCoconeLift_natural A f g p p hfg (𝟙 P)
        (CochainComplex.PrincipalCone.productUnit μ) (Pi.lift u)
        (CochainComplex.PrincipalCone.productUnit_comp μ) hv hn).symm
  refine ⟨c, ?_⟩
  change DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫
    DerivedCategory.Q.map b = _
  rw [← Functor.map_comp, hb]

/-- The regular one-generator cone tower and the actual finite quotient tower have
isomorphic Roos complexes in the derived category, preserving the entire specified unit.
Only K-flatness is required; the terms need not be flat.

Source: Stacks Tags 0A0E, 093M and 0941.
(blueprint: lem-pur-integral-principal-cone-quotient-comparison).

Proof: the normalized principal-cone quotient augmentation supplies a strict,
levelwise quasi-isomorphic comparison, preserving the actual quotient augmentations.
The product comparison commutes with one minus the two transition shifts. Exact
countable products make it a quasi-isomorphism. The induced cone-triangle morphism
has invertible first two components after localization, hence also its third.
Shift by minus one and localize to obtain c. After every product projection the
strict augmentation equation identifies the product units. Naturality of the
zero-homotopy cocone lift proves equality of the entire units, including their zero
second cochains. Localization preserves this equality. This also covers zero P and
the first positive exponent. -/
theorem integralPrincipalConeQuotientComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})
    (P : IntegralOnSlice.Cx l E T none)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) P)
    (μ : End P)
    (hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x =
        (integralConstantToCompletionOfUniverses l E T).hom.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
                (ULift.up (Padic.coefficientExtensionUniformizer l E))) • x) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ) ≅
        DerivedCategory.Q.obj ((IntegralOnSlice.roos l E T none).obj P),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ c.hom =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P) := by
  classical
  obtain ⟨a, ha, hs, hu⟩ := integralPrincipalConeQuotientAugmentation l E T P hP μ hμ
  let : HasExactLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Mod l E T none) :=
    IntegralOnSlice.sliceProductsExact l E T none
  exact principalConeComparison μ ((IntegralOnSlice.tower l E T none).obj P)
    (fun n ↦ ((IntegralOnSlice.augmentation l E T none).app P).app (op n))
    (by
      apply CochainComplex.HomComplex.Cochain.ofHom_injective
      simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
        IntegralOnSlice.productAugmentation,
        CochainComplex.HomComplex.Cochain.ofHom_zero] using
        IntegralOnSlice.roosUnit_condition l E T none P)
    a ha hs hu

end WeilConjectures
