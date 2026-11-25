/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarMateInvertible
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso

/-! # Localization of the normalized integral scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

attribute [local irreducible] IntegralComponent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend the invertible integral scalar morphism to the actual raw rational stage.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; localization universal
property, applied to steps 3--8 of the native finite-comparison plan.
(blueprint: lem-sf-native-compact-support-integral-localization).

Proof: use the integral natural morphism and its two invertible outer factors.
The actual middle scalar mate is invertible by its coefficient-change theorem.
The derived section equivalence reflects these component isomorphisms. Residue Tor
identifies every integral constructible input with a finite-Tor input, so the integral
natural morphism is a natural isomorphism on the entire integral category. Apply the
existing raw scalar-localization natural-isomorphism theorem, using the integral
linear shift instances. Its component equation preserves the six-arrow normalization
by equality transport. No field-transition coherence is asserted or used here. -/
theorem native_compact_support_integral_localization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hchange : ∀ (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E)
        (embedding l E)), (change E).map T = C.integralMap l T)
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : Index l (PadicAlgCl l)) :
    ∃ alpha : finiteSource l D hl P c target stage E ≅ finiteTarget l c source E,
      ∀ K : finiteTorConstructibleIntegralCategory l
          (Coefficient.{u} l (PadicAlgCl l) E) X,
        IntegralComponent l D hl P c source target change E K
          (alpha.hom.app
            ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)) := by
  obtain ⟨tau, htau⟩ := native_integral_scalar_morphism l D hl P c
    source target stage change (fun E ↦ hchange E X (source.coefficient E))
      (fun E ↦ hchange E Y (target.coefficient E)) E
  have htor := (integral_residue_tor D l hl
    (Coefficient.{u} l (PadicAlgCl l) E) X).2
  have htauIso (K : sfIntegralConstructibleCategory l
      (Coefficient.{u} l (PadicAlgCl l) E) X) : IsIso (tau.app K) := by
    let K' : finiteTorConstructibleIntegralCategory l
        (Coefficient.{u} l (PadicAlgCl l) E) X :=
      ⟨K.obj, by rw [← htor]; exact K.property⟩
    obtain ⟨⟨b, d, hfac⟩, _⟩ := htau K'
    have hscalar : IsIso ((PurCompactSupport.comparison (change E) c).app K'.obj) :=
      native_compact_support_scalar_mate_invertible l D hl c E
        (change E) (hchange E) K'
    have : IsIso ((sections l Y).mapDerivedCategory.map (tau.app K)) := by
      change IsIso ((sections l Y).mapDerivedCategory.map
        (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K')))
      rw [hfac]
      let e := b ≪≫ (@asIso _ _ _ _
        ((PurCompactSupport.comparison (change E) c).app K'.obj) hscalar) ≪≫ d
      change IsIso e.hom
      infer_instance
    exact isIso_of_reflects_iso (tau.app K) (sections l Y).mapDerivedCategory
  let integralIso : sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X ⋙ finiteSource l D hl P c target stage E ≅
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteTarget l c source E :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (tau.app K) (htauIso K))
      (fun f ↦ tau.naturality f)
  obtain ⟨alpha, halpha, _⟩ := @ScalarLocalization.naturalIso_of_integral
    (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E)) _
    (sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    _ _ _ _ _ (fun n ↦ inferInstance) _ _
    (fun n ↦ sfIntegralConstructibleShift_linear l
      (Coefficient.{u} l (PadicAlgCl l) E) X n)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E)) _ _
    (finiteSource l D hl P c target stage E) (finiteTarget l c source E) integralIso
  refine ⟨alpha, ?_⟩
  intro K
  change IntegralComponent l D hl P c source target change E K
    (alpha.hom.app ((sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj
        ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)))
  have hcomponent : alpha.hom.app
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj
          ((PurCompactSupport.finiteTorIntegralInclusion l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) =
      tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) :=
    halpha ((PurCompactSupport.finiteTorIntegralInclusion l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
  exact hcomponent.symm ▸ (htau K).2

end WeilConjectures.LocallyFiniteAdicCompactSupport
