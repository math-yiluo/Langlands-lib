/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientWeilReduction
public import WeilConjectures.WeilSheaf.SmoothPurityEquivariantLift

/-! # Ordinary reduction preserves the transported Weil equation -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The geometric pullback on a finite coefficient category. This named functor avoids
reconstructing its derived tensor-category instances at each specialization. -/
noncomputable def purityFiniteGeometricPullback (g : X ⟶ X) (n : ℕ) :=
  L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧)

/-- The Weil equation at a finite geometric reduction. Naming it keeps applications
from repeatedly elaborating the geometric and coefficient derived functors. -/
def PurityGeometricReductionWeilCondition (g : X ⟶ X)
    {K M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (φK : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K ⟶ K)
    (φM : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj M ⟶ M) (n : ℕ)
    (s : (purityIntegralReduction X ℓ E n).obj K ⟶
      (purityIntegralReduction X ℓ E n).obj M) : Prop :=
  IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧)
    (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E n g) φK)
    (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E n g) φM) s

/-- The actual transition between two finite reductions preserves equivariance for the
actual geometric pullback/reduction comparisons. The scheme endomorphism need not be
linear over a chosen base field. -/
theorem isWeilEquivariant_derivedReductionStep (g : X ⟶ X) (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (φK : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K ⟶ K)
    (φL : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj L ⟶ L)
    (s : (purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
      (purityIntegralReduction X ℓ E (n + 1)).obj L)
    (hs : IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E (n + 1)⟧)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E (n + 1) g) φK)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E (n + 1) g) φL) s) :
    IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E n g) φK)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E n g) φL)
      (derivedReductionStep n s) := by
  exact isWeilEquivariant_coefficientReduction
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E (n + 1))
    (Profinite.integersModPowRingObjTransition ℓ E n)
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g
    (Profinite.padicIntegersRingObjToIntegersModPow_comp_integersModPowRingObjTransition ℓ E n)
    φK φL s hs

end AlgebraicGeometry.ProEtale
