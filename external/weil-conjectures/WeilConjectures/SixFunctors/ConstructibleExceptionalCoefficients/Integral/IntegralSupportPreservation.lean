/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/-- Integral compact support preserves the finite-Tor constructible subcategory.
Source: Zheng, Construction 5.25 and Propositions 5.24 and 5.26;
coefficient construction step 3.
Proof: extend by zero and proper direct image on normalized finite systems, then transport
constructibility and a common Tor interval through strict evaluation and derived completion.
(blueprint: lem-sf-integral-support-preservation). -/
theorem integral_support_preservation (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l) :
    ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
      finiteTorConstructibleIntegral l E.carrier Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj
          K.obj) := by
  intro K
  let hu : IsUnit (l : D.k) := PurCompactSupport.coefficientPrimeUnit l D _hl
  letI : ∀ x : X, Invertible (l : X.residueField x) :=
    fun x ↦ (map_natCast ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) l) ▸
      ((PurCompactSupport.coefficientPrimeUnit l D _hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  letI : ∀ y : Y, Invertible (l : Y.residueField y) :=
    fun y ↦ (map_natCast ((Y ↘ Spec (.of D.k)).residueFieldAlgebraMap y) l) ▸
      ((PurCompactSupport.coefficientPrimeUnit l D _hl).map
        ((Y ↘ Spec (.of D.k)).residueFieldAlgebraMap y)).invertible
  let hX : sfIntegralConstructible l E.carrier X =
      finiteTorConstructibleIntegral l E.carrier X :=
    (integral_residue_tor D l _hl E.carrier X).2
  let hY : sfIntegralConstructible l E.carrier Y =
      finiteTorConstructibleIntegral l E.carrier Y :=
    (integral_residue_tor D l _hl E.carrier Y).2
  have hK : sfIntegralConstructible l E.carrier X K.obj := by
    rw [hX]
    exact K.property
  let K' : sfIntegralConstructibleCategory l E.carrier X := ⟨K.obj, hK⟩
  have hs : sfIntegralConstructible l E.carrier Y
      ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj K.obj) := by
    exact (sfIntegralConstructible l E.carrier Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E.carrier D.k hu c).app K').symm
      ((sfCompactSupportFiniteIntegralFunctor l D.k hu c E.carrier).obj K').property
  have torY (M : DerivedCategory (scalarReductionSource.{u, u} l E.carrier Y))
      (hM : sfIntegralConstructible l E.carrier Y M) :
      finiteTorConstructibleIntegral l E.carrier Y M := by
    rw [← hY]
    exact hM
  exact torY _ hs

end WeilConjectures.ConstructibleExceptionalCoefficients
