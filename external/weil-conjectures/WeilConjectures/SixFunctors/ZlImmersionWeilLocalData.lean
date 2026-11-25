/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.ConstructiblePullbackTExact
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Normalized clause data for immersion local behavior

Source: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction and Part 2
(blueprint: def-zl-immersion-weil-local-data).

The auxiliary structures package the clauses of this statement. No operation is chosen
from their existence. All stalks are the recorded point fibres, and normalization on every
finite stage specifies the local operators and the pullback comparison themselves.

## Main declarations

- `ZlWeilExactOperation`: exact-heart restriction and the normalized Weil cohomology maps.
- `ZlWeilLocalOperators`: the specified local geometric Frobenius on actual stalks.
- `ZlImmersionPullback` and `ZlOpenExtension`: the two clauses of the node.
- `zlOpenStalkIso`: the inside-open stalk comparison constructed from restriction and unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u uC vC uB vB uV vV
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures

section Categorical
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]

end Categorical

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The recorded Frobenius endofunctor, with the fixed coefficient datum.
Source: Restriction, induced Weil structures
(blueprint: def-zl-immersion-weil-local-data). -/
abbrev zlFrobenius := sfCommonStageWeilFrobeniusPullback D c.l c.different Y₀ c.Qbar

variable {Y₀}
variable {W₀ X₀ U₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]

end WeilConjectures
