/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorCoordinateMap

/-! # Components of the two-term free Hom--tensor exchange

Source: the finite-free calculation in the first paragraph of blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 0A8X and 08J7.
(blueprint: lem-sf-two-term-free-hom-tensor-components).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

/-- A chain map with the signed evaluation formula is invertible in every degree
when its coefficient complex has precisely two free rank-one terms.
Neither Hom input is bounded, and no condition is imposed on the differential of Q.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1,
finite-free coefficient construction; Stacks Tags 0A8X and 08J7.
(blueprint: lem-sf-two-term-free-hom-tensor-components).

Proof: fix total degree j. Delete zero summands outside coefficient degrees -1,0.
The source is the biproduct of Hom(P,I)^(j+1) tensor Q^(-1) and
Hom(P,I)^j tensor Q^0. The given identifications of the two terms of Q with
R identify these summands with the two indicated Hom degrees. For each source
index p, the target I tensor Q in degree p+j is the biproduct of I^(p+j+1)
and I^(p+j). Internal Hom from P^p preserves this finite product. Its product
over all p commutes with the two-factor product, by the product universal
property, without any finiteness assumption on P. The resulting component
isomorphism multiplies the -1 coordinate at source index p by (-1)^p and
leaves the zero coordinate fixed. Applying that sign twice gives the identity.
The formula IsSignedHomTensor identifies f with this isomorphism: test on
local pure tensors, then on all restrictions and all local sections of P^p.
The sheafified tensor universal property and the Hom product projections
imply equality. This works over the zero sheaf and on the empty site as well. -/
theorem twoTermFreeHomTensor_component_isIso
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (f : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (j : ℤ) : IsIso (f.f j) := by
  obtain ⟨g, hg, hformula⟩ :=
    twoTermFreeHomTensor_coordinate_exists Y R P I Q hzero eNeg eZero j
  have hfg := twoTermFreeHomTensor_coordinate_unique Y R P I Q hzero eNeg eZero f g hf j hformula
  rw [hfg]
  exact hg

end WeilConjectures.IntegralHom
