/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement

/-!
# Integral constructible complexes with uniformly finite Tor amplitude

Source: Stacks Project, Cohomology on Sites, Tag 08G2, part (2), applied to each
reduction; Weil blueprint, integral-stage paragraph of `definition-constructible-sheaves`
(blueprint: lem-weil-integral-ctf-triangulated).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem torAmplitude_iso
    (Y : AlgebraicGeometry.Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  rintro N P ⟨q⟩ f hf hP M i hi
  exact h.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

end WeilConjectures
