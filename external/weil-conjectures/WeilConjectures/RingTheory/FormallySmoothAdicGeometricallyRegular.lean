/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularTensorProductOfFormallySmoothAdic

/-!
# Geometric regularity from maximal-ideal-adic formal smoothness

Source: Stacks Project, More on Algebra, Theorem Tag 07EL, implication (2) to (1)
(blueprint: lem-weil-pbc-fs-adic-field-geometrically-regular).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A Noetherian local algebra over a field which is formally smooth for its maximal-ideal-adic
 topology is geometrically regular. Source: Stacks Project, More on Algebra, Theorem Tag 07EL,
 implication (2) to (1) (blueprint: lem-weil-pbc-fs-adic-field-geometrically-regular).

Proof plan:
1. For any finite purely inseparable extension `k₁/k`, set `D = C ⊗[k] k₁` and
   `I = m D`. The ring `D` is Noetherian local with maximal ideal `n` containing `I`, by
   lem-weil-pbc-purely-inseparable-base-change-local-ring. This includes `k₁ = k`.
2. By lem-weil-pbc-fs-adic-base-change, `D` is formally smooth over `k₁` for the `I`-adic
   topology.
3. In theorem-finite-etale-covers-proper-henselian--2, any test map killing `n ^ q` kills `I ^ q`,
because
   `I ≤ n`. The `I`-adic lifting property therefore gives the required lift for the `n`-adic
   lifting property. Its image of `n ^ q` lies in the square-zero ideal `J`, so the lift
   kills `n ^ (2 * q)` and is continuous as well.
4. Apply lem-weil-pbc-fs-adic-field-regular-local (Stacks Tag 07EI) to obtain regular locality
   of `D`. By lem-weil-pbc-regular-local-localization, every prime localization is regular
   local, so `D` is regular.
5. The factor swap `C ⊗[k] k₁ ≃+* k₁ ⊗[k] C`, constructed using
   lem-weil-pbc-algebra-tensor-pushout-universal-property, preserves regularity: it identifies
   primes and their localizations, dimensions and maximal-ideal generator numbers. Thus every
   finite purely inseparable base change is regular, as in
   theorem-finite-etale-covers-proper-henselian--2 and def-weil-regular-scheme. In characteristic
   zero the purely inseparable extension has degree one
   (def-weil-pbc-finite-purely-inseparable-extension), so the same argument applies. -/
theorem isGeometricallyRegular_of_formallySmoothAdic (k : Type u) (C : Type v)
    [Field k] [CommRing C] [Algebra k C] [IsNoetherianRing C] [IsLocalRing C]
    (h : FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)) :
    IsGeometricallyRegular k C := by
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  exact isRegularRing_tensorProduct_of_formallySmoothAdic k C k' h

end Algebra
