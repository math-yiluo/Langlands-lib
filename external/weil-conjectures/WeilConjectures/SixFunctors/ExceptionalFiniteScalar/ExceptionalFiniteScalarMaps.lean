/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsCore
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsEtale

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The normalized scalar mates exist once the finite operation and scalar packages exist.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps).

The statement packages the canonical proper/open comparison, its counit transpose,
the two shift compatibilities, and the ordinary-etale mate data.  It is strictly
smaller than `Construction`, since the scalar and operation packages are inputs.

Proof in words.  `X`, `Y` are of finite type over `k`, hence Noetherian, and `f` is separated
of finite type, so the etale compact scalar coherence theorem makes the ordinary
`Etale.compactScalarMap a c` (proper coefficient comparison at `j_!`, followed by the open
scalar balancing map) invertible; this is `q` of `EtaleMates`, and `b` is its mate under the
two etale exceptional adjunctions, with the projection data of the constant-coefficient
exceptional tensor theorem (steps 3--5 of the item).  Transport `q` to the finite-Tor
categories through the operations' realizations `left` and the equality realizations of the
scalar packages: since `ι` is fully faithful, `q_normalized` defines `q` and `leftScalarMap`
is invertible on these objects.  Define `b` as the `target.adjunction`-transpose of
`scalarY.functor.map ε_A ∘ q⁻¹`; the counit equation is the transpose identity, and `b` is
invertible because its realization is the etale `b` up to the site comparisons (steps 6--7).
The shift equations follow from the shift compatibility of the proper and open maps and the
uniqueness of adjoint shifts (step 8).  Uses: lem-asd-proper-finite-coefficient-extension,
lem-pur-etale-compact-scalar-coherence, theorem-existence-exceptional-inverse-image--1.
-/
theorem finiteScalarMaps_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) :
    Nonempty (ConstructionMaps l E L n m a c scalarX scalarY source target) := by
  obtain ⟨core⟩ :=
    finiteScalarMapsCore_exists D l _hl E L n m a f c scalarX scalarY source target
  obtain ⟨etale⟩ := finiteScalarMapsEtale_exists D l _hl E L n m a f c
  exact ⟨{
    q := core.q
    b := core.b
    q_normalized := core.q_normalized
    counit := core.counit
    qShift := core.qShift
    bShift := core.bShift
    etale := etale
  }⟩

end WeilConjectures.ExceptionalFiniteScalar
