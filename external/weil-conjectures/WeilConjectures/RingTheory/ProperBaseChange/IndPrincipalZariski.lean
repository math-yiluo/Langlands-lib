/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-! # Ind-etale, principal ind-Zariski, and weakly etale algebras

Source: blueprint, proper base change, definition of ind-etale and ind-Zariski algebras
(blueprint: definition-ind-etale-pro-etale-weakly).

## Main definitions

- `Algebra.IsIndPrincipalZariski`: the blueprint's filtered-colimit definition with terms
  finite products of principal localizations. Upstream `Algebra.IndZariski` instead allows
  arbitrary local isomorphisms as terms, so it does not express this clause verbatim.
- Ind-etale means the existing `Algebra.IndEtale`. Its stages are `Algebra.Etale`, which
  includes finite presentation.
- The corresponding affine inverse-limit description is the existing
  `AlgebraicGeometry.proAffineEtale_Spec_iff`, with affine terms and hence affine transitions.
- Weakly etale means the existing `Algebra.WeaklyEtale`: flatness over the base and flatness
  of tensor multiplication. The equivalence with weak etaleness of the spectrum map is
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- An `A`-algebra `B` is ind-Zariski in the blueprint's principal-localization sense if it
is a filtered colimit of finite products of algebras `A_f`. The empty finite product is
allowed. Source: blueprint, proper base change, definition of ind-etale and ind-Zariski
algebras (blueprint: definition-ind-etale-pro-etale-weakly). -/
def IsIndPrincipalZariski (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
    (P : ColimitPresentation I (CommAlgCat.of A B)),
    ∀ i : I, ∃ (n : ℕ) (f : Fin n → A),
      Nonempty (P.diag.obj i ≃ₐ[A] ((j : Fin n) → Localization.Away (f j)))

end Algebra
