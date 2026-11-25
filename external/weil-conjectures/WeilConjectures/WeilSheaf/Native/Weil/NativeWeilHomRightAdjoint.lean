/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilHomClosedStructure

/-! # Pointwise left adjoints of native derived internal Hom

Source: native tensor lift, adjoint-construction step; Stacks Tags 06YS and 08J9.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Every fixed-source native derived internal Hom has a left adjoint. This
pointwise assertion does not construct a tensor bifunctor or any comparison
with ordinary tensor.

Source: prose-10-20, internal-Hom/transposition paragraph;
native tensor lift step 1; Stacks Tags 06YS, 08J9 and 0A97
(blueprint: lem-sf-native-weil-hom-right-adjoint).

Proof: use the Frobenius ringed action-site realization and its additive
module equivalence. For a fixed native derived object K, choose a K-flat
flat-term representative on that site. Total relative tensor with this
representative takes quasi-isomorphisms to quasi-isomorphisms, so it descends
to a functor on the native derived category. Tensor-Hom adjunction on complexes
identifies maps from this tensor into a K-injective I with maps into the
product-total internal Hom from the representative of K to I. Under the
module equivalence this is the native product-total Hom: the componentwise
native-to-standard row-sign conversion intertwines the differentials and
both complex-variable maps. The model and naturality fields of
M.weilRepresentatives identify the resulting right adjoint with
M.weilHom(K,-), first on K-injective targets and then on all targets through
the K-injective localization equivalence. Transport the adjunction across
this natural isomorphism. These are unbounded resolutions. The zero source
and the empty scheme satisfy the same universal properties; no boundedness,
constructibility or nonzero-object assumption enters. -/
theorem native_weil_hom_isRightAdjoint
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (Prod.sectR (op K) _ ⋙ M.weilHom).IsRightAdjoint := by
  obtain ⟨S⟩ := native_weil_hom_closed_structure k₀ l X M
  let _ := S.monoidal
  exact (S.adjunction K).isRightAdjoint

end AlgebraicGeometry.ProEtaleWeilSheaf
