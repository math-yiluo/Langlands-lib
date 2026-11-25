/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage
public import WeilConjectures.ZetaFunction.WeilSheafObjectComparisonLisse

/-!
# Weil sheaves have the traces of Weil objects

A Weil sheaf `G` on a separated `k₀`-scheme `X₀` of finite type, placed in degree `0`, has the
traces of a Weil object of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀`, through the canonical
identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`
(`ProEtale.CondensedRing.endTensorUnitRingEquiv`); see
`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex`. By the dévissage of
`WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage` the same then holds for every Weil
complex (`AlgebraicGeometry.WeilSheaf.exists_hasWeilObjectComparison`).

## The comparison

`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex` compares the Weil sheaves of the
zeta-function chapter, `ℓ`-adic sheaves on the pro-étale site of the geometric fiber `X₀ ⊗ k̄`
with a Frobenius structure, with the Weil objects of the trace formula chapter, condensed
`ℚ̲̄_ℓ`-modules on the pro-étale site of `X₀` with an automorphism. Since the Weil objects satisfy
the trace formula `ProEtale.CondensedRing.weilTraceFormula`, its global clause is, given the local
one, the Grothendieck–Lefschetz formula for `G`. It is proved in
`WeilConjectures.ZetaFunction.WeilSheafObjectComparisonLisse`:
* by Noetherian induction the traces reduce to irreducible lisse Weil sheaves on smooth strata,
  which by Deligne (Weil II, 1.3.14) are twists `p^* H ⊗ 𝓑_b` of pullbacks of lisse `ℓ`-adic
  sheaves `H` on the stratum by a character `b^{deg}` of `W(k̄/k₀)`; the twist becomes the
  automorphism `b` of the Weil object `(H, b)`;
* the two sheaf theories are compared along the pullback `X₀ ⊗ k̄ ⟶ X₀`, with their stalks and
  their direct images with compact support.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

open ProEtale.CondensedRing in
/-- **Weil sheaves have the traces of Weil objects of `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`**: every Weil
sheaf placed in degree `0` has, through the canonical identification
`End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the compactly supported Frobenius traces and the trace function
of a Weil object for the identity of `X₀`
(`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`).

The Weil object is not a descent of the Weil sheaf, which need not exist: by Deligne (Weil II,
1.3.14) every irreducible Weil sheaf is the twist of an étale sheaf on `X₀` by a character of
`W(k̄/k₀)`, which becomes the automorphism of the Weil object, and the traces only depend on the
semisimplification. -/
theorem hasWeilObjectComparison_toComplex (G : WeilSheaf k₀ l X) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom (toComplex.obj G) :=
  hasWeilObjectComparison_toComplex_of_irreducibleLisse G

open ProEtale.CondensedRing MonoidalCategory in
/-- There is an additive map `ι : End (𝟙_ Mod_{Spec k̄}) ⟶ ℚ̄_ℓ`, the canonical identification,
along which every Weil sheaf placed in degree `0` has the traces of a Weil object. -/
theorem exists_hasWeilObjectComparison :
    ∃ ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l,
      ∀ G : WeilSheaf k₀ l X, WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) :=
  ⟨_, hasWeilObjectComparison_toComplex⟩

end AlgebraicGeometry.WeilSheaf
