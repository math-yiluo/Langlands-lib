/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.WeilObject.BoundedConstructible.Defs
public import WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage

/-!
# The Weil object of a lisse `ℓ`-adic sheaf twisted by a scalar

Let `X₀` be a separated `k₀`-scheme of finite type, `H` a lisse `ℓ`-adic sheaf on `X₀` and
`b ∈ ℚ̄_ℓˣ`. Through the equivalence `AdicSheaf ℓ X₀ ≌ Mod_{ℚ̲̄_ℓ,X₀}`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), `H` placed in degree `0` is a bounded
constructible complex on `X₀`; with the structure automorphism `b` it is a Weil object of
`Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀`
(`AlgebraicGeometry.WeilComplex.weilObjectOfLisse`). It is the Weil object whose traces are
those of the Weil sheaf `p^* H ⊗ 𝓑_b` on `X₀ ⊗ k̄`.

## Main definitions

- `AlgebraicGeometry.ProEtale.isConstructibleModuleObject_of_isAdicLisseSheaf`: the module object
  of a lisse `ℓ`-adic sheaf is constructible.
- `AlgebraicGeometry.WeilComplex.weilObjectOfLisse`: the Weil object `(H, b)`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open ProEtale ProEtale.CondensedRing

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- The module object over `ℚ̲̄_ℓ,X` of a lisse `ℓ`-adic sheaf is constructible: pro-étale locally
it is a finite free module, by the compatibility of `AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}` with
pullbacks. -/
theorem isConstructibleModuleObject_of_isAdicLisseSheaf {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) :=
  hH.isLocallyFree.isConstructibleModuleObject

end ProEtale

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite

/-- A lisse `ℓ`-adic sheaf `H` on `X₀`, as an object of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` placed in degree `0`. -/
noncomputable def boundedConstructibleOfLisse {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    Dᵇc(X)⟦Profinite.padicAlgClRingObj l⟧ :=
  ⟨(_root_.DerivedCategory.singleFunctor _ 0).obj ((adicSheafEquivCondensedMod l X).functor.obj H),
    boundedConstructible_singleFunctor_obj _ X 0 _
      (isConstructibleModuleObject_of_isAdicLisseSheaf hH)⟩

/-- The multiplication by `b ∈ ℚ̄_ℓˣ` on `H` placed in degree `0`. -/
noncomputable def boundedConstructibleOfLisseSMulIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) :
    boundedConstructibleOfLisse hH ≅ boundedConstructibleOfLisse hH :=
  ObjectProperty.isoMk _ ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
    ((adicSheafEquivCondensedMod l X).functor.mapIso (WeilCoefficients.smulIso b H)))

/-- **The Weil object of a lisse sheaf twisted by a scalar**: a lisse `ℓ`-adic sheaf `H` on `X₀`,
placed in degree `0`, with the structure automorphism `b ∈ ℚ̄_ℓˣ`, as a Weil object of
`Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀`. -/
noncomputable def weilObjectOfLisse {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H)
    (b : (PadicAlgCl l)ˣ) :
    WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) X)).hom :=
  IsoAlgebra.mk (boundedConstructibleOfLisse hH)
    ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj.{u} l) l _).app _ ≪≫
      boundedConstructibleOfLisseSMulIso hH b)

end WeilComplex

end AlgebraicGeometry
