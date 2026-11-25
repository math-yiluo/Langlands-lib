/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The forgetful functor and the operations on Weil complexes

The operations on Weil complexes are lifts of the operations on the derived categories of
pro-étale `ℚ̄_ℓ`-sheaves on the geometric fibers: the Weil structure of the result is obtained
from that of the input by the exchange isomorphisms with the Frobenius pullbacks. This file
records that forgetting the Weil structure (`AlgebraicGeometry.WeilComplex.forget`) commutes
with the lifted operations.

## Main definitions

- `AlgebraicGeometry.WeilComplex.upperStarCompForgetIso` (`sec-Weil-complexes`): the
  forgetful functor commutes with the pullback `φ^*` of Weil complexes,
  `For ∘ φ^* ≅ φ̄^* ∘ For`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_forget_iso`
  (`sec-Weil-complexes`): the forgetful functor commutes with the derived pushforward
  `Rφ_*` of Weil complexes, `For ∘ Rφ_* ≅ Rφ̄_* ∘ For`.

## Implementation notes

Blueprint `sec-Weil-complexes` lifts `Lf^*`, `Rf_*`, `Rf_!`, `⊗ᴸ`, `RHom` and `Rf^!` to Weil
complexes, compatibly with the forgetful functor, and asserts that the composition, base
change, projection, purity and duality isomorphisms are morphisms of Weil complexes. The Weil
complexes of the repository (`AlgebraicGeometry.WeilComplex`) carry the lifts of `φ^*`
(`AlgebraicGeometry.WeilComplex.upperStar`), of `Rφ_*`
(`AlgebraicGeometry.WeilComplex.derivedLowerStar`) and of `Rf_!`
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`); this file covers their compatibility with
the forgetful functor for `φ^*` and `Rφ_*`. The lifts of `⊗ᴸ`, `RHom` and `Rf^!`, and the
equivariance of the comparison isomorphisms, need operations on Weil complexes that the
repository does not have yet.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- Blueprint `sec-Weil-complexes`: Six operations on Weil complexes.

The forgetful functor commutes with the pullback of Weil complexes: `For(φ^* K) ≅ φ̄^* For(K)`,
where `φ̄ : X̄ ⟶ Ȳ` is the base change of `φ` to the geometric fibers. The pullback of a
pro-étale Weil sheaf has underlying sheaf the pullback of the underlying sheaf, so this is the
composition isomorphism of the functors induced on derived categories by the exact functors
`φ^*` and `For`. -/
noncomputable def upperStarCompForgetIso :
    upperStar (k₀ := k₀) (l := l) φ ⋙ forget ≅
      forget ⋙
        D((Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l]) :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
    ((Functor.mapDerivedCategoryCompIso (ProEtaleWeilSheaf.upperStar k₀ l φ)
        (IsoAlgebra.forget _)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (Iso.refl (ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ IsoAlgebra.forget _) :
          ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ IsoAlgebra.forget _ ≅
            IsoAlgebra.forget _ ⋙
              (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l]) ≪≫
      (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget _)
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l])).symm)

/-- Blueprint `sec-Weil-complexes`: Six operations on Weil complexes.

The forgetful functor commutes with the derived pushforward of Weil complexes:
`For(Rφ_* K) ≅ Rφ̄_* For(K)`, where `φ̄ : X̄ ⟶ Ȳ` is the base change of `φ` to the geometric
fibers. The forgetful functor from pro-étale Weil sheaves has an exact left adjoint, the
induction `F ↦ ⨁ₙ (Frⁿ)^* F`, so it preserves K-injective complexes, and it commutes with the
underived pushforward. -/
theorem nonempty_derivedLowerStar_comp_forget_iso [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerStar (k₀ := k₀) (l := l) φ ⋙ forget ≅
      forget ⋙
        R(((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l]))) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact ⟨Functor.isoWhiskerLeft (ObjectProperty.ι _)
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _)⟩

end WeilComplex

end AlgebraicGeometry
