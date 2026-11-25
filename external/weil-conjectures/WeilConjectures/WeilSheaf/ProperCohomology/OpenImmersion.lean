/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Universally closed open immersions of pro-étale Weil sheaves

For a universally closed open immersion `i`, the extension by zero `i_!` of pro-étale Weil
sheaves is the direct image `i_*`.

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.isIso_extensionByZeroToLowerStar`: `i_! ⟶ i_*` is an
  isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The base change `ī` of a universally closed open immersion `i` has clopen range. -/
lemma isClosed_range_geometricFiberMap (i : U ⟶ X) [IsOpenImmersion i] [UniversallyClosed i]
    [i.IsOver (Spec (CommRingCat.of k₀))] :
    IsClosed (Set.range (Scheme.Hom.geometricFiberMap i (comp_over i
      (Spec (CommRingCat.of k₀)))).base) :=
  have : UniversallyClosed (Scheme.Hom.geometricFiberMap i
      (comp_over i (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @UniversallyClosed) i
      (comp_over i (Spec (CommRingCat.of k₀))) inferInstance
  (Scheme.Hom.isClopen_range _).isClosed

/-- For a universally closed open immersion `i`, the comparison `i_! ⟶ i_*` of pro-étale Weil
sheaves is an isomorphism. -/
instance ProEtaleWeilSheaf.isIso_extensionByZeroToLowerStar (i : U ⟶ X) [IsOpenImmersion i]
    [UniversallyClosed i] [i.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i) := by
  have := isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range l _
    (isClosed_range_geometricFiberMap (k₀ := k₀) i)
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have : IsIso ((IsoAlgebra.forget _).map
      ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i).app K)) :=
    inferInstanceAs (IsIso ((adicOpenImmersionLowerShriekToLowerStar l
      (Scheme.Hom.geometricFiberMap i (comp_over i (Spec (CommRingCat.of k₀))))).app K.carrier))
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

attribute [local instance] Compactification.over

variable [Fact (ringChar k₀ ≠ l)]

instance (i : U ⟶ X) [IsOpenImmersion i] [UniversallyClosed i]
    [i.IsOver (Spec (CommRingCat.of k₀))] :
    (Scheme.Hom.geometricFiberMap i
      (comp_over i (Spec (CommRingCat.of k₀))))_!ᵃ[l].PreservesKInjectiveComplexes :=
  have := isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range l _
    (isClosed_range_geometricFiberMap (k₀ := k₀) i)
  Functor.preservesKInjectiveComplexes_of_iso
    (asIso (adicOpenImmersionLowerShriekToLowerStar l _)).symm

end AlgebraicGeometry
