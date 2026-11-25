/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginUpperStar

/-!
# Module complexes of étale origin with finite coefficients

Let `T` be a finite discrete commutative ring, `Λ = C(-, T)` and
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` the comparison of `D(Mod_{Λ_X})` with the
derived category of pro-étale sheaves of `T`-modules. We say informally that `C ∈ D(Mod_{Λ_X})`
is *bounded below of étale origin* if `Φ C` is (`ProEtale.DerivedCategory.plusEtaleOrigin`).

* This is stable under derived pullback
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj`).
* Bounded constructible complexes with coefficients `𝒪_E/ℓⁿ` on schemes over a field are of étale
  origin (`ProEtale.CondensedRing.plusEtaleOrigin_of_boundedConstructible_integersModPow`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}}

/-- **Derived pullbacks preserve module complexes of étale origin**: if `Φ C` is bounded below of
étale origin, so is `Φ (Lf^* C)`. -/
lemma plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj (f : Y ⟶ X)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y
      ((finiteCoefficientDerivedEquivalence Y T).functor.obj
        (L(CondensedRing.upperStar (Profinite.continuousMapRingObj T) f).obj C)) :=
  ObjectProperty.prop_of_iso _
    ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T).app C).symm
    (hC.leftDerivedUpperStar_obj f)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- **Bounded constructible complexes with coefficients `𝒪_E/ℓⁿ` are of étale origin**, on a
scheme over a field (`ProEtale.CondensedRing.etaleOriginReading`). -/
lemma plusEtaleOrigin_of_boundedConstructible_integersModPow (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
    (X : Over (Spec (.of k))) (M : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X.left
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        M.obj) :=
  (etaleOriginReading ℓ E n X M).plusEtaleOrigin

end AlgebraicGeometry.ProEtale.CondensedRing
