/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived

/-!
# The étale reading of `𝒪_E ⧸ ℓⁿ`-coefficients and pullback

Write `ρ_X : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)`, `M ↦ Rν_* Φ(M)`, for the étale reading
(`ProEtale.CondensedRing.finiteEtaleReading`). For a morphism `f : Z ⟶ Y` of separated
`k`-schemes of finite type, this file defines the canonical isomorphism
```
Lf^* ⋙ ρ_Z ≅ ρ_Y ⋙ Lf^*_{ét}
```
(`ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso`), composite of the compatibility of the
inclusion of bounded constructible complexes with `Lf^*`, of the finite-coefficient comparison
`Φ` with `Lf^*` (`ProEtale.leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`) and of
the inverse of the base change morphism `Lf^* Rν_* ⟶ Rν_* Lf^*`
(`ProEtale.rightDerivedComparisonBaseChange`), invertible on the objects of étale origin
`Φ(M)` (`ProEtale.isEtaleOrigin_of_isConstructible`).

Its compatibility with the pullback comparison of the étale reduction is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperStarReading`,
its compatibility with composition and with pullback squares in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperStarCoherence`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Iso

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The base change morphism `Lf^* Rν_* ⟶ Rν_* Lf^*` is invertible on the pro-étale complexes
`Φ(M)` read from bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes `M`, these being of étale
origin. -/
instance isIso_whiskerLeft_rightDerivedComparisonBaseChange (f : Z ⟶ Y) :
    IsIso (Functor.whiskerLeft ((boundedConstructible _).ι ⋙
        (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor)
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        f.left)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun M ↦ isIso_rightDerivedComparisonBaseChange_app _ f.left _
    (isEtaleOrigin_of_isConstructible _ M.property).plusEtaleOrigin

/-- **The étale reading commutes with pullback**: the canonical isomorphism
`Lf^* ⋙ ρ_Z ≅ ρ_Y ⋙ Lf^*_{ét}`, composite of the compatibility of the inclusion of bounded
constructible complexes with `Lf^*` (`boundedConstructibleUpperStarCompatibility`), of the
finite-coefficient comparison `Φ` with `Lf^*`
(`leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`) and of the inverse of the base
change morphism `Lf^* Rν_* ⟶ Rν_* Lf^*` (`rightDerivedComparisonBaseChange`), which is invertible
on the objects `Φ(M)` of étale origin. -/
noncomputable def finiteEtaleReadingUpperStarIso (f : Z ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f ⋙
        finiteEtaleReading ℓ E n Z ≅
      finiteEtaleReading ℓ E n Y ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left) :=
  Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility
      (Profinite.integersModPowRingObj ℓ E n) ℓ f)
      ((finiteCoefficientDerivedEquivalence Z.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(Z.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])) ≪≫
    Functor.isoWhiskerLeft (boundedConstructible _).ι (Functor.isoWhiskerRight
      (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f.left
        (PadicAlgCl.integersModPow ℓ E n)) _) ≪≫
    (asIso (Functor.whiskerLeft ((boundedConstructible _).ι ⋙
        (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor)
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        f.left))).symm

/-- The components of the inverse of `finiteEtaleReadingUpperStarIso`: the base change morphism
`Lf^* Rν_* ⟶ Rν_* Lf^*` at `Φ(M)`, followed by `Rν_*` of the inverses of the comparisons of `Φ`
and of the inclusion with `Lf^*`. -/
lemma finiteEtaleReadingUpperStarIso_inv_app (f : Z ⟶ Y)
    (M : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (finiteEtaleReadingUpperStarIso ℓ E n f).inv.app M =
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          f.left).app ((finiteCoefficientDerivedEquivalence Y.left
            (PadicAlgCl.integersModPow ℓ E n)).functor.obj M.obj) ≫
        R(ν_*(Z.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).map
          ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f.left
            (PadicAlgCl.integersModPow ℓ E n)).inv.app M.obj) ≫
        R(ν_*(Z.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).map
          ((finiteCoefficientDerivedEquivalence Z.left
            (PadicAlgCl.integersModPow ℓ E n)).functor.map
            ((boundedConstructibleUpperStarCompatibility
              (Profinite.integersModPowRingObj ℓ E n) ℓ f).inv.app M)) := by
  simp [finiteEtaleReadingUpperStarIso]

end Iso

end AlgebraicGeometry.ProEtale.CondensedRing
