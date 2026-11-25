/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteReadingWeil
public import WeilConjectures.WeilSheaf.SmoothPurityReductionWeilStep
public import WeilConjectures.WeilSheaf.SmoothPurityWeilIsoTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction

/-! # Étale reading of the Weil data on the integral reductions -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The geometric Weil datum on bounded constructible reduction, transported through
the actual comparison with ambient derived coefficient extension. -/
noncomputable def purityReducedBoundedWeilDatum (g : X.left ⟶ X.left)
    {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (φ : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K.obj ⟶ K.obj) :=
  purityConjugateWeilDatum (purityFiniteGeometricPullback (ℓ := ℓ) (E := E) g n)
    ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app K)
    (transportWeilDatum (purityIntegralReduction X.left ℓ E n)
      (integersModPowReductionUpperStarIso ℓ E n g) φ)

/-- The finite étale datum obtained from an integral geometric datum by coefficient
reduction and the canonical étale reading. -/
noncomputable def purityEtaleReducedWeilDatum (g : X.left ⟶ X.left)
    {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (φ : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K.obj ⟶ K.obj) :=
  purityFiniteReadWeilDatum ℓ E n X g
    (purityReducedBoundedWeilDatum ℓ E n X g φ)

/-- Equivariance for the specified integral data after the actual finite étale reduction. -/
def PurityEtaleReducedWeilCondition (g : X.left ⟶ X.left)
    {K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (φK : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K.obj ⟶ K.obj)
    (φL : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj L.obj ⟶ L.obj)
    (s : (etaleReduction ℓ E n X).obj K ⟶ (etaleReduction ℓ E n X).obj L) : Prop :=
  IsWeilEquivariant
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g)
    (purityEtaleReducedWeilDatum ℓ E n X g φK)
    (purityEtaleReducedWeilDatum ℓ E n X g φL) s

/-- An equivariant finite étale isomorphism for the actual reduced data gives an
equivariant isomorphism between the ambient derived reductions. -/
theorem exists_equivariant_derivedReduction_iso_of_etale
    (g : X.left ⟶ X.left)
    (K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (φK : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K.obj ⟶ K.obj)
    (φL : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj L.obj ⟶ L.obj)
    (hne : ∃ e : (etaleReduction ℓ E n X).obj K ≅ (etaleReduction ℓ E n X).obj L,
      IsWeilEquivariant
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g)
        (purityEtaleReducedWeilDatum ℓ E n X g φK)
        (purityEtaleReducedWeilDatum ℓ E n X g φL) e.hom) :
    ∃ e : (purityIntegralReduction X.left ℓ E n).obj K.obj ≅
        (purityIntegralReduction X.left ℓ E n).obj L.obj,
      PurityGeometricReductionWeilCondition g φK φL n e.hom := by
  let red := boundedConstructibleIntegersModPowReduction X.left ℓ E n
  obtain ⟨e, he⟩ := exists_finite_equivariant_iso_of_etale_reading ℓ E n X g
    (red.obj K) (red.obj L)
    (purityReducedBoundedWeilDatum ℓ E n X g φK)
    (purityReducedBoundedWeilDatum ℓ E n X g φL) hne
  let a := (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app K
  let b := (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app L
  refine ⟨a.symm ≪≫ e ≪≫ b, ?_⟩
  exact purity_isWeilEquivariant_iso_transport
    (purityFiniteGeometricPullback (ℓ := ℓ) (E := E) g n) a b _ _ e he

end AlgebraicGeometry.ProEtale.CondensedRing
