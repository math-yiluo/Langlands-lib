/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-! # Finite étale reading along semilinear scheme maps

Geometric Galois Frobenius is a scheme automorphism which is semilinear over the algebraic
closure. The pullback and reading comparisons here therefore take arbitrary scheme maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Bounded constructible pullback at arbitrary condensed coefficients, without requiring
linearity over a chosen ground field. -/
noncomputable def purityBoundedConstructiblePullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory ⥤
      (boundedConstructible (condensedRingObj Λ X)).FullSubcategory :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((g)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ g K.obj K.property

/-- The comparison with the ambient geometric pullback is the identity on complexes. -/
noncomputable def purityBoundedConstructiblePullbackForgetIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    purityBoundedConstructiblePullback Λ g ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((g)^*⟦Λ⟧) := Iso.refl _

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The canonical finite reading comparison works for a semilinear map as well: étale
origin makes the comparison-site base change invertible on every constructible complex. -/
noncomputable def purityFiniteEtaleReadingUpperStarIso (g : X.left ⟶ Y.left) :
    purityBoundedConstructiblePullback (Profinite.integersModPowRingObj ℓ E n) g ⋙
        finiteEtaleReading ℓ E n X ≅
      finiteEtaleReading ℓ E n Y ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g) := by
  have h : IsIso (Functor.whiskerLeft ((boundedConstructible _).ι ⋙
      (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor)
    (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
      g)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun M ↦ isIso_rightDerivedComparisonBaseChange_app _ g _
      (isEtaleOrigin_of_isConstructible _ M.property).plusEtaleOrigin
  exact Functor.isoWhiskerRight (purityBoundedConstructiblePullbackForgetIso _ g)
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])) ≪≫
    Functor.isoWhiskerLeft (boundedConstructible _).ι (Functor.isoWhiskerRight
      (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso g
        (PadicAlgCl.integersModPow ℓ E n)) _) ≪≫
    (asIso (Functor.whiskerLeft ((boundedConstructible _).ι ⋙
        (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor)
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        g))).symm

end AlgebraicGeometry.ProEtale.CondensedRing
