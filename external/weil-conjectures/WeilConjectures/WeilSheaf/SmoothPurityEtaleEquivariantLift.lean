/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReductionReadingWeil
public import WeilConjectures.WeilSheaf.SmoothPurityGeometricEquivariantLift

/-! # Integral purity from finite étale equivariant orientations

This is the comparison interface: finite étale orientations for the actual reductions
of the given integral Weil data suffice. No coefficient compatibility of chosen finite
orientations, finiteness assumptions, or reduction-step assumptions are required.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

set_option hygiene false in
local notation "𝐓" => (shiftFunctor _ (2 * d : ℤ)).obj
  (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)
set_option hygiene false in
local notation "𝐖" => (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)

/-- Finite étale equivariant orientations lift to an integral equivariant orientation
for any geometric endomorphism, including semilinear Frobenius. -/
theorem exists_equivariant_integralOrientation_iso_of_etale_reductions
    (g : X.left ⟶ X.left)
    (φT : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj 𝐓.obj ≅ 𝐓.obj)
    (φW : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj 𝐖.obj ⟶ 𝐖.obj)
    (hne : ∀ n : ℕ, ∃ e : (etaleReduction ℓ E.1 (n + 1) X).obj 𝐓 ≅
        (etaleReduction ℓ E.1 (n + 1) X).obj 𝐖,
      PurityEtaleReducedWeilCondition ℓ E.1 (n + 1) X g φT.hom φW e.hom) :
    ∃ e : 𝐓 ≅ 𝐖,
      IsWeilEquivariant L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧) φT.hom φW e.hom.hom := by
  apply exists_geometric_equivariant_integralOrientation_iso ℓ E f d g φT φW
  intro n
  exact exists_equivariant_derivedReduction_iso_of_etale ℓ E.1 (n + 1) X g
    𝐓 𝐖 φT.hom φW (hne n)

end AlgebraicGeometry.ProEtale.CondensedRing
