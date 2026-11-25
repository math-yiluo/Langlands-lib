/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCanonicalFinite
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMate
import WeilConjectures.Tactic.ExactModProofs

/-! # Finite trace normalization of the integral orientation -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- A comparison defined by mates transports an orientation precisely when it transports
its counit transpose. -/
lemma purity_orientation_eq_iff_trace_eq
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : A' ⥤ B'} {R' : B' ⥤ A'} (adj' : L' ⊣ R')
    (S : A ⥤ A') (T : B ⥤ B') (α : L ⋙ T ≅ S ⋙ L')
    {K : A} {U : B} (φ : K ⟶ R.obj U) (θ : S.obj K ⟶ R'.obj (T.obj U)) :
    S.map φ ≫ (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.inv)).app U = θ ↔
      T.map ((adj.homEquiv _ _).symm φ) =
        α.hom.app K ≫ (adj'.homEquiv _ _).symm θ := by
  rw [← (adj'.homEquiv _ _).symm.injective.eq_iff]
  rw [Adjunction.homEquiv_symm_map_comp_mateEquiv_app]
  constructor
  · intro h
    simpa only [Iso.hom_inv_id_app_assoc] using congrArg (α.hom.app K ≫ ·) h
  · intro h
    rw [h, Iso.inv_hom_id_app_assoc]

/-- The trace criterion with the exceptional comparison supplied as an isomorphism. -/
lemma purity_orientation_map_eq_iff_trace_eq
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : A' ⥤ B'} {R' : B' ⥤ A'} (adj' : L' ⊣ R')
    (S : A ⥤ A') (T : B ⥤ B') (α : L ⋙ T ≅ S ⋙ L')
    (β : R ⋙ S ≅ T ⋙ R')
    (hβ : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.inv)) = β.hom)
    {K : A} {U : B} (φ : K ⟶ R.obj U)
    (θ θ₀ : S.obj K ⟶ S.obj (R.obj U)) (hθ : θ = θ₀) :
    S.map φ = θ₀ ↔ T.map ((adj.homEquiv _ _).symm φ) =
      α.hom.app K ≫ (adj'.homEquiv _ _).symm (θ ≫ β.hom.app U) := by
  rw [← hθ, ← cancel_mono (β.hom.app U)]
  have h := purity_orientation_eq_iff_trace_eq adj adj' S T α φ (θ ≫ β.hom.app U)
  rw [hβ] at h
  exact h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- The counit transpose of the prescribed finite orientation, with the actual comparison
between integral and étale exceptional pullback. -/
noncomputable def canonicalFiniteIntegralOrientationTrace (n : ℕ) :
    have := HasCompactification.of_over f
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
      f.left).obj ((etaleReduction ℓ E.1 n X).obj
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) ⟶
      (etaleReduction ℓ E.1 n Y).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) :=
  have := HasCompactification.of_over f
  ((Etale.rightDerivedUpperShriekAdjunction (integersModPowCoeff.{u} ℓ E.1 n)
    f.left).homEquiv _ _).symm
      ((finiteEtaleReading ℓ E.1 n X).map
          (canonicalFiniteIntegralOrientationIso ℓ E f d n).hom ≫
        (etaleReductionUpperShriekIso ℓ E.1 n f).hom.app (𝟙_ _))

/-- Finite trace normalization is equivalent to the prescribed finite orientation equation. -/
theorem isIntegralSmoothOrientation_iff_trace
    (φ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :
    IsIntegralSmoothOrientation ℓ E f d φ ↔
      ∀ n : ℕ, (etaleReduction ℓ E.1 (n + 1) Y).map
          (((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f).homEquiv
            _ _).symm φ) =
        (etaleReductionLowerShriekIsoOfCompactification ℓ E.1 (n + 1)
          (compactificationOverField f)).hom.app _ ≫
            canonicalFiniteIntegralOrientationTrace ℓ E f d (n + 1) := by
  have := HasCompactification.of_over f
  unfold IsIntegralSmoothOrientation
  apply forall_congr'
  intro n
  let θ := (finiteEtaleReading ℓ E.1 (n + 1) X).map
    (canonicalFiniteIntegralOrientationIso ℓ E f d (n + 1)).hom
  have hθ := canonicalFiniteIntegralOrientationIso_map_hom ℓ E f d (n + 1)
  have h := purity_orientation_map_eq_iff_trace_eq
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (etaleReduction ℓ E.1 (n + 1) X) (etaleReduction ℓ E.1 (n + 1) Y)
    (etaleReductionLowerShriekIsoOfCompactification ℓ E.1 (n + 1)
      (compactificationOverField f))
    (etaleReductionUpperShriekIso ℓ E.1 (n + 1) f) rfl φ
    θ _ hθ
  dsimp only [etaleReduction, finiteEtaleReading, Functor.comp_map, Functor.comp_obj, θ,
    canonicalFiniteIntegralOrientationTrace] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing
