/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.EtalePolynomialStandardSmooth
import WeilConjectures.AlgebraicGeometry.SmoothRetractRelativeGlobalCompleteIntersection
import WeilConjectures.RingTheory.SmoothConormalBasisEtalePolynomialChart

/-!
# Smooth retracts of standard smooth algebras

Source: Stacks Project, Smoothing Ring Maps, Lemma 07CH
(blueprint: lem-weil-pbc-smooth-retract-standard-smooth).
-/

@[expose] public section

universe u v

namespace Algebra


/-- Every smooth R-algebra admits an R-algebra inclusion into a standard smooth R-algebra,
with an R-algebra retraction, and the inclusion itself is smooth.
Source: Stacks Project, Lemma 07CH
(blueprint: lem-weil-pbc-smooth-retract-standard-smooth).

Proof. First take the relative global complete intersection retract `C` of Stacks 07CG,
with its specified conormal basis. Smooth composition makes `C` smooth over `R`.
The étale polynomial chart lemma (the construction in the proof of 07CH) gives
`g ∈ C[y]` with constant coefficient one and an étale `R[z]`-algebra `L = C[y]_g`.
Mathlib identifies étale algebras with standard smooth algebras of relative dimension zero;
composition with the standard smooth polynomial algebra makes `L` standard smooth over `R`.
Evaluation at zero sends `g` to one, so the localization universal property extends evaluation
to an `R`-algebra map `L → C`. Composing with `C → A` gives the retraction; its composite
with `A → C → L` is the identity because evaluation fixes constants.
Polynomial extension and principal localization are smooth, so `A → L` is smooth by
composition. Finally lift `L` to the universe required by the unchanged statement and
transport these properties along the canonical algebra equivalence. -/
theorem Smooth.exists_standardSmooth_retract
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] [Smooth R A] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      IsStandardSmooth R B ∧ ∃ (ι : A →ₐ[R] B) (ρ : B →ₐ[R] A),
        ρ.comp ι = AlgHom.id R A ∧ @Smooth A _ B _ ι.toRingHom.toAlgebra := by
  classical
  obtain ⟨n, c, f, _, ⟨b, hb⟩, σ, π, hπσ, instAC, hσ, hAC⟩ :=
    smooth_retract_relative_global_complete_intersection R A
  let C := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let : Algebra A C := instAC
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R C r = algebraMap A C (algebraMap R A r)
    rw [show algebraMap A C = σ.toRingHom from hσ]
    exact (σ.commutes r).symm
  have : Smooth A C := hAC
  have : Smooth R C := Smooth.comp R A C
  obtain ⟨g, hg, θ, hθ⟩ := exists_etale_polynomial_chart_of_conormal_basis R n c f b hb
  let D := MvPolynomial (Fin c) C
  let L := Localization.Away g
  have : Smooth C D := ⟨inferInstance, inferInstance⟩
  have : Smooth D L := Smooth.of_isLocalization_Away g
  have : Smooth C L := Smooth.comp C D L
  have : Smooth A L := Smooth.comp A C L
  have : IsStandardSmooth R L := isStandardSmooth_of_etale_polynomial R L n θ hθ
  let ε : D →ₐ[C] C := MvPolynomial.aeval (fun _ => 0)
  have hε : IsUnit (ε g) := by
    change IsUnit (MvPolynomial.aeval (fun _ : Fin c => (0 : C)) g)
    rw [MvPolynomial.aeval_zero', hg]
    exact isUnit_one
  let εg : L →ₐ[C] C := IsLocalization.Away.liftAlgHom g hε
  let τ : L →ₐ[R] A := π.comp (εg.restrictScalars R)
  let B := ULift.{v} L
  let e : B ≃ₐ[R] L := ULift.algEquiv
  have : IsStandardSmooth R B := IsStandardSmooth.of_algEquiv e.symm
  have : Smooth A B := Smooth.of_equiv (ULift.algEquiv (R := A)).symm
  let ι : A →ₐ[R] B := IsScalarTower.toAlgHom R A B
  refine ⟨B, inferInstance, inferInstance, inferInstance, ι, τ.comp e.toAlgHom, ?_, ?_⟩
  · ext a
    change π (εg (algebraMap A L a)) = a
    rw [IsScalarTower.algebraMap_apply A C L]
    change π (εg (algebraMap D L (MvPolynomial.C (algebraMap A C a)))) = a
    change π (IsLocalization.Away.lift g hε
      (algebraMap D L (MvPolynomial.C (algebraMap A C a)))) = a
    rw [IsLocalization.Away.lift_eq]
    change π (ε (MvPolynomial.C (algebraMap A C a))) = a
    change π (MvPolynomial.aeval (fun _ : Fin c => (0 : C))
      (MvPolynomial.C (algebraMap A C a))) = a
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_self]
    rw [show algebraMap A C = σ.toRingHom from hσ]
    exact AlgHom.congr_fun hπσ a
  · change @Smooth A _ B _ (algebraMap A B).toAlgebra
    rw [toAlgebra_algebraMap]
    infer_instance

end Algebra
