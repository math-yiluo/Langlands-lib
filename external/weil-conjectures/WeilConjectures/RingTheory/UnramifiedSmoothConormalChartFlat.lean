/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.SmoothConormalChartDifferentialBasis
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Fibrewise flatness of an unramified smooth chart

Source: Stacks Project, proof of Lemma 07CH.
(blueprint: lem-weil-pbc-unramified-smooth-conormal-chart-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

/-- Unramified maps from an n-variable polynomial ring into the localized polynomial
extension of a smooth quotient with conormal rank c are flat.

Source: Stacks Project, proof of Lemma 07CH, fibrewise flatness paragraph, using
Tags 00R4, 00T6, and 00R7, https://stacks.math.columbia.edu/tag/07CH.
(blueprint: lem-weil-pbc-unramified-smooth-conormal-chart-flat).

Proof. The split conormal sequence, polynomial-extension decomposition, and
localization identify Omega(B/R) with B^n, where B = C[y]_g. The polynomial
source P also has n differential generators. Formal unramifiedness makes
B tensor_P Omega(P/R) -> Omega(B/R) surjective. A surjective endomorphism
of a finite free module is injective, so this map is an isomorphism.
Smoothness of B over R kills H1(L(B/R)); the Jacobi-Zariski sequence
(Tags 00S2 and 031J) then makes H1(L(B/P)) inject into the kernel of this
isomorphism, hence zero. Omega(B/P) is already zero by unramifiedness.
Thus B is formally smooth over P. It is finitely presented over P because
it is finitely presented over R and P is of finite type over R.
Smoothness over P follows, and Mathlib's smooth-implies-flat theorem
finishes. The argument uses the given map theta throughout and applies
also to empty variable sets and zero localizations. -/
theorem flat_of_unramified_smooth_conormal_chart
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g) :
    letI := θ.toRingHom.toAlgebra
    letI : Module (MvPolynomial (Fin n) R) (Localization.Away g) :=
      θ.toRingHom.toAlgebra.toModule
    FormallyUnramified (MvPolynomial (Fin n) R) (Localization.Away g) →
      Module.Flat (MvPolynomial (Fin n) R) (Localization.Away g) := by
  classical
  intro hu
  let P := MvPolynomial (Fin n) R
  let C := P ⧸ Ideal.span (Set.range f)
  let D := MvPolynomial (Fin c) C
  let B := Localization.Away g
  let : Algebra P B := θ.toRingHom.toAlgebra
  let : Module P B := θ.toRingHom.toAlgebra.toModule
  have := IsScalarTower.of_algHom θ
  have : FormallyUnramified P B := hu
  have : Smooth C D := ⟨inferInstance,
    FinitePresentation.mvPolynomial_of_finitePresentation (R := C) (A := C) (Fin c)⟩
  have : Smooth R D := Smooth.comp R C D
  have : Smooth R B := Smooth.comp R D B
  obtain ⟨bB⟩ := KaehlerDifferential.nonempty_basis_smooth_conormal_chart R n c f b g
  let bP := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange B
  let e := bP.equivFun.trans bB.equivFun.symm
  let d := KaehlerDifferential.mapBaseChange R P B
  have hd : Function.Surjective d := fun x ↦
    (KaehlerDifferential.exact_mapBaseChange_map R P B x).mp (Subsingleton.elim _ _)
  have hEnd : Function.Surjective (e.symm.toLinearMap.comp d) := e.symm.surjective.comp hd
  have hi : Function.Injective d := by
    have h := Module.End.injective_of_surjective B _ hEnd
    intro x y hxy
    exact h (congrArg e.symm hxy)
  have hδ : Function.Injective (H1Cotangent.δ R P B) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (H1Cotangent.exact_map_δ R P B)).mpr
    ext x
    simp only [Subsingleton.elim x 0, map_zero]
  have hH : Subsingleton (H1Cotangent P B) := by
    apply subsingleton_iff_forall_eq 0 |>.mpr
    intro x
    apply hδ
    apply hi
    have hzero := (H1Cotangent.exact_δ_mapBaseChange R P B
      (H1Cotangent.δ R P B x)).mpr ⟨x, rfl⟩
    simpa only [map_zero] using hzero
  have : FormallySmooth P B := ⟨inferInstance, hH⟩
  have : FinitePresentation P B := FinitePresentation.of_restrict_scalars_finitePresentation R P B
  have : Smooth P B := ⟨inferInstance, inferInstance⟩
  exact Smooth.flat P B

end Algebra
