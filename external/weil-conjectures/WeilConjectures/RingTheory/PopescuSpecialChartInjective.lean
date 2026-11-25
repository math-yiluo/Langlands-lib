/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuSpecialChartMap
import WeilConjectures.RingTheory.PopescuSpecialChartSubstitution

@[expose] public section

universe a c

namespace Algebra

/-- The canonical special-chart map is injective.
Source: Stacks Project, Tag 07CP, polynomial elimination modulo pi
and comparison of the other chart relations.
(blueprint: lem-weil-pbc-popescu-special-chart-map-injective).

Proof: Put A = (Cbar/pi Cbar)[1/a_k]. Define a substitution from R[x,z] to
A[z_j : j in E_k] by sending x_i to its coefficient class, z_j for j in E_k
to X_j, and every other z_l to a_k inverse times sum h_klj X_j. The f_l
map to zero, and pi maps to zero. The k-th relations vanish by substitution,
including those indexed by E_k by normalized_h. For another chart k',
compare its expression for a_k a_k' f_l with the expression on chart k
in the localized reduced conormal module. Linear independence of the basis
specified by hd.conormal forces every coefficient
b_j = a_k' h_klj - sum h_k'lj' h_kj'j to vanish in the localized reduced
coefficient quotient. The presentation surjection and its specified kernel
identify this quotient with Cbar[1/a_k]. Mapping onwards to A preserves the
zero coefficients. Consequently substitution kills every other chart relation.
It therefore descends through the defining quotient, ULift, and the quotient
by pi, and extends through localization because the image of a_k is a unit.
Its composite with the canonical chart map fixes each X_j. It fixes the
coefficients too: hc identifies the x_i images, algebra-map compatibility
identifies constants, and polynomial induction followed by hd.surjective
identifies all of Cbar; hcmod then identifies Cbar/pi Cbar. The composite
fixes the inverse of a_k by uniqueness of inverses, so it fixes A. Polynomial
extensionality makes this composite the identity. A map with this left inverse
is injective, without any assumption that the coefficient rings are nontrivial. -/
theorem popescu_special_chart_map_injective (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    Function.Injective (popescu_special_chart_map R Cbar π d c cmod hcmod k) := by
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let D₀ := d.liftingAlgebra ⧸
    Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  let := cmod.toAlgebra
  let a₀ : C₀ := Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))
  let A := Localization.Away a₀
  let P := MvPolynomial (d.E k) A
  let t : D₀ := c (d.ε (d.reduced (d.a k)))
  let T := Localization.Away t
  obtain ⟨g, hg⟩ := popescu_special_chart_substitution R Cbar π d hd c cmod hc hcmod k
  have ht : t = algebraMap C₀ D₀ a₀ :=
    (DFunLike.congr_fun hcmod (d.ε (d.reduced (d.a k)))).symm
  have hu : IsUnit (g t) := by
    rw [ht, g.commutes]
    exact (IsLocalization.Away.algebraMap_isUnit a₀).map MvPolynomial.C
  let G : T →ₐ[C₀] P := IsLocalization.Away.liftAlgHom t (f := g) hu
  let f := popescu_special_chart_map R Cbar π d c cmod hcmod k
  have hX (j : d.E k) : G (f (MvPolynomial.X j)) = MvPolynomial.X j := by
    simp only [f, popescu_special_chart_map, MvPolynomial.aevalTower_X]
    change IsLocalization.Away.lift t hu _ = _
    rw [IsLocalization.Away.lift_eq]
    exact hg j
  have hC : ∀ b : A, G (f (MvPolynomial.C b)) = MvPolynomial.C b := by
    have hcoeff :
        (G.toRingHom.comp (f.toRingHom.comp MvPolynomial.C)) =
          (MvPolynomial.C : A →+* P) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers a₀)
      apply RingHom.ext
      intro b
      simp only [RingHom.comp_apply]
      change G (f (algebraMap C₀ P b)) = algebraMap C₀ P b
      rw [f.commutes, G.commutes]
    exact DFunLike.congr_fun hcoeff
  have hid : G.toRingHom.comp f.toRingHom = RingHom.id P :=
    MvPolynomial.ringHom_ext hC hX
  have hleft : Function.LeftInverse G f := fun p ↦ DFunLike.congr_fun hid p
  exact hleft.injective

end Algebra
