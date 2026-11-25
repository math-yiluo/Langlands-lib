/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation

@[expose] public section

universe a c

namespace Algebra

/-- The chart coefficient becomes a unit in the localized lifting quotient.
The compatibility equation `hcmod` identifies its image with the element inverted.
Source: Stacks Project, Tag 07CP, localization in the special chart. -/
theorem popescu_special_chart_coefficient_isUnit (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
    letI := cmod.toAlgebra
    IsUnit (algebraMap C₀ (Localization.Away (c (d.ε (d.reduced (d.a k)))))
      (Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k))))) := by
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let D₀ := d.liftingAlgebra ⧸
    Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  let := cmod.toAlgebra
  change IsUnit (algebraMap C₀ _ (Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))))
  rw [IsScalarTower.algebraMap_apply C₀ D₀]
  have ha : algebraMap C₀ D₀ (Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))) =
      c (d.ε (d.reduced (d.a k))) :=
    DFunLike.congr_fun hcmod (d.ε (d.reduced (d.a k)))
  rw [ha]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The canonical special-chart map, with coefficients induced by `cmod` and each free
variable sent to its class in the explicitly constructed lifting quotient.
Source: Stacks Project, Tag 07CP, displayed polynomial chart modulo pi.
(blueprint: def-weil-pbc-popescu-special-chart-map). -/
noncomputable def popescu_special_chart_map (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
    letI := cmod.toAlgebra
    MvPolynomial (d.E k)
      (Localization.Away (Ideal.Quotient.mk
        (Ideal.span ({algebraMap R Cbar π} : Set Cbar)) (d.ε (d.reduced (d.a k))))) →ₐ[C₀]
      Localization.Away (c (d.ε (d.reduced (d.a k)))) := by
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let D₀ := d.liftingAlgebra ⧸
    Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  letI := cmod.toAlgebra
  let a₀ : C₀ := Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))
  let t : D₀ := c (d.ε (d.reduced (d.a k)))
  let T := Localization.Away t
  let f : C₀ →ₐ[C₀] T := Algebra.ofId C₀ T
  let hu : IsUnit (f a₀) :=
    popescu_special_chart_coefficient_isUnit R Cbar π d c cmod hcmod k
  let coeff : Localization.Away a₀ →ₐ[C₀] T :=
    IsLocalization.Away.liftAlgHom a₀ (f := f) hu
  exact MvPolynomial.aevalTower coeff (fun j : d.E k ↦
    algebraMap D₀ T (Ideal.Quotient.mk _
      (ULift.up (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inr j.1))))))

end Algebra
