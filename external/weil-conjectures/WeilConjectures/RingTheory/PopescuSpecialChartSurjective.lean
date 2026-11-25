/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuSpecialChartMap

@[expose] public section

universe a c b

namespace Algebra

/-- Polynomial compatibility in an arbitrary target algebra: equality on the original
variables extends to every polynomial. This generalizes the quotient-valued helper
in PopescuLiftChartFlat and is used here with the localized quotient map. -/
private theorem polynomial_value {R : Type a} {Cbar : Type c} {B : Type b}
    [CommRing R] [CommRing Cbar] [CommRing B] [Algebra R Cbar] [Algebra R B] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (c : Cbar →ₐ[R] B)
    (q : d.polynomial →ₐ[R] B)
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = q (MvPolynomial.X (.inl i)))
    (p : MvPolynomial (Fin d.n) R) :
    c (d.ε (d.reduced p)) = q (d.includeX p) := by
  let Rbar := R ⧸ Ideal.span ({π ^ 2} : Set R)
  let left : MvPolynomial (Fin d.n) R →ₐ[R] B :=
    c.comp ((d.ε.restrictScalars R).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId R Rbar)))
  have heq : left = q.comp d.includeX := by
    apply MvPolynomial.algHom_ext
    intro i
    change c (d.ε (MvPolynomial.map (algebraMap R Rbar) (MvPolynomial.X i))) =
      q (d.includeX (MvPolynomial.X i))
    rw [MvPolynomial.map_X]
    simpa only [PopescuLiftPresentation.includeX, MvPolynomial.rename_X] using hc i
  exact DFunLike.congr_fun heq p

/-- The canonical special-chart map is surjective.
Source: Stacks Project, Tag 07CP, polynomial elimination modulo pi
and comparison of the other chart relations.
(blueprint: lem-weil-pbc-popescu-special-chart-map-surjective).

Proof: Write T for the localized lifting quotient and A for the localized
coefficient quotient. The canonical map sends every free variable z_j,
j in E_k, to its class in T and sends A by the localized coefficient map.
Each original variable x_i is in its image by hc and hcmod. Constants from R
are in its image because the maps are algebra maps. Polynomial induction on
R[x] therefore identifies the image of any original polynomial with its
coefficient image. In T the defining k-th relation, reduced modulo pi, reads
a_k z_l = sum over j in E_k of h_klj z_j. The image of a_k is invertible,
and its inverse is the image of the inverse in A. Thus every auxiliary z_l
is in the map's image, including those outside E_k. Polynomial induction on
R[x,z] shows that every element of the unlocalized lifting algebra is in the
image after passing through its defining quotient and ULift. Surjectivity of
the quotient by pi gives the same claim for D/pi D. Finally every element
of T is a fraction whose denominator is a power of the image of a_k; that
inverse already lies in the image. This proves surjectivity. No preparation,
conormal independence, normalization, or smoothness assumption is needed. -/
theorem popescu_special_chart_map_surjective (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    Function.Surjective (popescu_special_chart_map R Cbar π d c cmod hcmod k) := by
  classical
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let D₀ := d.liftingAlgebra ⧸
    Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  let := cmod.toAlgebra
  let a₀ : C₀ := Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))
  let t : D₀ := c (d.ε (d.reduced (d.a k)))
  let A := Localization.Away a₀
  let T := Localization.Away t
  let f := popescu_special_chart_map R Cbar π d c cmod hcmod k
  let F : d.polynomial →ₐ[R] T :=
    (IsScalarTower.toAlgHom R D₀ T).comp ((Ideal.Quotient.mkₐ R _).comp
      ((ULift.algEquiv (R := R)).symm.toAlgHom.comp
        (Ideal.Quotient.mkₐ R d.definingIdeal)))
  have coeff (x : C₀) : algebraMap C₀ T x ∈ f.range := f.range.algebraMap_mem x
  have value (p : MvPolynomial (Fin d.n) R) :
      F (d.includeX p) = algebraMap D₀ T (c (d.ε (d.reduced p))) := by
    apply (polynomial_value π d ((IsScalarTower.toAlgHom R D₀ T).comp c) F
      (fun i ↦ congrArg (algebraMap D₀ T) (hc i)) p).symm
  have original (p : MvPolynomial (Fin d.n) R) : F (d.includeX p) ∈ f.range := by
    rw [value]
    have he : cmod (Ideal.Quotient.mk _ (d.ε (d.reduced p))) =
        c (d.ε (d.reduced p)) := DFunLike.congr_fun hcmod _
    rw [← he]
    exact coeff (Ideal.Quotient.mk _ (d.ε (d.reduced p)))
  have free (j : d.E k) : F (MvPolynomial.X (.inr j.1)) ∈ f.range := by
    refine f.mem_range.mpr ⟨MvPolynomial.X j, ?_⟩
    simp only [f, popescu_special_chart_map, MvPolynomial.aevalTower_X]
    rfl
  let v : T := f (MvPolynomial.C (IsLocalization.Away.invSelf a₀ : A))
  have hv : v ∈ f.range := f.mem_range_self _
  have ht : algebraMap D₀ T t * v = 1 := by
    have he : f (MvPolynomial.C (algebraMap C₀ A a₀)) = algebraMap D₀ T t := by
      change f (algebraMap C₀ _ a₀) = _
      rw [f.commutes, IsScalarTower.algebraMap_apply C₀ D₀ T]
      have ha : algebraMap C₀ D₀ a₀ = t := DFunLike.congr_fun hcmod _
      rw [ha]
    have h := congrArg f (congrArg (MvPolynomial.C (σ := d.E k))
      (IsLocalization.Away.mul_invSelf a₀ (S := A)))
    simp only [map_mul, map_one, he] at h
    exact h
  have hπ : F (MvPolynomial.C π) = 0 := by
    change algebraMap R T π = 0
    rw [IsScalarTower.algebraMap_apply R D₀ T]
    have hzero : algebraMap R D₀ π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hzero, map_zero]
  have equation (i : Fin d.m ⊕ (Fin d.r × Fin d.m)) : F (d.equation i) = 0 := by
    change algebraMap D₀ T (Ideal.Quotient.mk _ (ULift.up
      (Ideal.Quotient.mk d.definingIdeal (d.equation i)))) = 0
    have hz : Ideal.Quotient.mk d.definingIdeal (d.equation i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [hz]
    change algebraMap D₀ T (Ideal.Quotient.mk _ 0) = 0
    rw [map_zero, map_zero]
  have aux (l : Fin d.m) : F (MvPolynomial.X (.inr l)) ∈ f.range := by
    have hrel := equation (.inr (k, l))
    simp only [PopescuLiftPresentation.equation, map_sub, map_mul, map_sum,
      hπ, zero_mul, sub_zero, sub_eq_zero] at hrel
    have hat : F (d.includeX (d.a k)) = algebraMap D₀ T t := value _
    rw [hat] at hrel
    have hz : F (MvPolynomial.X (.inr l)) =
        v * ∑ j ∈ d.E k, F (d.includeX (d.h k l j)) * F (MvPolynomial.X (.inr j)) := by
      rw [← hrel, ← mul_assoc, mul_comm v, ht, one_mul]
    rw [hz]
    exact f.range.mul_mem hv (f.range.sum_mem fun j hj ↦
      f.range.mul_mem (original _) (free ⟨j, hj⟩))
  have allpoly (p : d.polynomial) : F p ∈ f.range := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h := original (MvPolynomial.C r)
      simpa [PopescuLiftPresentation.includeX] using h
    | add p q hp hq => simpa only [map_add] using f.range.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      apply f.range.mul_mem hp
      cases i with
      | inl i =>
        have h := original (MvPolynomial.X i)
        simpa [PopescuLiftPresentation.includeX] using h
      | inr l => exact aux l
  have allD₀ (x : D₀) : algebraMap D₀ T x ∈ f.range := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective x.down
    have hx : x = ULift.up (Ideal.Quotient.mk d.definingIdeal p) := by
      exact ULift.ext hp.symm
    rw [hx]
    exact allpoly p
  intro z
  obtain ⟨n, x, hn⟩ := IsLocalization.Away.surj t z
  have hz : z = algebraMap D₀ T x * v ^ n := by
    calc
      z = z * (algebraMap D₀ T t * v) ^ n := by rw [ht, one_pow, mul_one]
      _ = (z * algebraMap D₀ T t ^ n) * v ^ n := by rw [mul_pow, mul_assoc]
      _ = algebraMap D₀ T x * v ^ n := by rw [hn]
  exact f.mem_range.mp (hz ▸ f.range.mul_mem (allD₀ x) (f.range.pow_mem hv n))

end Algebra
