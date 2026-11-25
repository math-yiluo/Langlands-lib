/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.Homotopy

/-! # A Koszul generator acts by a null-homotopic map

Source: Stacks Project, More on Algebra, Tag 0663.
(blueprint: lem-k3-koszul-generator-homotopy).
-/

@[expose] public section

universe u
open CategoryTheory
namespace ExteriorAlgebra

private noncomputable def generatorWedge
    (A : Type u) [CommRing A] (r : ℕ) (i : Fin r) (n : ℕ) :
    ⋀[A]^n (Fin r →₀ A) →ₗ[A] ⋀[A]^(n + 1) (Fin r →₀ A) :=
  LinearMap.codRestrict _
    ((LinearMap.mulLeft A (ι A (Finsupp.single i 1))).comp
      (⋀[A]^n (Fin r →₀ A)).subtype) (by
    intro x
    change ι A (Finsupp.single i 1) * (x : ExteriorAlgebra A (Fin r →₀ A)) ∈ _
    rw [show (⋀[A]^(n + 1) (Fin r →₀ A)) =
      LinearMap.range (ι A) * (⋀[A]^n (Fin r →₀ A)) by
        change _ ^ (n + 1) = _ * _ ^ n
        rw [pow_succ']]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) x.property)

private theorem generatorWedge_identity
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (i : Fin r) (n : ℕ) :
    ModuleCat.ofHom (koszulBoundary A r f n) ≫
        ModuleCat.ofHom (generatorWedge A r i n) +
      ModuleCat.ofHom (generatorWedge A r i (n + 1)) ≫
        ModuleCat.ofHom (koszulBoundary A r f (n + 1)) =
      (f i) • 𝟙 (ModuleCat.of A (⋀[A]^(n + 1) (Fin r →₀ A))) := by
  ext x
  change ι A (Finsupp.single i 1) *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
        (Finsupp.linearCombination A f) (x : ExteriorAlgebra A (Fin r →₀ A)) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A f)
      (ι A (Finsupp.single i 1) * (x : ExteriorAlgebra A (Fin r →₀ A))) =
    (f i) • (x : ExteriorAlgebra A (Fin r →₀ A))
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp

private theorem generatorWedge_zero_identity
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (i : Fin r) :
    ModuleCat.ofHom (generatorWedge A r i 0) ≫
      ModuleCat.ofHom (koszulBoundary A r f 0) =
      (f i) • 𝟙 (ModuleCat.of A (⋀[A]^0 (Fin r →₀ A))) := by
  ext x
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A f)
      (ι A (Finsupp.single i 1) * (x : ExteriorAlgebra A (Fin r →₀ A))) =
    (f i) • (x : ExteriorAlgebra A (Fin r →₀ A))
  rw [CliffordAlgebra.contractLeft_ι_mul]
  have hx : ∃ a : A,
      algebraMap A (ExteriorAlgebra A (Fin r →₀ A)) a = x := by
    have hmem := x.property
    change (x : ExteriorAlgebra A (Fin r →₀ A)) ∈ _ ^ 0 at hmem
    simpa only [pow_zero, Submodule.mem_one] using hmem
  obtain ⟨a, ha⟩ := hx
  rw [← ha, CliffordAlgebra.contractLeft_algebraMap]
  simp

/-- Multiplication by a member of the sequence on its Koszul chain complex is
homotopic to zero. Source: Stacks Project, Tag 0663, Lemma 15.29.6,
and its preceding lemma (Tag 0626).
(blueprint: lem-k3-koszul-generator-homotopy).

Proof: Set E = Fin r →₀ A and e_i = Finsupp.single i 1. In degree q take the
linear map x ↦ ι(e_i) * x from ⋀^q E to ⋀^(q+1) E; its image lies in that
exterior power by the multiplication rule for the grading. Take zero components
for all other pairs of degrees. The contraction recursion gives
D(ι(e_i) * x) = f_i • x - ι(e_i) * D(x). Thus d h + h d is multiplication
by f_i. In degree zero the second summand is zero, since contraction kills
scalars, and the same recursion proves the identity. Restrict the identity to
exterior powers, using injectivity of their subtype maps, to obtain the
Homotopy comm field. The off-diagonal components give its zero field.
No regularity assumption is used; r=0 has no i, and the zero ring is allowed. -/
theorem koszul_generator_homotopy
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (i : Fin r) :
    Nonempty (Homotopy ((f i) • 𝟙 (koszulComplex A r f)) 0)  := by
  let K := koszulComplex A r f
  let h : ∀ n m, K.X n ⟶ K.X m := fun n m ↦
    if hm : n + 1 = m then
      ModuleCat.ofHom (generatorWedge A r i n) ≫ eqToHom (congrArg K.X hm)
    else 0
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    exact dite_eq_right hnm
  · intro n
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        HomologicalComplex.zero_f_apply, add_zero, zero_add]
      simpa only [K, koszulComplex, HomologicalComplex.smul_f_apply,
        HomologicalComplex.id_f, ChainComplex.of_d] using
        (generatorWedge_zero_identity A r f i).symm
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        HomologicalComplex.zero_f_apply, add_zero]
      simpa only [K, koszulComplex, HomologicalComplex.smul_f_apply,
        HomologicalComplex.id_f, ChainComplex.of_d] using
        (generatorWedge_identity A r f i n).symm

end ExteriorAlgebra
