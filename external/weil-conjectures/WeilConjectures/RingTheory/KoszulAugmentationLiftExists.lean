/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Lifting a Koszul augmentation to a projective resolution

Source: Stacks Project, Tag 00LS, part (1).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem koszulBoundary_zero_formula (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (x : ⋀[A]^1 (Fin r →₀ A)) :
    exteriorPower.zeroEquiv A (Fin r →₀ A) (ExteriorAlgebra.koszulBoundary A r f 0 x) =
      Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x) := by
  have he : (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (ExteriorAlgebra.koszulBoundary A r f 0) = (Finsupp.linearCombination A f).comp
        (exteriorPower.oneEquiv A (Fin r →₀ A)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    have hg : ExteriorAlgebra.koszulBoundary A r f 0 (exteriorPower.ιMulti A 1 v) =
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm
          (Finsupp.linearCombination A f (v 0)) := by
      apply Subtype.ext
      simp [ExteriorAlgebra.koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
        ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
        Algebra.algebraMap_eq_smul_one]
    simp [hg]
  exact LinearMap.congr_fun he x

/-- A finite tuple in an ideal has an augmentation-preserving Koszul lift to any
projective resolution of the quotient. Source: Stacks Project, Tag 00LS, part (1).
(blueprint: new-e1-koszul-augmentation-lift-exists).

Proof: Every term of the Koszul complex is free, hence projective. Lift its
quotient augmentation through the epimorphism in degree zero of P. The first
Koszul differential has image in I, so its composite with that augmentation is
zero; exactness of P in degree zero lifts the resulting map to degree one.
Inductively the chain-map equation in the preceding degree and d squared equal
to zero show that the next map lands in the cycles of P. Exactness and
projectivity lift it one degree further. ChainComplex.mkHom assembles these
lifts. Neither regularity nor generation of the whole ideal is needed. -/
theorem koszul_augmentation_lift_exists (A : Type u) [CommRing A]
    (I : Ideal A) (r : ℕ) (g : Fin r → I)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))) :
    ∃ a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex,
      a.f 0 ≫ P.π.f 0 =
        ModuleCat.ofHom (I.mkQ.comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) := by
  classical
  let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
  have (i : ℕ) : Projective (K.X i) := by
    change Projective (ModuleCat.of A (⋀[A]^i (Fin r →₀ A)))
    infer_instance
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) :=
    ModuleCat.ofHom (I.mkQ.comp (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)
  have hz : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change I.mkQ (exteriorPower.zeroEquiv A (Fin r →₀ A)
      (ExteriorAlgebra.koszulBoundary A r (fun j ↦ (g j : A)) 0 x)) = 0
    rw [koszulBoundary_zero_formula]
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    have he : (Finsupp.linearCombination A (fun j ↦ (g j : A))) =
        I.subtype.comp (Finsupp.linearCombination A g) := by
      ext j
      simp
    rw [he]
    exact (Finsupp.linearCombination A g _).property
  let a₀ : K.X 0 ⟶ P.complex.X 0 := Projective.factorThru q (P.π.f 0)
  have ha₀ : a₀ ≫ P.π.f 0 = q := Projective.factorThru_comp q (P.π.f 0)
  have hz₁ : (K.d 1 0 ≫ a₀) ≫ P.π.f 0 = 0 := by rw [Category.assoc, ha₀, hz]
  let a₁ : K.X 1 ⟶ P.complex.X 1 := P.exact₀.liftFromProjective _ hz₁
  have ha₁ : a₁ ≫ P.complex.d 1 0 = K.d 1 0 ≫ a₀ :=
    P.exact₀.liftFromProjective_comp _ _
  let a : K ⟶ P.complex := ChainComplex.mkHom _ _ a₀ a₁ ha₁ fun n ⟨b, b', hb⟩ ↦
    ⟨(P.exact_succ n).liftFromProjective (K.d (n + 2) (n + 1) ≫ b') (by simp [hb]),
      (P.exact_succ n).liftFromProjective_comp _ _⟩
  exact ⟨a, ha₀⟩

end AlgebraicGeometry
