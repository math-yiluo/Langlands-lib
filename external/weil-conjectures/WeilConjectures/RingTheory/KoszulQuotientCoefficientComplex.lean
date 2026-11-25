/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Reduction of coefficients in a dual Koszul complex

Source: Stacks Project, Tag 0BQZ, the coefficient comparison in
lemma-regular-immersion-ext.
(blueprint: new-j3-koszul-quotient-coefficient-complex). -/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- Signed precomposition in the Hom complex with quotient coefficients.
Source: Stacks Project, Tag 0BQZ. 
(blueprint: new-j3-koszul-quotient-coefficient-complex)
-/
noncomputable def koszulQuotientDualBoundary
    (A : Type u) [CommRing A] (I : Ideal A) (r n : ℕ) (f : Fin r → A) :
    ((koszulComplex A r f).X n ⟶ ModuleCat.of A (A ⧸ I)) →ₗ[A]
      ((koszulComplex A r f).X (n + 1) ⟶ ModuleCat.of A (A ⧸ I)) :=
  (-1 : A) ^ (n + 1) •
    Linear.leftComp A (ModuleCat.of A (A ⧸ I)) ((koszulComplex A r f).d (n + 1) n)

/-- Precomposition has square zero, since the Koszul boundary has square zero.
Source: Stacks Project, Tag 0623. 
(blueprint: new-j3-koszul-quotient-coefficient-complex)
-/
theorem koszulQuotientDualBoundary_comp
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A) (n : ℕ) :
    ModuleCat.ofHom (koszulQuotientDualBoundary A I r n f) ≫
      ModuleCat.ofHom (koszulQuotientDualBoundary A I r (n + 1) f) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change koszulQuotientDualBoundary A I r (n + 1) f
    (koszulQuotientDualBoundary A I r n f x) = 0
  simp [koszulQuotientDualBoundary, Linear.leftComp]

/-- The actual signed complex `Hom_A(K(f), A/I)`, without derived choices.
Source: Stacks Project, Tag 0BQZ. 
(blueprint: new-j3-koszul-quotient-coefficient-complex)
-/
noncomputable def koszulQuotientDualComplex
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A ((koszulComplex A r f).X n ⟶ ModuleCat.of A (A ⧸ I)))
    (fun n ↦ ModuleCat.ofHom (koszulQuotientDualBoundary A I r n f))
    (koszulQuotientDualBoundary_comp A I r f)

/-- Reduction of the value of a dual cochain modulo the ideal.
Source: Stacks Project, Tag 0BQZ. 
(blueprint: new-j3-koszul-quotient-coefficient-complex)
-/
noncomputable def koszulCoefficientReductionDegree
    (A : Type u) [CommRing A] (I : Ideal A) (r n : ℕ) (f : Fin r → A) :
    (koszulDualComplex A r f).X n ⟶ (koszulQuotientDualComplex A I r f).X n :=
  ModuleCat.ofHom (Linear.rightComp A ((koszulComplex A r f).X n)
    (ModuleCat.ofHom I.mkQ))

/-- Reduction of values commutes with signed precomposition.
Source: Stacks Project, Tag 0BQZ. 
(blueprint: new-j3-koszul-quotient-coefficient-complex)
-/
theorem koszulCoefficientReductionDegree_comm
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A) (n : ℕ) :
    (koszulDualComplex A r f).d n (n + 1) ≫
        koszulCoefficientReductionDegree A I r (n + 1) f =
      koszulCoefficientReductionDegree A I r n f ≫
        (koszulQuotientDualComplex A I r f).d n (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  simp [koszulCoefficientReductionDegree, koszulDualComplex, koszulQuotientDualComplex,
    koszulDualBoundary, koszulQuotientDualBoundary, Linear.leftComp, Linear.rightComp]

/-- The coefficient morphism of the two dual Koszul complexes.
Source: Stacks Project, Tag 0BQZ.
(blueprint: new-j3-koszul-quotient-coefficient-complex). -/
noncomputable def koszulCoefficientReduction
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A) :
    koszulDualComplex A r f ⟶ koszulQuotientDualComplex A I r f :=
  CochainComplex.ofHom (fun n ↦ koszulCoefficientReductionDegree A I r n f)
    (fun n ↦ (koszulCoefficientReductionDegree_comm A I r f n).symm)

end ExteriorAlgebra
