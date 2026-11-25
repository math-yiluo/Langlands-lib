/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Resolution certificate for restriction of algebraic self-Tor

Source: Stacks Project, Tags 00LS and 06YH.
(blueprint: new-t2-self-tor-restriction-certificate). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- A restriction map is induced by augmented resolution comparison and quotient
change of scalars. The condition on all cycles fixes the entire map, including
Tor classes not in the image of the conormal exterior power.
Source: Stacks Project, Tags 00LS and 06YH.
(blueprint: new-t2-self-tor-restriction-certificate). -/
def IsSelfTorRestrictionMap (A B : Type u) [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (φ : A →+* B) (n : ℕ)
    (q : (((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) →
      (((Tor' (ModuleCat.{u} B) n).obj (ModuleCat.of B (B ⧸ J))).obj
        (ModuleCat.of B (B ⧸ J)))) : Prop :=
  ∀ (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (Q : ProjectiveResolution (ModuleCat.of B (B ⧸ J))),
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
    ∃ (ψ : (A ⧸ I) →+* (B ⧸ J))
      (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj Q.complex)
      (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj (TB.obj Q.complex)),
      (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) ∧
      (∀ x : P.complex.X 0, Q.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
      (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
        k.f j (x ⊗ₜ[A] y) = (show Q.complex.X j from a.f j x) ⊗ₜ[B] (ψ y)) ∧
      ∀ (z : (TA.obj P.complex).cycles n) (w : (TB.obj Q.complex).cycles n),
        (TB.obj Q.complex).iCycles n w = k.f n ((TA.obj P.complex).iCycles n z) →
        (Q.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).hom
            (q ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
              ((TA.obj P.complex).homologyπ n z))) =
          (TB.obj Q.complex).homologyπ n w

end AlgebraicGeometry
