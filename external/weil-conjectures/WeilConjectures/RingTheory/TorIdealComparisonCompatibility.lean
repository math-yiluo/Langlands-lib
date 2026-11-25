/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

import WeilConjectures.RingTheory.TorIdealQuotientChainMap
import WeilConjectures.RingTheory.TorIdealCycleLift

/-! # Compatibility of Tor connecting formulas
Source: Stacks Project, Algebra, Tags 00M5 and 00M6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, functoriality of Tor preceding Tag 00M5,
Remark 00M6, and the comparison of resolutions in Tag 00LS
(blueprint: lem-weil-pbc-tor-ideal-comparison-compatibility).

Proof in words: use the supplied semilinear comparison `φ₀` to define the
quotient tensor chain map, sending `p ⊗ mk r` to `φ₀ p ⊗ mk (f r)`.
It is well defined because `f(I) ⊆ J` and the tensor balancing relation is
preserved by semilinearity. The chain identities follow from those of `φ₀`.
Apply first homology and transport by the resolution isomorphisms to obtain `τ`.
For any cycle, choose a quotient lift `y` and express `d y` as a finite sum of
ideal multiples. Such choices exist since tensoring a free module with `R/I`
gives its quotient by `I` times that module. The image cycle has lift `φ₀ y`
and differential `∑ f(a j) • φ₀(p j)`. The two assumed connecting formulas,
augmentation compatibility, and the pure-tensor formula for `θ` give
`δA (τ t) = θ (δR t)` for all cycle classes, hence all Tor elements.
For an arbitrary second comparison `φ`, the same construction gives a chain
map and a map `τφ` satisfying this same identity. Injectivity of `δA` implies
`τφ = τ`, proving the universal cycle-class formula. No multiplication maps or
image descriptions are needed here. The argument also covers zero or unit
ideals, zero modules, and identity or noninjective ring maps.
-/
theorem exists_tor_ideal_comparison_compatibility
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) (J : Ideal A) (hJ : J = Ideal.map f I)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} A)
    (g : M →+ N) (hg : ∀ (r : R) (x : M), g (r • x) = f r • g x)
    (P : ProjectiveResolution M) (G : ProjectiveResolution N)
    (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    (hG : ∀ n : ℕ, Module.Free A (G.complex.X n))
    (δR : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))) →ₗ[R] (I ⊗[R] M))
    (δA : (((Tor' (ModuleCat.{u} A) 1).obj N).obj (ModuleCat.of A (A ⧸ J))) →ₗ[A] (J ⊗[A] N))
    (θ : (I ⊗[R] M) →+ (J ⊗[A] N))
    (hθ : ∀ (a : I) (x : M) (b : J), (b : A) = f a →
      θ (a ⊗ₜ[R] x) = b ⊗ₜ[A] g x)
    (hδA : Function.Injective δA)
    (hformulaR : ∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δR ((P.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I)))
          1).inv (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
          I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z)) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j))
    (hformulaA : ∀ (z : ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
        J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).cycles 1)
        (y : G.complex.X 1) (k : ℕ) (b : Fin k → J) (p : Fin k → G.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj G.complex).iCycles 1 z = y ⊗ₜ[A] (1 : A ⧸ J) →
        G.complex.d 1 0 y = ∑ j, (b j : A) • p j →
        δA ((G.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J)))
          1).inv (((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
          J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).homologyπ 1 z)) =
          ∑ j, b j ⊗ₜ[A] G.π.f 0 (p j))
    (φ₀ : ∀ n : ℕ, (P.complex.X n) →+ (G.complex.X n))
    (hφ₀ : ∀ (n : ℕ) (r : R) (p : P.complex.X n), φ₀ n (r • p) = f r • φ₀ n p)
    (hdφ₀ : ∀ (n : ℕ) (p : P.complex.X (n + 1)),
      G.complex.d (n + 1) n (φ₀ (n + 1) p) = φ₀ n (P.complex.d (n + 1) n p))
    (hπφ₀ : ∀ p : P.complex.X 0, G.π.f 0 (φ₀ 0 p) = g (P.π.f 0 p)) :
    ∃ τ : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))) →+ (((Tor'
        (ModuleCat.{u} A) 1).obj N).obj (ModuleCat.of A (A ⧸ J))),
      (∀ φ : ∀ n : ℕ, (P.complex.X n) →+ (G.complex.X n),
        (∀ (n : ℕ) (r : R) (p : P.complex.X n), φ n (r • p) = f r • φ n p) →
        (∀ (n : ℕ) (p : P.complex.X (n + 1)),
          G.complex.d (n + 1) n (φ (n + 1) p) = φ n (P.complex.d (n + 1) n p)) →
        (∀ p : P.complex.X 0, G.π.f 0 (φ 0 p) = g (P.π.f 0 p)) →
        ∃ ψ :
          ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R
              ⧸ I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ⟶
          ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A
              ⧸ J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex),
          (∀ (n : ℕ) (p : P.complex.X n) (r : R),
            ψ.f n (p ⊗ₜ[R] Ideal.Quotient.mk I r) =
              φ n p ⊗ₜ[A] Ideal.Quotient.mk J (f r)) ∧
          (∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
            I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
            (w : ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
              J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).cycles 1),
            ψ.f 1 (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
              I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z) =
              ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
                J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).iCycles 1 w →
            τ ((P.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
              I))) 1).inv (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
              I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z)) =
              ((G.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
                J))) 1).inv (((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
                J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).homologyπ 1 w)))) ∧
      (∀ t : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))), 
        δA (τ t) = θ (δR t)) := by
  classical
  have _ := hg
  have _ := hP
  have _ := hG
  let C := (((tensoringRight (ModuleCat.{u} R)).obj
    (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let D := (((tensoringRight (ModuleCat.{u} A)).obj
    (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex
  let eR := P.isoLeftDerivedObj
    ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))) 1
  let eA := G.isoLeftDerivedObj
    ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J))) 1
  have hlocal (φ : ∀ n : ℕ, (P.complex.X n) →+ (G.complex.X n))
      (hφ : ∀ (n : ℕ) (r : R) (p : P.complex.X n), φ n (r • p) = f r • φ n p)
      (hdφ : ∀ (n : ℕ) (p : P.complex.X (n + 1)),
        G.complex.d (n + 1) n (φ (n + 1) p) = φ n (P.complex.d (n + 1) n p))
      (hπφ : ∀ p : P.complex.X 0, G.π.f 0 (φ 0 p) = g (P.π.f 0 p))
      (ψ : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C ⟶
        ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj D)
      (hψ : ∀ (n : ℕ) (p : P.complex.X n) (r : R),
        ψ.f n (p ⊗ₜ[R] Ideal.Quotient.mk I r) =
          φ n p ⊗ₜ[A] Ideal.Quotient.mk J (f r))
      (z : C.cycles 1) (w : D.cycles 1)
      (heq : ψ.f 1 (C.iCycles 1 z) = D.iCycles 1 w) :
      δA (eA.inv (D.homologyπ 1 w)) = θ (δR (eR.inv (C.homologyπ 1 z))) := by
    obtain ⟨y, k, a, p, hy, hdy⟩ := exists_quotient_cycle_lift I M P z
    let b : Fin k → J := fun j ↦ ⟨f (a j), by
      rw [hJ]
      exact Ideal.mem_map_of_mem f (a j).property⟩
    have hw : D.iCycles 1 w = φ 1 y ⊗ₜ[A] (1 : A ⧸ J) := by
      rw [← heq, hy]
      simpa only [map_one] using hψ 1 y 1
    have hd : G.complex.d 1 0 (φ 1 y) = ∑ j, (b j : A) • φ 0 (p j) := by
      rw [hdφ 0 y, hdy, map_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ hφ 0 (a j) (p j))
    rw [hformulaA w (φ 1 y) k b (fun j ↦ φ 0 (p j)) hw hd,
      hformulaR z y k a p hy hdy, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hθ (a j) (P.π.f 0 (p j)) (b j) rfl, hπφ]
  obtain ⟨ψ₀, hψ₀, hcycles₀⟩ :=
    exists_quotient_tensor_comparison f I J hJ M N P G φ₀ hφ₀ hdφ₀
  have hrange : ∀ t, ∃ v, δA v = θ (δR t) := by
    intro t
    obtain ⟨z, hz⟩ := (epi_iff_surjective (C.homologyπ 1)).mp inferInstance (eR.hom t)
    have ht : eR.inv (C.homologyπ 1 z) = t := by
      rw [hz]
      exact ConcreteCategory.congr_hom eR.hom_inv_id t
    obtain ⟨w, hw⟩ := hcycles₀ z
    refine ⟨eA.inv (D.homologyπ 1 w), ?_⟩
    rw [← ht]
    exact hlocal φ₀ hφ₀ hdφ₀ hπφ₀ ψ₀ hψ₀ z w hw
  let τ : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))) →+
      (((Tor' (ModuleCat.{u} A) 1).obj N).obj (ModuleCat.of A (A ⧸ J))) :=
    { toFun := fun t ↦ (hrange t).choose
      map_zero' := by
        apply hδA
        simpa only [map_zero] using (hrange 0).choose_spec
      map_add' := by
        intro x y
        apply hδA
        rw [(hrange (x + y)).choose_spec, map_add, map_add, map_add,
          (hrange x).choose_spec, (hrange y).choose_spec] }
  have hcomm : ∀ t, δA (τ t) = θ (δR t) := fun t ↦ (hrange t).choose_spec
  refine ⟨τ, ?_, hcomm⟩
  intro φ hφ hdφ hπφ
  obtain ⟨ψ, hψ, _⟩ := exists_quotient_tensor_comparison f I J hJ M N P G φ hφ hdφ
  refine ⟨ψ, hψ, ?_⟩
  intro z w heq
  apply hδA
  rw [hcomm]
  exact (hlocal φ hφ hdφ hπφ ψ hψ z w heq).symm

end ModuleCat
