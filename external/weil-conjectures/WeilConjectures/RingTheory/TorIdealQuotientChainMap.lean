/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-! # Quotient tensor complexes under a semilinear comparison
Source: Stacks Project, Algebra, Section 00LY and Tag 00M6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, functoriality in Section 00LY and Tag 00M6;
Step 1 of the ideal comparison compatibility argument.
(blueprint: lem-weil-pbc-quotient-tensor-comparison).

Proof in words: the composite of f with A → A/J kills I because J = map f I,
so it descends to an additive semilinear map R/I → A/J. Tensor it with φ in
each degree, using semilinearity in both arguments to verify balancing.
The tensor map sends p ⊗ mk(r) to φ(p) ⊗ mk(f(r)). The chain identity on
consecutive differentials follows from hdφ on pure tensors; for all other
pairs both differentials are zero by the complex shape. Thus these maps form
a morphism of the underlying additive complexes. A chain map sends a cycle
to a cycle: the target differential kills its image by the chain identity.
The kernel universal property of iCycles supplies w and the displayed equality.
The pure tensor formula determines every component, hence ψ uniquely; this
construction chooses no arbitrary mathematical data. No freeness,
augmentation, connecting maps, or homology comparison is used.
-/
theorem exists_quotient_tensor_comparison
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) (J : Ideal A) (hJ : J = Ideal.map f I)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} A)
    (P : ProjectiveResolution M) (G : ProjectiveResolution N)
    (φ : ∀ n : ℕ, (P.complex.X n) →+ (G.complex.X n))
    (hφ : ∀ (n : ℕ) (r : R) (p : P.complex.X n), φ n (r • p) = f r • φ n p)
    (hdφ : ∀ (n : ℕ) (p : P.complex.X (n + 1)),
      G.complex.d (n + 1) n (φ (n + 1) p) = φ n (P.complex.d (n + 1) n p)) :
    ∃ ψ : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex) ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((((tensoringRight (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj G.complex),
      (∀ (n : ℕ) (p : P.complex.X n) (r : R),
        ψ.f n (p ⊗ₜ[R] Ideal.Quotient.mk I r) =
          φ n p ⊗ₜ[A] Ideal.Quotient.mk J (f r)) ∧
      (∀ z : ((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).cycles 1,
        ∃ w : ((((tensoringRight (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj G.complex).cycles 1,
          ψ.f 1 (((((tensoringRight (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z) =
            ((((tensoringRight (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj G.complex).iCycles 1 w) := by
  classical
  let C := (((tensoringRight (ModuleCat.{u} R)).obj
    (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let D := (((tensoringRight (ModuleCat.{u} A)).obj
    (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex
  let q : R ⧸ I →+* A ⧸ J := Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp f) (by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hJ]
    exact Ideal.mem_map_of_mem f hr)
  let qL : (R ⧸ I) →ₛₗ[f] (A ⧸ J) :=
    { __ := q.toAddMonoidHom
      map_smul' := by
        intro r x
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        change q (Ideal.Quotient.mk I (r * s)) =
          Ideal.Quotient.mk J (f r * f s)
        simp [q] }
  let φL (n : ℕ) : (P.complex.X n) →ₛₗ[f] (G.complex.X n) :=
    { __ := φ n
      map_smul' := hφ n }
  let ψ : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj D :=
    { f := fun n ↦ AddCommGrpCat.ofHom (TensorProduct.map (φL n) qL).toAddMonoidHom
      comm' := by
        intro i j hij
        apply AddCommGrpCat.hom_ext
        ext x
        induction x using TensorProduct.inductionOn with
        | tmul p r =>
          change (G.complex.d i j (φ i p)) ⊗ₜ[A] q r =
            (φ j (P.complex.d i j p)) ⊗ₜ[A] q r
          have h : j + 1 = i := hij
          subst i
          rw [hdφ]
        | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy }
  refine ⟨ψ, ?_, ?_⟩
  · intro n p r
    change φ n p ⊗ₜ[A] q (Ideal.Quotient.mk I r) = _
    simp [q]
  · intro z
    let x : D.X 1 := ψ.f 1 (C.iCycles 1 z)
    have hx : D.d 1 0 x = 0 := by
      have h := ConcreteCategory.congr_hom (ψ.comm 1 0) (C.iCycles 1 z)
      change D.d 1 0 x = ψ.f 0 (C.d 1 0 (C.iCycles 1 z)) at h
      rw [h]
      have hz := ConcreteCategory.congr_hom (C.iCycles_d 1 0) z
      change C.d 1 0 (C.iCycles 1 z) = 0 at hz
      rw [hz, map_zero]
    let v : ModuleCat.of A A ⟶ D.X 1 := ofHom (LinearMap.toSpanSingleton A (D.X 1) x)
    have hv : v ≫ D.d 1 0 = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change D.d 1 0 (a • x) = 0
      rw [map_smul, hx, smul_zero]
    let w := D.liftCycles v 0 (by simp) hv
    refine ⟨w 1, ?_⟩
    have hw := ConcreteCategory.congr_hom (D.liftCycles_i v 0 (by simp) hv) 1
    dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    change D.iCycles 1 (w 1) = v 1 at hw
    change x = D.iCycles 1 (w 1)
    exact (show v 1 = x from one_smul A x).symm.trans hw.symm

end ModuleCat
