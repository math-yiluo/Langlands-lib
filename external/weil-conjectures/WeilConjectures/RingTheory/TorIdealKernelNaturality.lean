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
import WeilConjectures.AlgebraicGeometry.FreeComplexMapsToResolution
import WeilConjectures.RingTheory.TorIdealConnectingFormula
import WeilConjectures.RingTheory.TorIdealComparisonCompatibility
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Naturality of the ideal-kernel description of first Tor

Source: Stacks Project, Algebra, Tags 00M6, 00M5, 00MO and 00LS
(blueprint: lem-weil-pbc-tor-ideal-kernel-naturality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators

namespace ModuleCat

/-- Stacks Project, Algebra, Tag 00M6 and the change-of-rings functoriality used in Tag 00MO
(blueprint: lem-weil-pbc-tor-ideal-kernel-naturality).

The maps `μR`, `μA` and `θ` are specified on pure tensors. The two connecting maps are
injective with precisely the multiplication kernels as images. Their values on cycles are
specified for every lift and every finite expression of its differential. The same `τ` is
induced by every semilinear comparison of the resolutions; thus it is independent of that
comparison. Tensor quotient generators `p ⊗ 1` represent `p mod IP`, so the condition on
`ψ` is exactly the induced quotient chain map. Its action on cycle classes specifies its
map on first homology, using `ProjectiveResolution.isoLeftDerivedObj` to identify Tor.

Proof:
1. Free terms are projective (`lem-weil-pbc-free-module-projective`) and flat
   (`lem-weil-pbc-projective-module-flat`). Flat tensor exactness and tensor right
   exactness (`lem-weil-pbc-flat-tensor-exact`, `lem-weil-pbc-tensor-right-exact`) give
   the degreewise exact rows obtained by tensoring `0 → I → R → R/I → 0`, and likewise
   over `A`, with the resolutions. The ideal-tensor terms identify with `IP` and `JG`.
2. Tensor right exactness identifies the two degree-zero cokernels with `I ⊗ M` and
   `M`; under these identifications the induced map is multiplication. Likewise for `A`.
3. Apply `lem-weil-pbc-snake-lemma-modules` to consecutive degrees. Exactness of the
   resolution identifies the kernel of the connecting map on cycles with boundaries.
   It therefore descends injectively to first homology with image the multiplication
   kernel. The snake formula gives the displayed finite-sum formula, independently of
   both choices. Use `def-weil-pbc-tor-modules` to identify first homology with Tor.
4. Restrict the scalars of the `A`-resolution along `f` and apply
   `lem-weil-pbc-free-complex-maps-to-resolution` to lift `g` to the semilinear maps `φ`.
5. Semilinearity sends `IP` into `JG`, giving the quotient chain map `ψ`. On ideal
   tensors the comparison sends `p ⊗ a` to `φ(p) ⊗ f(a)` and commutes with both
   multiplication and the differentials; its degree-zero cokernel map is `θ`.
6. A lift of a cycle and an ideal-tensor expression of its differential map to valid
   choices on the `A` side. Choice independence in the snake formula gives
   `δA ∘ τ = θ ∘ δR`. Injectivity and the image identifications show that `θ` carries
   kernels into kernels and `τ` is its restriction under those identifications.
   This formula and injectivity of `δA` give independence of the comparison `φ`.
-/
theorem exists_tor_ideal_kernel_naturality
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) (J : Ideal A) (hJ : J = Ideal.map f I)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} A)
    (g : M →+ N) (hg : ∀ (r : R) (x : M), g (r • x) = f r • g x)
    (P : ProjectiveResolution M) (G : ProjectiveResolution N)
    (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    (hG : ∀ n : ℕ, Module.Free A (G.complex.X n)) :
    ∃ (μR : (I ⊗[R] M) →ₗ[R] M) (μA : (J ⊗[A] N) →ₗ[A] N)
      (θ : (I ⊗[R] M) →+ (J ⊗[A] N))
      (δR : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))) →ₗ[R] (I ⊗[R] M))
      (δA : (((Tor' (ModuleCat.{u} A) 1).obj N).obj (ModuleCat.of A (A ⧸ J))) →ₗ[A] (J ⊗[A] N))
      (τ : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))) →+ (((Tor'
        (ModuleCat.{u} A) 1).obj N).obj (ModuleCat.of A (A ⧸ J)))),
      (∀ (a : I) (x : M), μR (a ⊗ₜ[R] x) = (a : R) • x) ∧
      (∀ (b : J) (y : N), μA (b ⊗ₜ[A] y) = (b : A) • y) ∧
      (∀ (a : I) (x : M) (b : J), (b : A) = f a →
        θ (a ⊗ₜ[R] x) = b ⊗ₜ[A] g x) ∧
      Function.Injective δR ∧ LinearMap.range δR = LinearMap.ker μR ∧
      Function.Injective δA ∧ LinearMap.range δA = LinearMap.ker μA ∧
      (∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δR ((P.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I)))
          1).inv (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
          I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z)) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) ∧
      (∀ (z : ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
        J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).cycles 1)
        (y : G.complex.X 1) (k : ℕ) (b : Fin k → J) (p : Fin k → G.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj G.complex).iCycles 1 z = y ⊗ₜ[A] (1 : A ⧸ J) →
        G.complex.d 1 0 y = ∑ j, (b j : A) • p j →
        δA ((G.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J)))
          1).inv (((((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸
          J))).mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex).homologyπ 1 z)) =
          ∑ j, b j ⊗ₜ[A] G.π.f 0 (p j)) ∧
      (∃ φ : ∀ n : ℕ, (P.complex.X n) →+ (G.complex.X n),
        (∀ (n : ℕ) (r : R) (p : P.complex.X n), φ n (r • p) = f r • φ n p) ∧
        (∀ (n : ℕ) (p : P.complex.X (n + 1)),
          G.complex.d (n + 1) n (φ (n + 1) p) = φ n (P.complex.d (n + 1) n p)) ∧
        (∀ p : P.complex.X 0, G.π.f 0 (φ 0 p) = g (P.π.f 0 p))) ∧
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
      (∀ t : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))), δA (τ t) = θ (δR t))
        ∧
      (∀ x : I ⊗[R] M, x ∈ LinearMap.ker μR → θ x ∈ LinearMap.ker μA) := by
  let μR : (I ⊗[R] M) →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let μA : (J ⊗[A] N) →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)
  have hμR (a : I) (x : M) : μR (a ⊗ₜ[R] x) = (a : R) • x := rfl
  have hμA (b : J) (y : N) : μA (b ⊗ₜ[A] y) = (b : A) • y := rfl
  let fi : I →ₛₗ[f] J :=
    { toFun := fun a => ⟨f a, hJ ▸ Ideal.mem_map_of_mem f a.property⟩
      map_add' := fun a b => Subtype.ext (f.map_add a b)
      map_smul' := fun r a => Subtype.ext (f.map_mul r a) }
  let gl : M →ₛₗ[f] N := { g with map_smul' := hg }
  let θ : (I ⊗[R] M) →+ (J ⊗[A] N) := (TensorProduct.map fi gl).toAddMonoidHom
  have hθ (a : I) (x : M) (b : J) (hb : (b : A) = f a) :
      θ (a ⊗ₜ[R] x) = b ⊗ₜ[A] g x := by
    change fi a ⊗ₜ[A] g x = b ⊗ₜ[A] g x
    have hab : fi a = b := Subtype.ext hb.symm
    rw [hab]
  obtain ⟨δR, hiR, hrR, hfR⟩ := exists_tor_ideal_connecting_formula I M P hP μR hμR
  obtain ⟨δA, hiA, hrA, hfA⟩ := exists_tor_ideal_connecting_formula J N G hG μA hμA
  have hlift : ∃ φ : ∀ n : ℕ, (P.complex.X n) →+ (G.complex.X n),
      (∀ (n : ℕ) (r : R) (p : P.complex.X n), φ n (r • p) = f r • φ n p) ∧
      (∀ (n : ℕ) (p : P.complex.X (n + 1)),
        G.complex.d (n + 1) n (φ (n + 1) p) = φ n (P.complex.d (n + 1) n p)) ∧
      (∀ p : P.complex.X 0, G.π.f 0 (φ 0 p) = g (P.π.f 0 p)) := by
    let S := restrictScalars f
    let γ : M ⟶ S.obj N := ofHom (X := M) (Y := S.obj N)
      { toFun := fun x => g x
        map_add' := g.map_add
        map_smul' := hg }
    let d : ∀ n : ℕ, S.obj (G.complex.X (n + 1)) ⟶ S.obj (G.complex.X n) :=
      fun n => S.map (G.complex.d (n + 1) n)
    let η := S.map (G.π.f 0)
    have hd0 : d 0 ≫ η = 0 := by
      change S.map (G.complex.d 1 0) ≫ S.map (G.π.f 0) = 0
      rw [← S.map_comp, G.complex_d_comp_π_f_zero, S.map_zero]
    have hd (n : ℕ) : d (n + 1) ≫ d n = 0 := by
      change S.map (G.complex.d (n + 2) (n + 1)) ≫
        S.map (G.complex.d (n + 1) n) = 0
      rw [← S.map_comp, G.complex.d_comp_d, S.map_zero]
    have hη : Function.Surjective η := by
      exact (epi_iff_surjective (G.π.f 0)).mp inferInstance
    have hex0 : (ShortComplex.mk (d 0) η hd0).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      exact (ShortComplex.moduleCat_exact_iff
        (ShortComplex.mk _ _ G.complex_d_comp_π_f_zero)).mp G.exact₀
    have hex (n : ℕ) : (ShortComplex.mk (d (n + 1)) (d n) (hd n)).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      exact (ShortComplex.moduleCat_exact_iff
        (ShortComplex.mk _ _ (G.complex.d_comp_d (n + 2) (n + 1) n))).mp (G.exact_succ n)
    obtain ⟨α, hα₀, hα⟩ := free_complex_maps_to_resolution R M (S.obj N) γ
      (fun n => S.obj (G.complex.X n)) d η hd0 hd hη hex0 hex
      (fun n => P.complex.X n) (fun n => P.complex.d (n + 1) n) (P.π.f 0)
      P.complex_d_comp_π_f_zero (fun n => P.complex.d_comp_d (n + 2) (n + 1) n) hP
    refine ⟨fun n => (α n).hom.toAddMonoidHom, ?_, ?_, ?_⟩
    · intro n r p
      exact (α n).hom.map_smul r p
    · intro n p
      exact congrArg (fun k => k p) (hα n)
    · intro p
      exact congrArg (fun k => k p) hα₀
  obtain ⟨φ, hφ, hdφ, hπφ⟩ := hlift
  obtain ⟨τ, hτ, hcomm⟩ := exists_tor_ideal_comparison_compatibility f I J hJ M N g hg
    P G hP hG δR δA θ hθ hiA hfR hfA φ hφ hdφ hπφ
  refine ⟨μR, μA, θ, δR, δA, τ, hμR, hμA, hθ, hiR, hrR, hiA, hrA, hfR, hfA,
    ⟨φ, hφ, hdφ, hπφ⟩, hτ, hcomm, ?_⟩
  intro x hx
  rw [← hrR] at hx
  obtain ⟨t, rfl⟩ := hx
  rw [← hcomm, ← hrA]
  exact ⟨τ t, rfl⟩

end ModuleCat
