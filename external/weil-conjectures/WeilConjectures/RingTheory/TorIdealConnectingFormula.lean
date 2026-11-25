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
import WeilConjectures.RingTheory.TorIdealHomologyFormula
import WeilConjectures.RingTheory.TorIdealHomologyExactness

/-! # The ideal connecting map for first Tor
Source: Stacks Project, Algebra, Tags 00M5 and 00M6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6
(blueprint: lem-weil-pbc-tor-ideal-connecting-formula).

Proof in words: tensor `0 → I → R → R/I → 0` with each free resolution term.
Flatness makes the ideal inclusion injective, and right exactness identifies the
quotient with the tensor by `R/I`. The snake lemma in degrees one and zero sends
an input cycle, lifted to `y`, to the class of an ideal tensor preimage of `d y`.
Tensor right exactness identifies the degree-zero cokernel of the ideal-tensor
complex with `I ⊗ M`; its map to the degree-zero cokernel of the original complex
is `μ`, by the specified formula on pure tensors. Exactness of the resolution in
degree one identifies the kernel of the snake map with boundaries. Descending to
homology is therefore injective, with range `ker μ`. Transport along
`P.isoLeftDerivedObj` identifies this homology with Tor. An ideal tensor preimage
of `d y = ∑ a j • p j` is `∑ p j ⊗ a j`, which gives the stated value after
symmetry and augmentation. Independence of both choices is the snake lemma's
well-definedness. This includes the zero ideal, unit ideal, and zero module.
-/
theorem exists_tor_ideal_connecting_formula
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    (μR : (I ⊗[R] M) →ₗ[R] M)
    (hμR : ∀ (a : I) (x : M), μR (a ⊗ₜ[R] x) = (a : R) • x) :
    ∃ δR : (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I)))
      →ₗ[R] (I ⊗[R] M),
      Function.Injective δR ∧ LinearMap.range δR = LinearMap.ker μR ∧
      (∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δR ((P.isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I)))
          1).inv (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
          I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z)) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) := by
  obtain ⟨δH, hδH⟩ := exists_tor_ideal_homology_formula I M P hP
  obtain ⟨hiH, hrH⟩ := tor_ideal_homology_exactness I M P hP μR hμR δH hδH
  let e := P.isoLeftDerivedObj
    ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))) 1
  let δR := δH.comp e.hom.hom
  refine ⟨δR, ?_, ?_, ?_⟩
  · exact hiH.comp ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)
  · change LinearMap.range (δH.comp e.hom.hom) = LinearMap.ker μR
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr
      ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance), Submodule.map_top, hrH]
  · intro z y k a p hz hy
    change δH (e.hom (e.inv (_))) = _
    simpa only [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply] using
      hδH z y k a p hz hy

end ModuleCat
