/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Derived invariance of Koszul top evaluations

Source: Stacks Project, Tags 0BQY and 0BQZ.
(blueprint: new-q2-koszul-derived-top-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Equal derived maps out of a Koszul complex have top evaluations equal modulo I.
Source: Stacks Project, Tag 0BQZ, the finite-free Koszul resolution computation.
(blueprint: new-q2-koszul-derived-top-evaluation).

Proof: Every exterior-power term has a finite free basis, so the extension by zero
is K-projective. Naturality of quotientCompQhIso transports equality of Q-maps to
Qh. Injectivity of IsKProjective.Qh_map_bijective reflects this to equality in the
homotopy category; homotopyOfEq then produces a homotopy. Its degree -r equation
expresses the difference of top components as the differential followed by the
next homotopy component, since the target single complex has zero differentials.
For r>0, transport through extendXIso: the source differential is Koszul
contraction, whose value on every wedge is a sum with coefficients f_i in I.
Apply the functional and reduce modulo I to kill every summand. For r=0 the
source term in degree 1 is zero, hence the difference is zero. No regularity is
required. For I=A the quotient evaluations are both zero. -/
theorem koszul_derived_top_evaluation_eq
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    (z w : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (heq : DerivedCategory.Q.map z = DerivedCategory.Q.map w) :
    ∀ v : Fin r → (Fin r →₀ A),
      Ideal.Quotient.mk I
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom
          (z.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := r) rfl).inv
              (exteriorPower.ιMulti A r v)))) =
      Ideal.Quotient.mk I
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom
          (w.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := r) rfl).inv
              (exteriorPower.ιMulti A r v)))) := by
  classical
  have (n : ℕ) : Projective ((koszulComplex A r f).X n) := by
    exact ModuleCat.projective_of_free
      ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n)
  let E := (koszulComplex A r f).extend ComplexShape.embeddingDownNat
  let T := (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A)
  have hh : (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).map z =
      (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).map w := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective E
      ((HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).obj T)).injective
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat A)).hom.app T)).mp
    simpa only [T, DerivedCategory.quotientCompQhIso_hom_naturality] using
      congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat A)).hom.app E ≫ k) heq
  let H := HomotopyCategory.homotopyOfEq z w hh
  have hcomponent : z.f (-(r : ℤ)) =
      E.d (-(r : ℤ)) (-(r : ℤ) + 1) ≫ H.hom (-(r : ℤ) + 1) (-(r : ℤ)) +
        w.f (-(r : ℤ)) := by
    have hc := H.comm (-(r : ℤ))
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-(r : ℤ)) (-(r : ℤ) + 1)
      from rfl), prevD_eq H.hom (show (ComplexShape.up ℤ).Rel
        (-(r : ℤ) - 1) (-(r : ℤ)) from by change _ + 1 = _; omega)] at hc
    simpa only [CochainComplex.singleFunctor_obj_d, comp_zero, add_zero] using hc
  intro v
  have hmem :
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
        (ModuleCat.of A A)).hom
        ((E.d (-(r : ℤ)) (-(r : ℤ) + 1) ≫ H.hom (-(r : ℤ) + 1) (-(r : ℤ)))
          (((koszulComplex A r f).extendXIso ComplexShape.embeddingDownNat
            (i := r) rfl).inv (exteriorPower.ιMulti A r v))) ∈ I := by
    cases r with
    | zero =>
      have hz : E.d 0 1 = 0 := by
        exact ((koszulComplex A 0 f).isZero_extend_X ComplexShape.embeddingDownNat 1
          (fun i ↦ by change -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _
      have hzero : E.d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 := hz
      rw [hzero, zero_comp]
      change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A A)).hom (0 : ((CochainComplex.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A A)).X 0) ∈ I
      simpa only [map_zero] using I.zero_mem
    | succ n =>
      let b : (koszulComplex A (n + 1) f).X n ⟶ ModuleCat.of A A :=
        ((koszulComplex A (n + 1) f).extendXIso ComplexShape.embeddingDownNat
          (i := n) (i' := -((n + 1 : ℕ) : ℤ) + 1)
            (by change -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1; omega)).inv ≫
          H.hom (-((n + 1 : ℕ) : ℤ) + 1) (-((n + 1 : ℕ) : ℤ)) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
            (ModuleCat.of A A)).hom
      have hd : E.d (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) =
          ((koszulComplex A (n + 1) f).extendXIso ComplexShape.embeddingDownNat
            (i := n + 1) rfl).hom ≫
          ModuleCat.ofHom (koszulBoundary A (n + 1) f n) ≫
          ((koszulComplex A (n + 1) f).extendXIso ComplexShape.embeddingDownNat
            (i := n) (i' := -((n + 1 : ℕ) : ℤ) + 1)
            (by change -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1; omega)).inv := by
        rw [HomologicalComplex.extend_d_eq (koszulComplex A (n + 1) f)
          ComplexShape.embeddingDownNat (i := n + 1) (j := n)
            (i' := -((n + 1 : ℕ) : ℤ)) (j' := -((n + 1 : ℕ) : ℤ) + 1)
            rfl (by change -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1; omega)]
        have hd' : (koszulComplex A (n + 1) f).d (n + 1) n =
            ModuleCat.ofHom (koszulBoundary A (n + 1) f n) := by
          dsimp only [koszulComplex]
          exact ChainComplex.of_d _ _ n
        rw [hd']
      have ht : ((koszulComplex A (n + 1) f).extendXIso ComplexShape.embeddingDownNat
          (i := n + 1) rfl).inv ≫ E.d (-((n + 1 : ℕ) : ℤ))
            (-((n + 1 : ℕ) : ℤ) + 1) ≫
          H.hom (-((n + 1 : ℕ) : ℤ) + 1) (-((n + 1 : ℕ) : ℤ)) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
            (ModuleCat.of A A)).hom =
          ModuleCat.ofHom (koszulBoundary A (n + 1) f n) ≫ b := by
        rw [hd]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rfl
      change (( ((koszulComplex A (n + 1) f).extendXIso ComplexShape.embeddingDownNat
        (i := n + 1) rfl).inv ≫ E.d _ _ ≫ H.hom _ _ ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) _
            (ModuleCat.of A A)).hom).hom) (exteriorPower.ιMulti A (n + 1) v) ∈ I
      change ( (((koszulComplex A (n + 1) f).extendXIso ComplexShape.embeddingDownNat
        (i := n + 1) (i' := -((n + 1 : ℕ) : ℤ)) rfl).inv ≫
        E.d (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) ≫
        H.hom (-((n + 1 : ℕ) : ℤ) + 1) (-((n + 1 : ℕ) : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
          (ModuleCat.of A A)).hom).hom) (exteriorPower.ιMulti A (n + 1) v) ∈ I
      rw [ht]
      change b.hom (koszulBoundary A (n + 1) f n (exteriorPower.ιMulti A (n + 1) v)) ∈ I
      rw [boundary_wedge, map_sum]
      apply I.sum_mem
      intro i hi
      rw [map_smul, smul_eq_mul]
      apply I.mul_mem_right
      apply I.mul_mem_left
      rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ _
  rw [hcomponent]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]
  rw [ Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_add]


end ExteriorAlgebra
