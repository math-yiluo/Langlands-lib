/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
import WeilConjectures.SixFunctors.Finite.FiniteFieldAbsoluteGalois
import WeilConjectures.RepresentationTheory.DiscreteModule.ProfiniteIntegerSmoothPrimitives

/-!
# Degree two with prime coefficients over a finite field

Source: the finite cyclic quotient argument in `sk-lem-base-field-cd-finite-field`.
(blueprint: lem-sfb-finite-field-prime-degree-two)
-/

@[expose] public section

set_option autoImplicit false

universe w u

namespace DiscreteModule

open CategoryTheory Limits Action

private theorem fixed_of_dense_generator
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (τ : G) (hd : DenseRange (zpowersHom G τ))
    (X : DiscreteModule.{w} G) (x : X.obj.V)
    (hx : (X.obj.ρ τ).asHom.hom x = x) : ∀ g : G, (X.obj.ρ g).asHom.hom x = x := by
  intro g
  let U := X.obj.stabilizer x
  have hU : IsClosed (U : Set G) := U.isClosed_of_isOpen (X.isOpen_stabilizer x)
  exact hd.induction_on g hU (fun z ↦ U.zpow_mem hx z.toAdd)

private theorem H_one_of_generator_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (τ : G) (hd : DenseRange (zpowersHom G τ))
    (X : DiscreteModule.{w} G)
    (hsurj : ∀ x : X.obj.V, ∃ y : X.obj.V, (X.obj.ρ τ).asHom.hom y - y = x) :
    Subsingleton (H G X 1) := by
  change Subsingleton (Abelian.Ext (intTrivial.{w} G) (shortComplex₁.{w} X).X₁ 1)
  rw [subsingleton_ext_one_iff (shortExact₁.{w} X) (subsingleton_H_coind₁.{w} _ 0),
    forall_exists_comp_eq_iff.{w}]
  intro z hz
  obtain ⟨f, rfl⟩ := (QuotientAddGroup.mk_surjective z)
  have hτf : (((coind₁.{w} G).obj X.obj.V).obj.ρ τ).asHom.hom f - f ∈ toCoind₁Range X := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hz τ
  obtain ⟨x, hx⟩ := hτf
  obtain ⟨y, hy⟩ := hsurj x
  let f' : ((coind₁.{w} G).obj X.obj.V).obj.V := f - (toCoind₁ X).hom.hom.hom y
  have hf'τ : (((coind₁.{w} G).obj X.obj.V).obj.ρ τ).asHom.hom f' = f' := by
    have h1 : (((coind₁.{w} G).obj X.obj.V).obj.ρ τ).asHom.hom f =
        f + (toCoind₁ X).hom.hom.hom x := by
      rw [hx]; abel
    simp only [f', map_sub, h1, ← hom_comm_apply, ← hy, map_sub]
    abel
  refine ⟨f', fixed_of_dense_generator τ hd _ f' hf'τ, ?_⟩
  have h0 : (QuotientAddGroup.mk ((toCoind₁ X).hom.hom.hom y) :
      (coker₁ X).obj.V) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨y, rfl⟩
  simp only [shortComplex₁, coker₁π_apply, f', QuotientAddGroup.mk_sub, h0, sub_zero]

private theorem H_two_of_coker_generator_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (τ : G) (hd : DenseRange (zpowersHom G τ))
    (X : DiscreteModule.{w} G)
    (hsurj : ∀ z : (coker₁ X).obj.V,
      ∃ y : (coker₁ X).obj.V, ((coker₁ X).obj.ρ τ).asHom.hom y - y = z) :
    Subsingleton (H G X 2) := by
  exact subsingleton_ext_succ_of_shortExact (shortExact₁ X)
    (subsingleton_H_coind₁ _ 1) (H_one_of_generator_surjective τ hd (coker₁ X) hsurj)

/-- The degree-two continuous cohomology of a finite field with trivial prime
coefficients prime to the characteristic vanishes.

Source: blueprint `sk-lem-base-field-cd-finite-field.proof.md`, paragraphs
Finite modules and Consequences; `lemma-cohomological-dimension-base-field`, clause (3), and
`lemma-cohomological-dimension-base-field--2`, final clause.
(blueprint: lem-sfb-finite-field-prime-degree-two)

Proof: The absolute Galois group of K is the profinite completion of the integers,
with Frobenius corresponding to one. Continuous cochains with the finite trivial
coefficient group Z/ℓ factor through finite cyclic quotients. Their second cohomology
is therefore the filtered colimit of the second cohomology of these quotients along
inflation. A representative at the cyclic quotient of order n becomes zero at the
quotient of order ℓ*n: cyclic inflation in degree two multiplies by ℓ in the periodic
resolution and the coefficient group is killed by ℓ. Every element of the colimit
vanishes. The equivalence of continuous cochain cohomology with Ext from the trivial
integer module gives the stated vanishing. This includes the quotient of order one
and requires no roots of unity in K. The characteristic-primary case is handled
separately by Artin–Schreier in the importing module. -/
theorem subsingleton_H_two_trivialZMod_of_finiteField
    (K Ks : Type u) [Field K] [Finite K] [Field Ks] [Algebra K Ks]
    [IsSepClosure K Ks] (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : K) ≠ 0) :
    Subsingleton (H Gal(Ks/K) (trivialZMod.{u + 1} Gal(Ks/K) ℓ) 2) := by
  -- Implement cyclic refinement by smooth partial sums, then dimension-shift through
  -- the existing coinduced short exact sequence; no cochain/Ext comparison is needed.
  classical
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨τ, _, _, e, he⟩ := finiteField_absoluteGaloisGroup K Ks
  let Z := GrpCat.of (Multiplicative ℤ)
  have heta (z : Multiplicative ℤ) :
      e.symm (ProfiniteGrp.ProfiniteCompletion.etaFn Z z) = τ ^ z.toAdd := by
    apply e.injective
    rw [e.apply_symm_apply, map_zpow, he]
    change (ProfiniteGrp.ProfiniteCompletion.eta Z).hom z =
      (ProfiniteGrp.ProfiniteCompletion.eta Z).hom (.ofAdd (1 : ℤ)) ^ z.toAdd
    rw [← map_zpow]
    exact congrArg (ProfiniteGrp.ProfiniteCompletion.eta Z).hom (by
      apply Multiplicative.toAdd.injective
      change z.toAdd = z.toAdd • (1 : ℤ)
      simp)
  have hd : DenseRange (zpowersHom (Gal(Ks/K)) τ) := by
    have h := e.symm.surjective.denseRange.comp
      (ProfiniteGrp.ProfiniteCompletion.denseRange Z) e.symm.continuous
    convert h using 1
    exact funext fun z ↦ (heta z).symm
  let residue (n : ℕ) (hn : 0 < n) : Gal(Ks/K) →ₜ* Multiplicative (ZMod n) := by
    have : NeZero n := ⟨by omega⟩
    exact (ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of (Multiplicative (ZMod n)))
      (GrpCat.ofHom (Int.castAddHom (ZMod n)).toMultiplicative)).hom.comp
        ⟨e.toMonoidHom, e.continuous⟩
  have hresidue (n : ℕ) (hn : 0 < n) : residue n hn τ = Multiplicative.ofAdd 1 := by
    have : NeZero n := ⟨by omega⟩
    have h : (ProfiniteGrp.ProfiniteCompletion.lift
        (P := ProfiniteGrp.of (Multiplicative (ZMod n)))
        (GrpCat.ofHom (Int.castAddHom (ZMod n)).toMultiplicative)).hom
        (ProfiniteGrp.ProfiniteCompletion.etaFn Z (Multiplicative.ofAdd (1 : ℤ))) =
        Multiplicative.ofAdd (1 : ZMod n) := by
      have h := congrArg (fun f : GrpCat.of (Multiplicative ℤ) ⟶
          GrpCat.of (Multiplicative (ZMod n)) ↦
        f.hom (Multiplicative.ofAdd (1 : ℤ)))
        (ProfiniteGrp.ProfiniteCompletion.lift_eta
          (P := ProfiniteGrp.of (Multiplicative (ZMod n)))
          (GrpCat.ofHom (Int.castAddHom (ZMod n)).toMultiplicative))
      change _ = Multiplicative.ofAdd ((1 : ℤ) : ZMod n) at h
      simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom, MonoidHom.comp_apply,
        Int.cast_one] using! h
    change (ProfiniteGrp.ProfiniteCompletion.lift
      (P := ProfiniteGrp.of (Multiplicative (ZMod n)))
      (GrpCat.ofHom (Int.castAddHom (ZMod n)).toMultiplicative)).hom (e τ) = _
    rw [he]
    exact h
  let X := trivialZMod.{u + 1} Gal(Ks/K) ℓ
  have hsurj (z : (coker₁.{u + 1} X).obj.V) :
      ∃ y : (coker₁.{u + 1} X).obj.V, ((coker₁.{u + 1} X).obj.ρ τ).asHom.hom y - y = z := by
    obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨h, hho, hh⟩ := exists_smooth_primitive_of_cyclic_residues τ hd residue hresidue
      ℓ (Fact.out : ℓ.Prime).one_lt f.1 f.2 (fun x ↦ by
        apply ULift.ext
        change ℓ • (f.1 x).down = 0
        simp [nsmul_eq_mul])
    let h' : ((coind₁.{u + 1} Gal(Ks/K)).obj X.obj.V).obj.V := ⟨h, hho⟩
    refine ⟨QuotientAddGroup.mk h', ?_⟩
    rw [coker₁_ρ_mk, ← QuotientAddGroup.mk_sub]
    congr 1
    exact Subtype.ext (funext hh)
  exact H_two_of_coker_generator_surjective.{u + 1, u} τ hd X hsurj

end DiscreteModule
