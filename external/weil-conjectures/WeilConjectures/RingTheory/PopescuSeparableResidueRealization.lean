/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.FieldTheory.Separable

import WeilConjectures.RingTheory.ArtinianSeparableResidueLift
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Etale.Field

/-!
# Realizing a separable residue element in an admissible subalgebra

Source: Stacks Project, Tags 07FH and 07FI, algebraic branch after power extraction.
(blueprint: lem-weil-pbc-popescu-separable-residue-realization).
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra

/-- Realize a specified separable element of the ambient residue field.
Source: Stacks Project, Tags 07FH and 07FI, algebraic case, after choosing a
separable power. No characteristic assumption is needed for this geometric step.

Proof: Use the given residue compatibility and surjectivity of A₀'s residue map
to identify the supplied residue algebra with the canonical one induced by inclusion.
Apply `exists_finiteEtale_artinian_residue_lift` to A₀ → B and β; admissibility
supplies the Artinian and flat hypotheses. This gives a finite étale local Artinian
A₀-algebra D, a flat local map g : D → B factoring inclusion, and d whose image
has residue β. Flat local maps are faithfully flat, hence g is injective. Its
k-algebra image A is isomorphic to D and contains A₀. Transfer finiteness and étaleness
through this isomorphism. Finiteness makes A Artinian and essentially finite type
over A₀, hence essentially finite type over k by composition. The inclusion A → B
is flat because it is g composed with the inverse isomorphism. Étaleness gives
m_A = m_A₀ A; extending this equality to B and using admissibility of A₀ gives
m_A B = m_B. Thus A is admissible. The element corresponding to d has residue β.
The canonical residue algebra of A₀ → A has the required compatibility and k-scalar
tower. The residue extension of a local étale map is separable, hence formally étale.
(blueprint: lem-weil-pbc-popescu-separable-residue-realization). -/
theorem exists_popescu_separable_residue_realization
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [IsArtinianRing B] [IsLocalRing B]
    (A₀ : Subalgebra k B) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible (IsLocalRing.maximalIdeal B))
    [IsLocalHom A₀.val]
    [Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    [IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    (hmap : ∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) (IsLocalRing.residue A₀ a₀) =
        IsLocalRing.residue B (a₀ : B))
    (β : IsLocalRing.ResidueField B) (hβ : IsSeparable (IsLocalRing.ResidueField A₀) β) :
    ∃ (A : Subalgebra k B) (_ : IsLocalRing A), ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible (IsLocalRing.maximalIdeal B) ∧
      ∃ a : A, IsLocalRing.residue B (a : B) = β ∧
        ∃ (alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A)),
          letI := alg
          IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) ∧
          (∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
            (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ a₀) =
              IsLocalRing.residue A (Subalgebra.inclusion hle a₀)) ∧
          Algebra.FormallyEtale (IsLocalRing.ResidueField A₀)
            (IsLocalRing.ResidueField A) := by
  classical
  let : IsLocalHom (algebraMap A₀ B) := ⟨fun a ha ↦ isUnit_of_map_unit A₀.val a ha⟩
  let : IsArtinianRing A₀ := hA₀.1
  let : EssFiniteType k A₀ := hA₀.2.1
  have hflat : (algebraMap A₀ B).Flat := hA₀.2.2.choose_spec.1
  have heq : (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ B) =
      IsLocalRing.maximalIdeal B := hA₀.2.2.choose_spec.2
  have halg : ‹Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)› =
      IsLocalRing.ResidueField.instAlgebra := by
    apply Algebra.algebra_ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A₀) x
    exact hmap a
  have hsep : @IsSeparable (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) _ _ IsLocalRing.ResidueField.instAlgebra β := by
    rw [← halg]
    exact hβ
  obtain ⟨D, hD, hAD, g, hlocal, hart, hbase, hg, het, hfin, hgf, hcomp, d, hd⟩ :=
    exists_finiteEtale_artinian_residue_lift.{v, v, 0} A₀ B hflat β hsep
  let : CommRing D := hD
  let : Algebra A₀ D := hAD
  let : IsLocalRing D := hlocal
  let : IsArtinianRing D := hart
  let : IsLocalHom (algebraMap A₀ D) := hbase
  let : IsLocalHom g := hg
  let : Etale A₀ D := het
  let : Module.Finite A₀ D := hfin
  let : Algebra k D := (algebraMap A₀ D).comp (algebraMap k A₀) |>.toAlgebra
  let : IsScalarTower k A₀ D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let φ : D →ₐ[k] B := ⟨g, fun r ↦ by
    change g (algebraMap A₀ D (algebraMap k A₀ r)) = algebraMap k B r
    exact congrArg (fun f : A₀ →+* B ↦ f (algebraMap k A₀ r)) hcomp⟩
  have hinj : Function.Injective g := by
    let : Algebra D B := g.toAlgebra
    have : Module.Flat D B := hgf
    let : Module.FaithfullyFlat D B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective D B
  let A := φ.range
  let e : D ≃ₐ[k] A := AlgEquiv.ofInjective φ hinj
  let : IsLocalRing A := IsLocalRing.of_surjective' e.toRingHom e.surjective
  let : Algebra A₀ A := ((e.toRingHom).comp (algebraMap A₀ D)).toAlgebra
  let : IsScalarTower k A₀ A := IsScalarTower.of_algebraMap_eq fun r ↦ (e.commutes r).symm
  let e₀ : D ≃ₐ[A₀] A := { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  let : Module.Finite A₀ A := Module.Finite.equiv e₀.toLinearEquiv
  let : IsArtinianRing A := IsArtinianRing.of_finite A₀ A
  let : Etale A₀ A := Etale.of_equiv e₀
  have hle : A₀ ≤ A := by
    intro a ha
    exact ⟨algebraMap A₀ D ⟨a, ha⟩,
      congrArg (fun f : A₀ →+* B ↦ f ⟨a, ha⟩) hcomp⟩
  have hinc : algebraMap A₀ A = (Subalgebra.inclusion hle).toRingHom := by
    ext a
    exact congrArg (fun f : A₀ →+* B ↦ f a) hcomp
  let : IsLocalHom (algebraMap A₀ A) := by
    change IsLocalHom (e.toRingHom.comp (algebraMap A₀ D))
    let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective e.toRingHom e.surjective
    exact RingHom.isLocalHom_comp e.toRingHom (algebraMap A₀ D)
  have hval : A.val.toRingHom.Flat := by
    have hh : A.val.toRingHom = g.comp e.symm.toRingHom := by
      ext a
      exact (congrArg Subtype.val (e.apply_symm_apply a)).symm
    rw [hh]
    exact (RingHom.Flat.of_bijective e.symm.bijective).comp hgf
  have hmax : (IsLocalRing.maximalIdeal A).map A.val.toRingHom =
      IsLocalRing.maximalIdeal B := by
    rw [← FormallyUnramified.map_maximalIdeal (R := A₀) (S := A), Ideal.map_map]
    have hh : A.val.toRingHom.comp (algebraMap A₀ A) = algebraMap A₀ B := by
      rw [hinc]
      rfl
    rw [hh, heq]
  let : EssFiniteType k A := EssFiniteType.comp k A₀ A
  refine ⟨A, inferInstance, hle, ⟨inferInstance, inferInstance,
    ⟨inferInstance, hval, hmax⟩⟩, e d, hd, inferInstance, inferInstance, ?_, ?_⟩
  · intro a
    rw [IsLocalRing.ResidueField.algebraMap_residue, hinc]
    rfl
  · exact FormallyEtale.of_isSeparable _ _


end Algebra
