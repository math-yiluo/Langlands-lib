/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import WeilConjectures.Mathlib.Topology.JacobsonSpace
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

/-!
# The identity component of a closed subgroup of `GL_n`

Let `G = V(I)` be the closed subgroup of `GL_n` over an algebraically closed field `k` cut
out by a Hopf ideal `I`, and let `G° = V(identityComponent I)` be its reduced identity component.
This file proves the structure of `G°`: it is irreducible, normal in `G` (on `R`-points for every
`k`-algebra `R`, when `G` is reduced) and of finite index in `G(k)`; `V(I)` has finitely many
connected components, and they are the cosets `g G°` of the identity component.

The key input is that the translations by `G(k)` act transitively on the closed points of `V(I)`,
so that the irreducible components of `V(I)` are pairwise disjoint
(`Matrix.GeneralLinearGroup.pairwise_disjoint_irreducibleComponents_zeroLocus`), hence equal to
its connected components.

## Main results

- `Matrix.GeneralLinearGroup.isPrime_identityComponent`: `G°` is irreducible.
- `Matrix.GeneralLinearGroup.normal_zeroLocus_identityComponent`: `G°` is normal in `G`.
- `Matrix.GeneralLinearGroup.finiteIndex_zeroLocus_identityComponent`: `G°(k)` has finite index
  in `G(k)`.
- `Matrix.GeneralLinearGroup.toPrimeSpectrum_mem_connectedComponentIn_iff`: the connected
  components of `G` are the cosets of `G°`.
- `Matrix.GeneralLinearGroup.isClopen_connectedComponent_zeroLocus`: the connected components of
  `G` are open and closed.

## Blueprint

- `lemma-connected-components-images-homomorphisms`: structure of the identity component.
- `lemma-connected-components-images-homomorphisms--1`: the identity component, its cosets and the
finite
  component group.
-/

@[expose] public section

open scoped TensorProduct

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k] [IsAlgClosed k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The underlying space of `V(I)` is noetherian. -/
instance : TopologicalSpace.NoetherianSpace
    (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) :=
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  inferInstance

/-- Left translation `x ↦ g * x` by a point `g` of `V(I)`, as a homeomorphism of `V(I)`. -/
noncomputable def zeroLocusTranslate {g : GL n k} (hg : g ∈ zeroLocus I k) :
    PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) ≃ₜ
      PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)) :=
  (translateHomeomorph g 1).subtype fun _ ↦
    (translateHomeomorph_mem_zeroLocus_iff hg (zeroLocus I k).one_mem).symm

/-- The irreducible components of `V(I)` are pairwise disjoint: the translations by points of
`V(I)` act transitively on its closed points, which are the points of `V(I)(k)`. -/
theorem pairwise_disjoint_irreducibleComponents_zeroLocus :
    (irreducibleComponents (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))).Pairwise
      Disjoint := by
  set X := PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))
  have hX : IsClosed X := PrimeSpectrum.isClosed_zeroLocus _
  have : IsJacobsonRing (CoordinateRing n k) := isJacobsonRing_of_finiteType (A := k)
  have : JacobsonSpace X := .of_isClosedEmbedding hX.isClosedEmbedding_subtypeVal
  have hcl (y : X) (hy : y ∈ closedPoints X) :
      ∃ g, ∃ hg : g ∈ zeroLocus I k, (⟨toPrimeSpectrum g, hg⟩ : X) = y := by
    have hy' : IsClosed {(y : PrimeSpectrum (CoordinateRing n k))} := by
      have := hX.isClosedEmbedding_subtypeVal.isClosedMap _ hy
      rwa [Set.image_singleton] at this
    have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hy'
    obtain ⟨g, hg⟩ := exists_ker_evalAlgHom_eq y.1.asIdeal
    have hgy : toPrimeSpectrum g = y := PrimeSpectrum.ext hg
    exact ⟨g, toPrimeSpectrum_mem_zeroLocus_iff.1 (hgy ▸ y.2), Subtype.ext hgy⟩
  refine fun Z₁ hZ₁ Z₂ hZ₂ hne ↦
    disjoint_of_mem_irreducibleComponents_of_forall_closedPoints (fun x hx y hy ↦ ?_) hZ₁ hZ₂ hne
  obtain ⟨g, hg, rfl⟩ := hcl x hx
  obtain ⟨h, hh, rfl⟩ := hcl y hy
  refine ⟨zeroLocusTranslate I ((zeroLocus I k).mul_mem hh ((zeroLocus I k).inv_mem hg)), ?_⟩
  refine Subtype.ext ?_
  change translateHomeomorph _ 1 (toPrimeSpectrum g) = _
  rw [translateHomeomorph_toPrimeSpectrum, mul_one, inv_mul_cancel_right]

/-- The connected component of `V(I)` through a point is an irreducible component. -/
theorem isIrreducible_connectedComponentIn_zeroLocus
    {p : PrimeSpectrum (CoordinateRing n k)}
    (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) :
    IsIrreducible (connectedComponentIn
      (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) p) := by
  rw [connectedComponentIn_eq_image hp,
    TopologicalSpace.NoetherianSpace.connectedComponent_eq_irreducibleComponent
      (pairwise_disjoint_irreducibleComponents_zeroLocus I)]
  exact isIrreducible_irreducibleComponent.image _ continuous_subtype_val.continuousOn

/-- The identity component `G°` of a closed subgroup `G = V(I)` of `GL_n` is irreducible: its
ideal is prime. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem isPrime_identityComponent : (identityComponent I).IsPrime :=
  PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1
    (isIrreducible_connectedComponentIn_zeroLocus I (zeroLocus I k).one_mem)

variable {I} in
/-- The `k`-points of `G°` are stable under conjugation by `G(k)`. -/
theorem mul_mul_inv_mem_zeroLocus_identityComponent {g h : GL n k} (hg : g ∈ zeroLocus I k)
    (hh : h ∈ zeroLocus (identityComponent I) k) :
    g * h * g⁻¹ ∈ zeroLocus (identityComponent I) k := by
  rw [zeroLocus_identityComponent] at hh ⊢
  have h1 := translateHomeomorph_image_connectedComponentIn hg ((zeroLocus I k).inv_mem hg)
    (toPrimeSpectrum_mem_zeroLocus_iff.2 (zeroLocus I k).one_mem)
  rw [translateHomeomorph_toPrimeSpectrum, mul_one, mul_inv_cancel] at h1
  change toPrimeSpectrum (g * h * g⁻¹) ∈ connectedComponentIn
    (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum 1)
  rw [← h1, ← translateHomeomorph_toPrimeSpectrum]
  exact Set.mem_image_of_mem _ hh

/-- The identity component `G°` of a closed reduced subgroup `G = V(I)` of `GL_n` is a normal
subgroup scheme: `G°(R)` is normal in `G(R)` for every `k`-algebra `R`.

The conjugation map `G × G° → G` sends `k`-points into `G°`, and `G × G°` is reduced, so it
factors through `G°`. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem normal_zeroLocus_identityComponent (hI : I.IsRadical) (R : Type*) [CommRing R]
    [Algebra k R] :
    ((zeroLocus (identityComponent I) R).subgroupOf (zeroLocus I R)).Normal := by
  set J := identityComponent I
  suffices ∀ g ∈ zeroLocus I R, ∀ h ∈ zeroLocus J R, g * h * g⁻¹ ∈ zeroLocus J R by
    refine ⟨fun h hh g ↦ ?_⟩
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    exact this g g.2 h hh
  intro g hg h hh
  have : IsReduced (CoordinateRing n k ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).1 hI
  have : IsReduced (CoordinateRing n k ⧸ J) :=
    (Ideal.isRadical_iff_quotient_reduced J).1 (isRadical_identityComponent I)
  set B := (CoordinateRing n k ⧸ I) ⊗[k] (CoordinateRing n k ⧸ J)
  let q₁ := (Algebra.TensorProduct.includeLeft (R := k) (S := k)
    (B := CoordinateRing n k ⧸ J)).comp (Ideal.Quotient.mkₐ k I)
  let q₂ := (Algebra.TensorProduct.includeRight (R := k) (A := CoordinateRing n k ⧸ I)).comp
    (Ideal.Quotient.mkₐ k J)
  let γ₁ : GL n B := map q₁.toRingHom (genericUnit n k)
  let γ₂ : GL n B := map q₂.toRingHom (genericUnit n k)
  -- the universal case
  have key (a : CoordinateRing n k) (ha : a ∈ J) : evalAlgHom (γ₁ * γ₂ * γ₁⁻¹) a = 0 := by
    refine Algebra.TensorProduct.eq_zero_of_forall_lift_algHom_eq_zero k _ _ fun ψ₁ ψ₂ ↦ ?_
    set ψ := Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ ↦ .all _ _)
    rw [← AlgHom.comp_apply, ← evalAlgHom_map, map_mul, map_mul, map_inv]
    refine mul_mul_inv_mem_zeroLocus_identityComponent (fun b hb ↦ ?_) (fun b hb ↦ ?_) a ha
    · rw [evalAlgHom_map, evalAlgHom_map_genericUnit, AlgHom.comp_apply]
      simp [q₁, ψ, Ideal.Quotient.eq_zero_iff_mem.2 hb]
    · rw [evalAlgHom_map, evalAlgHom_map_genericUnit, AlgHom.comp_apply]
      simp [q₂, ψ, (Ideal.Quotient.eq_zero_iff_mem (I := J)).2 hb]
  -- specialization to `(g, h)`
  set φ : B →ₐ[k] R := Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ I (evalAlgHom g) hg)
    (Ideal.Quotient.liftₐ J (evalAlgHom h) hh) (fun _ _ ↦ .all _ _)
  have h₁ : map φ.toRingHom γ₁ = g := evalAlgHom_injective (k := k) <| by
    dsimp only
    rw [evalAlgHom_map, evalAlgHom_map_genericUnit]
    rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeLeft,
      Ideal.Quotient.liftₐ_comp]
  have h₂ : map φ.toRingHom γ₂ = h := evalAlgHom_injective (k := k) <| by
    dsimp only
    rw [evalAlgHom_map, evalAlgHom_map_genericUnit]
    rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeRight',
      Ideal.Quotient.liftₐ_comp]
  intro a ha
  rw [← h₁, ← h₂, ← map_inv, ← map_mul, ← map_mul, evalAlgHom_map, AlgHom.comp_apply, key a ha,
    map_zero]

omit [IsAlgClosed k] [I.IsHopfIdeal k] in
/-- A closed subgroup `G = V(I)` of `GL_n` has finitely many connected components.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem finite_connectedComponents_zeroLocus :
    Finite (_root_.ConnectedComponents
      (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))) :=
  inferInstance


/-- The connected components of a closed subgroup `G = V(I)` of `GL_n` are the cosets of the
identity component: a point `x` of `G` lies in the connected component of `g ∈ G` if and only if
`g⁻¹ * x ∈ G°`. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem toPrimeSpectrum_mem_connectedComponentIn_iff {g x : GL n k} (hg : g ∈ zeroLocus I k) :
    toPrimeSpectrum x ∈ connectedComponentIn
        (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum g) ↔
      g⁻¹ * x ∈ zeroLocus (identityComponent I) k := by
  rw [zeroLocus_identityComponent]
  change _ ↔ toPrimeSpectrum (g⁻¹ * x) ∈ connectedComponentIn
    (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) (toPrimeSpectrum 1)
  have h := translateHomeomorph_image_connectedComponentIn ((zeroLocus I k).inv_mem hg)
    (zeroLocus I k).one_mem (toPrimeSpectrum_mem_zeroLocus_iff.2 hg)
  rw [translateHomeomorph_toPrimeSpectrum, mul_one, inv_mul_cancel] at h
  rw [← h, ← mul_one (g⁻¹ * x), ← translateHomeomorph_toPrimeSpectrum,
    (translateHomeomorph _ _).injective.mem_set_image]

/-- The identity component `G°` of a closed subgroup `G = V(I)` of `GL_n` has finite index in `G`.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem finiteIndex_zeroLocus_identityComponent :
    ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).FiniteIndex := by
  set X := PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))
  set H := (zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)
  let f (g : zeroLocus I k) : _root_.ConnectedComponents X :=
    ConnectedComponents.mk ⟨toPrimeSpectrum (g : GL n k), toPrimeSpectrum_mem_zeroLocus_iff.2 g.2⟩
  have hf (g h : zeroLocus I k) : f g = f h ↔ g⁻¹ * h ∈ H := by
    rw [eq_comm, ConnectedComponents.coe_eq_coe', Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv, ← toPrimeSpectrum_mem_connectedComponentIn_iff I g.2,
      connectedComponentIn_eq_image (toPrimeSpectrum_mem_zeroLocus_iff.2 g.2)]
    exact (Subtype.val_injective.mem_set_image (a := (⟨_, _⟩ : X))).symm
  have : Finite (zeroLocus I k ⧸ H) := Finite.of_injective
    (Quotient.lift f fun a b hab ↦ (hf a b).2 (QuotientGroup.leftRel_apply.1 hab))
    fun x y ↦ Quotient.inductionOn₂ x y fun a b hab ↦
      Quotient.sound (QuotientGroup.leftRel_apply.2 ((hf a b).1 hab))
  exact Subgroup.finiteIndex_of_finite_quotient

omit [IsAlgClosed k] [I.IsHopfIdeal k] in
/-- **Identity component and cosets.** The connected component of a point `g` of a closed subgroup
`G = V(I)` of `GL_n` is open and closed in `G`, and it is the coset `g G°`: its points are the `x`
with `g⁻¹ * x ∈ G°` (`toPrimeSpectrum_mem_connectedComponentIn_iff`). There are finitely many of
them (`finite_connectedComponents_zeroLocus`, `finiteIndex_zeroLocus_identityComponent`), and `G°`
is normal (`normal_zeroLocus_identityComponent`), so that `G(k) ⧸ G°(k)` is a finite group.
(blueprint: `lemma-connected-components-images-homomorphisms--1`) -/
theorem isClopen_connectedComponent_zeroLocus
    (p : PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k))) :
    IsClopen (connectedComponent p) :=
  ⟨isClosed_connectedComponent, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent p⟩


end Matrix.GeneralLinearGroup
