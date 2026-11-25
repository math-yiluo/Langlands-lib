/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.DenseOpen
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# Extending locally finite `ℓ`-adic functions over a dense open

Let `e : T' ⟶ T` be an open embedding of topological spaces. Suppose that every point of `T` is
a specialization of a point of the image of `e`, that any two generizations of a point of `T`
have a common generization, that closures of relatively clopen subsets of the image are
detected by specializations, and that `T` is covered by opens whose preimages in `T'` are
compact. Then restriction along `e` is a bijection between the locally finite continuous
`ℓ`-adic functions on `T` and on `T'`
(`PadicAlgCl.bijective_locallyFiniteFunctionsComp_of_isOpenEmbedding`).

Uniqueness holds because continuous functions to the Hausdorff space `ℚ̄_ℓ` are constant along
specializations. The extension of `g` takes at `x` the value of `g` at any generization of `x`
in `T'`, which is well defined by the second hypothesis. It is continuous since the
`ℓ`-adic balls are clopen, `ℚ̄_ℓ` being ultrametric: the points of `T'` at which `g` is far
from its value at `x` form a relatively clopen set whose closure does not contain `x`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']

/-- The values of a locally finite function on a compact set span a finite-dimensional
`ℚ_ℓ`-subspace. -/
lemma finiteDimensional_span_image_of_isCompact {f : C(T, PadicAlgCl l)}
    (hf : f ∈ locallyFiniteFunctions l T) {K : Set T} (hK : IsCompact K) :
    FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' K)) := by
  choose U hU hfin using hf
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover U (fun x _ ↦ hU x)
  refine Submodule.finiteDimensional_of_le (S₂ := t.sup fun x ↦ Submodule.span ℚ_[l] (f '' U x))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact Finset.le_sup (f := fun x ↦ Submodule.span ℚ_[l] (f '' U x)) hx
    (Submodule.subset_span ⟨y, hyx, rfl⟩)

omit [TopologicalSpace T'] in
/-- Two continuous `ℓ`-adic functions agreeing on a set of points which generize every point
agree. -/
lemma eq_of_comp_eq_of_forall_specializes {e : T' → T}
    (hgen : ∀ x : T, ∃ y : T', e y ⤳ x) {f₁ f₂ : C(T, PadicAlgCl l)}
    (h : ∀ y, f₁ (e y) = f₂ (e y)) : f₁ = f₂ := by
  ext x
  obtain ⟨y, hy⟩ := hgen x
  rw [← (hy.map f₁.continuous).eq, ← (hy.map f₂.continuous).eq, h]

/-- **Extension of locally finite functions over a dense open.** Let `e : T' ⟶ T` be an open
embedding such that
- every point of `T` is a specialization of a point of the image of `e`;
- any two generizations of a point of `T` have a common generization;
- a point in the closure of the image of a clopen subset `B` of `T'` is a specialization of a
  point of the image of `B`;
- every point of `T` has an open neighbourhood with compact preimage in `T'`.

Then restriction along `e` is a bijection on locally finite continuous `ℓ`-adic functions. -/
theorem bijective_locallyFiniteFunctionsComp_of_isOpenEmbedding (e : C(T', T))
    (he : IsOpenEmbedding e) (hgen : ∀ x : T, ∃ y : T', e y ⤳ x)
    (hdir : ∀ x y₁ y₂ : T, y₁ ⤳ x → y₂ ⤳ x → ∃ z, z ⤳ y₁ ∧ z ⤳ y₂)
    (hcl : ∀ B : Set T', IsClopen B → ∀ x ∈ closure (e '' B), ∃ b ∈ B, e b ⤳ x)
    (hfin : ∀ x : T, ∃ N : Set T, IsOpen N ∧ x ∈ N ∧ IsCompact (e ⁻¹' N)) :
    Function.Bijective (locallyFiniteFunctionsComp l e) := by
  refine ⟨fun f₁ f₂ h ↦ Subtype.ext (eq_of_comp_eq_of_forall_specializes hgen fun y ↦ ?_),
    fun g ↦ ?_⟩
  · exact congrArg (fun f : locallyFiniteFunctions l T' ↦ f.1 y) h
  choose y hy using hgen
  -- `g` is constant on the generizations of a point lying in `T'`
  have key (x : T) (b : T') (hb : e b ⤳ x) : g.1 b = g.1 (y x) := by
    obtain ⟨z, hz₁, hz₂⟩ := hdir x (e b) (e (y x)) hb (hy x)
    obtain ⟨z', rfl⟩ := hz₁.mem_open he.isOpen_range ⟨b, rfl⟩
    rw [he.isInducing.specializes_iff] at hz₁ hz₂
    rw [← (hz₁.map g.1.continuous).eq, ← (hz₂.map g.1.continuous).eq]
  let G : T → PadicAlgCl l := fun x ↦ g.1 (y x)
  have hG : Continuous G := by
    refine continuous_iff_continuousAt.2 fun x ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    let B : Set T' := g.1 ⁻¹' (Metric.ball (G x) ε)ᶜ
    have hB : IsClopen B := (IsUltrametricDist.isClopen_ball (G x) ε).compl.preimage g.1.continuous
    have hx : x ∉ closure (e '' B) := fun hx ↦ by
      obtain ⟨b, hb, hbx⟩ := hcl B hB x hx
      exact hb (by rw [key x b hbx]; exact Metric.mem_ball_self hε)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with z hz
    by_contra hzB
    exact hz (closure_mono (s := {e (y z)})
      (Set.singleton_subset_iff.2 (⟨y z, hzB, rfl⟩ : e (y z) ∈ e '' B))
      (specializes_iff_mem_closure.1 (hy z)))
  refine ⟨⟨⟨G, hG⟩, fun x ↦ ?_⟩, Subtype.ext (ContinuousMap.ext fun b ↦ (key (e b) b le_rfl).symm)⟩
  obtain ⟨N, hN, hxN, hNc⟩ := hfin x
  have := finiteDimensional_span_image_of_isCompact g.2 hNc
  refine ⟨N, hN.mem_nhds hxN, Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[l] (g.1 '' (e ⁻¹' N))) (Submodule.span_mono ?_)⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨y z, (hy z).mem_open hN hz, rfl⟩

end PadicAlgCl

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime]

/-- For a quasi-compact open immersion `j` into `C` and any morphism `f : W ⟶ C`, the preimage
of the range of `j` meets every affine open of `W` in a quasi-compact set. -/
lemma isCompact_preimage_range_inter_of_isAffineOpen {W C U : Scheme.{u}} (f : W ⟶ C)
    (j : U ⟶ C) [QuasiCompact j] {N : W.Opens} (hN : IsAffineOpen N) :
    IsCompact (f ⁻¹' Set.range j ∩ N) := by
  have h := ((pullback.fst f j).isCompact_preimage (U := N) hN.isCompact).image
    (pullback.fst f j).continuous
  change IsCompact (pullback.fst f j '' (pullback.fst f j ⁻¹' (N : Set W))) at h
  rwa [Set.image_preimage_eq_inter_range, Scheme.Pullback.range_fst, Set.inter_comm] at h

/-- **Locally finite functions extend uniquely over the preimage of a dense open.** Let
`f : W ⟶ C` be flat with integral local rings on `W`, `j : U ⟶ C` a quasi-compact open immersion
with dense image and `ι : W' ⟶ W` an open immersion onto `f⁻¹(j(U))`. Then restriction along `ι`
is a bijection on locally finite continuous `ℓ`-adic functions.

Every point of `W` generizes into `W'`, the open `j(U)` being dense and quasi-compact and `f`
lifting generizations; the generizations of a point have a common generization, the local
rings being domains; and closures of quasi-compact opens in affine opens are detected by
specializations (`AlgebraicGeometry.Scheme.exists_specializes_of_mem_closure`). -/
theorem bijective_locallyFiniteFunctionsComp_of_isOpenImmersion {W W' C U : Scheme.{u}}
    (f : W ⟶ C) [Flat f] (hW : ∀ w : W, IsDomain (W.presheaf.stalk w)) (j : U ⟶ C)
    [IsOpenImmersion j] [QuasiCompact j] (hj : Dense (Set.range j)) (ι : W' ⟶ W)
    [IsOpenImmersion ι] (hι : Set.range ι = f ⁻¹' Set.range j) :
    Function.Bijective (PadicAlgCl.locallyFiniteFunctionsComp l ι.base.hom) := by
  have he : IsOpenEmbedding ι := ι.isOpenEmbedding
  -- the preimages in `W'` of affine opens of `W` are quasi-compact
  have hcpt {N : W.Opens} (hN : IsAffineOpen N) : IsCompact (ι ⁻¹' N) := by
    rw [he.isInducing.isCompact_iff, Set.image_preimage_eq_inter_range, hι, Set.inter_comm]
    exact isCompact_preimage_range_inter_of_isAffineOpen f j hN
  have haff (x : W) : ∃ N : W.Opens, IsAffineOpen N ∧ x ∈ N := by
    obtain ⟨_, ⟨N, hN, rfl⟩, hxN, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨N, hN, hxN⟩
  refine PadicAlgCl.bijective_locallyFiniteFunctionsComp_of_isOpenEmbedding _ he
    (fun x ↦ ?_) (fun x y₁ y₂ h₁ h₂ ↦
      Scheme.exists_specializes_and_specializes_of_isDomain_stalk (hW x) h₁ h₂)
    (fun B hB x hx ↦ ?_) (fun x ↦ ?_)
  · -- every point of `W` generizes into `W'`
    obtain ⟨_, ⟨N, hN, rfl⟩, hxN, -⟩ :=
      C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    have hc : IsCompact (Set.range j ∩ N) := by
      have h := (j.isCompact_preimage (U := N) hN.isCompact).image j.continuous
      change IsCompact (j '' (j ⁻¹' (N : Set C))) at h
      rwa [Set.image_preimage_eq_inter_range, Set.inter_comm] at h
    obtain ⟨u, hu, hux⟩ := Scheme.exists_specializes_of_mem_closure
      j.isOpenEmbedding.isOpen_range hN hxN hc (hj.closure_eq ▸ Set.mem_univ _)
    obtain ⟨x', hx'x, rfl⟩ := Flat.generalizingMap f hux
    obtain ⟨y, rfl⟩ : x' ∈ Set.range ι := by rw [hι]; exact hu
    exact ⟨y, hx'x⟩
  · obtain ⟨N, hN, hxN⟩ := haff x
    have hc : IsCompact (ι '' B ∩ N) := by
      rw [← Set.image_inter_preimage]
      exact ((hcpt hN).inter_left hB.isClosed).image ι.continuous
    obtain ⟨_, ⟨b, hb, rfl⟩, hbx⟩ :=
      Scheme.exists_specializes_of_mem_closure (he.isOpenMap B hB.isOpen) hN hxN hc hx
    exact ⟨b, hb, hbx⟩
  · obtain ⟨N, hN, hxN⟩ := haff x
    exact ⟨N, N.isOpen, hxN, hcpt hN⟩

end AlgebraicGeometry
