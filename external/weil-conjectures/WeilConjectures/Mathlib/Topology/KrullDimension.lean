/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Topological Krull dimension: open covers and complements of dense opens

In a quasi-sober `T₀` space, the coheight of a point is bounded by the topological Krull
dimension, and the topological Krull dimension is bounded by any common bound on the
dimensions of the members of an open cover. In an irreducible `T₀` space of dimension at most
one, every point outside a nonempty open subset is closed; if the space is moreover quasi-sober
and noetherian, there are only finitely many such points.

## Main definitions

- `topologicalKrullDimAt`: the local dimension `dim_x X` of a space at a point, the infimum of
  the dimensions of the open neighbourhoods of the point.

## Main statements

- `coheight_le_topologicalKrullDim`: the coheight of a point for the specialization order is
  at most the topological Krull dimension.
- `topologicalKrullDim_le_of_iSup_eq_top`: the topological Krull dimension is at most any
  common bound on the dimensions of the members of an open cover.
- `IsOpen.finite_compl_of_topologicalKrullDim_le_one`: the complement of a nonempty open subset
  is finite.
- `IsOpen.isClosed_singleton_of_mem_compl`: each point of that complement is closed.
- `IsOpen.topologicalKrullDimAt_eq`: the local dimension at a point of an open subset agrees
  with the local dimension in the ambient space.
- `topologicalKrullDim_le_of_specializingMap`, `topologicalKrullDim_le_of_continuous`: comparison
  of the dimensions of two sober spaces along a specializing surjection, respectively along a
  continuous map that is injective on specializations.
- `topologicalKrullDim_lt_of_forall_exists_specializes`: a closed subset all of whose points
  generalize outside it inside a closed `Z` has dimension smaller than `Z`.
- `IsClosed.finite_setOf_maximal_specializes`, `IsClosed.exists_maximal_specializes`: a closed
  subset of a noetherian space has finitely many maximal points, which generalize all its points.
- `exists_specializes_ne_le_topologicalKrullDim_closure`: in a space of dimension at least
  `d + 1`, a proper specialization of the generic point whose closure has dimension at least `d`.
- `exists_le_topologicalKrullDim_closure_singleton`: in a space of dimension at least `d`, a
  point whose closure has dimension at least `d`.
- `Topology.IsEmbedding.topologicalKrullDim_eq_range`: an embedding preserves dimension onto its
  range.
-/

@[expose] public section

open Topology TopologicalSpace Order

attribute [local instance] specializationOrder in
/-- In a quasi-sober `T₀` space, the coheight of a point for the specialization order is at
most the topological Krull dimension. -/
theorem coheight_le_topologicalKrullDim {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] (x : X) : (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [← coheight_orderIso irreducibleSetEquivPoints.symm]
  exact coheight_le_krullDim _

attribute [local instance] specializationOrder in
/-- The topological Krull dimension of a quasi-sober `T₀` space is bounded by any common
bound on the dimensions of the members of an open cover. -/
theorem topologicalKrullDim_le_of_iSup_eq_top {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {ι : Type*} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) (n : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (U i) ≤ n) : topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, krullDim_eq_iSup_coheight]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ (irreducibleSetEquivPoints Z)))
  have := (U i).isOpenEmbedding'.quasiSober
  rw [← coheight_orderIso irreducibleSetEquivPoints Z]
  exact (congrArg _ ((U i).isOpenEmbedding'.coheight_eq (x := (⟨_, hi⟩ : U i)))).trans_le
    ((coheight_le_topologicalKrullDim _).trans (h i))

section

variable {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] [T0Space X]

/-- In an irreducible `T₀` space of dimension at most one, every point outside a
nonempty open subset `U` is closed: it is not the generic point, so a proper specialization of it
would give a chain of three irreducible closed subsets. -/
theorem IsOpen.isClosed_singleton_of_mem_compl (h : topologicalKrullDim X ≤ 1) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) {x : X} (hx : x ∉ U) : IsClosed {x} := by
  obtain ⟨u, hu⟩ := hne
  by_contra hcl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure {x}, y ≠ x := by
    by_contra! H
    exact hcl (closure_subset_iff_isClosed.mp fun y hy ↦ H y hy)
  let Y : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h₁ : Y < Z := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {x} from
      closure_minimal (by simpa using hy) isClosed_closure) fun h ↦ hyx ?_
    exact (inseparable_iff_closure_eq.mpr congr(($h : Set X))).eq
  have h₂ : Z < T := by
    refine lt_of_le_of_ne (show closure {x} ⊆ Set.univ from Set.subset_univ _) fun h ↦ hx ?_
    have hu' : u ∈ closure ({x} : Set X) := by
      rw [show closure ({x} : Set X) = Set.univ from congr(($h : Set X))]; trivial
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hu' U hU hu
    rwa [Set.mem_singleton_iff.mp hz] at hzU
  let q₁ : LTSeries (IrreducibleCloseds X) := (RelSeries.singleton _ Y).snoc Z h₁
  let q : LTSeries (IrreducibleCloseds X) :=
    q₁.snoc T (by rw [show q₁.last = Z from RelSeries.last_snoc _ _ _]; exact h₂)
  have hq : q.length = 2 := rfl
  have := Order.LTSeries.length_le_krullDim q
  rw [hq] at this
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := this.trans h
  exact absurd h2 (by decide)

/-- In an irreducible quasi-sober noetherian `T₀` space of dimension at most one, the complement
of a nonempty open subset is finite: it is a closed subset all of whose points are closed, so its
finitely many irreducible components are points. -/
theorem IsOpen.finite_compl_of_topologicalKrullDim_le_one [QuasiSober X] [NoetherianSpace X]
    (h : topologicalKrullDim X ≤ 1) {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    Uᶜ.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (hU.isClosed_singleton_of_mem_compl h hne hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z

end

section Map

open Order

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] [T0Space X]
  [QuasiSober Y] [T0Space Y]

attribute [local instance] specializationOrder

/-- The dimension of a quasi-sober `T₀` space is the Krull dimension of its points, ordered by
specialization. -/
theorem topologicalKrullDim_eq_krullDim_specializationOrder :
    topologicalKrullDim X = krullDim X :=
  krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- A surjective specializing map `f : X ⟶ Y` of quasi-sober `T₀` spaces satisfies
`dim Y ≤ dim X`: a chain of specializations in `Y` lifts to `X`, starting from its generic end.
-/
theorem topologicalKrullDim_le_of_specializingMap {f : X → Y} (hf : SpecializingMap f)
    (hsurj : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder, krullDim_eq_iSup_height,
    krullDim_eq_iSup_height]
  refine iSup_le fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  refine le_trans (WithBot.coe_le_coe.mpr ?_) (le_iSup (fun a : X ↦ (height a : WithBot ℕ∞)) x)
  suffices ∀ (n : ℕ) (p : LTSeries Y) (x : X), p.length = n → p.last = f x → (n : ℕ∞) ≤ height x
    from height_le fun p hp ↦ this _ p x rfl hp
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro p x hn hp
    have hlt : p.eraseLast.last < f x := hp ▸ p.eraseLast_last_rel_last (by omega)
    obtain ⟨x', hxx', hx'⟩ := hf hlt.le
    have hx'x : x' < x := lt_of_le_of_ne hxx' (by rintro rfl; exact hlt.ne hx'.symm)
    have := ih p.eraseLast x' (by simp [hn]) hx'.symm
    calc ((n + 1 : ℕ) : ℕ∞) = n + 1 := by push_cast; rfl
      _ ≤ height x' + 1 := by gcongr
      _ ≤ height x := height_add_one_le hx'x

/-- A continuous map `f : X ⟶ Y` of quasi-sober `T₀` spaces which identifies no two distinct
points `x ⤳ x'` satisfies `dim X ≤ dim Y`. -/
theorem topologicalKrullDim_le_of_continuous {f : X → Y} (hf : Continuous f)
    (hinj : ∀ x x', x ⤳ x' → f x = f x' → x = x') :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder]
  refine krullDim_le_of_strictMono f fun a b hab ↦ lt_of_le_of_ne (hab.le.map hf) fun h ↦ ?_
  exact hab.ne (hinj _ _ hab.le h.symm).symm

end Map

section Inducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An inducing map with closed range into an irreducible space of finite dimension, whose
source has the same dimension as the target, is surjective: otherwise a maximal chain of
irreducible closed subsets of the source, pushed forward and followed by the whole space, would be
longer than any chain of the target. -/
theorem Topology.IsInducing.surjective_of_topologicalKrullDim_eq [IrreducibleSpace X]
    {f : Y → X} (hf : IsInducing f) (hc : IsClosed (Set.range f))
    (hfin : topologicalKrullDim X ≠ ⊤) (h : topologicalKrullDim Y = topologicalKrullDim X) :
    Function.Surjective f := by
  by_contra hns
  have hne : Set.range f ≠ Set.univ := fun h ↦ hns (Set.range_eq_univ.1 h)
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hbot
  have hm' : m ≠ ⊤ := by
    rintro rfl
    exact hfin hm.symm
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hm'
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (show ((n : ℕ∞) : WithBot ℕ∞) ≤
    topologicalKrullDim Y from h ▸ hm.le)
  let top : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let l₀ := l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hf)
  have hlast : l₀.last < top := by
    refine lt_of_le_of_ne (fun x _ ↦ Set.mem_univ x) fun heq ↦ hne ?_
    refine Set.eq_univ_of_univ_subset ?_
    have : (top : Set X) ⊆ closure (f '' l.last) := by
      rw [← heq]
      rfl
    exact this.trans (closure_minimal (Set.image_subset_range _ _) hc)
  let l' := l₀.snoc top hlast
  have := Order.LTSeries.length_le_krullDim l'
  rw [show l'.length = n + 1 by simp [l', l₀, hl]] at this
  change _ ≤ topologicalKrullDim X at this
  rw [← hm] at this
  norm_cast at this
  omega

end Inducing

section DimensionZero

variable {X : Type*} [TopologicalSpace X]

/-- In a space of dimension at most zero, an inclusion of irreducible closed subsets is an
equality: a strict inclusion would be a chain of length one. -/
theorem IrreducibleCloseds.eq_of_le_of_topologicalKrullDim_le_zero
    (h : topologicalKrullDim X ≤ 0) {A B : IrreducibleCloseds X} (hAB : A ≤ B) : A = B := by
  by_contra hne
  have := Order.LTSeries.length_le_krullDim ((RelSeries.singleton _ A).snoc B
    (lt_of_le_of_ne hAB hne))
  have h1 : ((1 : ℕ) : WithBot ℕ∞) ≤ 0 := this.trans h
  exact absurd h1 (by decide)

/-- **Zero-dimensional closed subsets are finite.** A closed subset `Z` of dimension at most zero
of a noetherian `T₀` space is a finite set of closed points. This applies to the underlying space
of a scheme of finite type over a field, which is noetherian.

(blueprint: `lem-sc-dim0-finite`) -/
theorem IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
    [NoetherianSpace X] [T0Space X] {Z : Set X} (hZ : IsClosed Z)
    (h : topologicalKrullDim Z ≤ 0) : Z.Finite ∧ ∀ z ∈ Z, IsClosed {z} := by
  -- Every point of `Z` is closed in `Z`: its closure is a minimal irreducible closed subset.
  have hcl : ∀ z : Z, closure {z} = {z} := by
    intro z
    refine subset_antisymm (fun y hy ↦ ?_) subset_closure
    let A : IrreducibleCloseds Z := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds Z := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A ≤ B := show closure {y} ⊆ closure {z} from
      closure_minimal (by simpa using hy) isClosed_closure
    have hAB' := IrreducibleCloseds.eq_of_le_of_topologicalKrullDim_le_zero h hAB
    exact (inseparable_iff_closure_eq.mpr congr(($hAB' : Set Z))).eq
  refine ⟨?_, fun z hz ↦ ?_⟩
  · -- Each irreducible component of `Z` is the closure of any of its points, a singleton.
    have hinj : Function.Injective fun z : Z ↦ irreducibleComponent z := by
      intro y z hyz
      have hy : irreducibleComponent y = {y} := by
        let A : IrreducibleCloseds Z := ⟨{y}, isIrreducible_singleton, by
          rw [← hcl y]; exact isClosed_closure⟩
        let B : IrreducibleCloseds Z := ⟨irreducibleComponent y,
          isIrreducible_irreducibleComponent, isClosed_irreducibleComponent⟩
        have hAB : A ≤ B := show {y} ⊆ irreducibleComponent y from
          Set.singleton_subset_iff.mpr (mem_irreducibleComponent)
        exact congr(($((IrreducibleCloseds.eq_of_le_of_topologicalKrullDim_le_zero h hAB).symm) :
          Set Z))
      have hz : z ∈ irreducibleComponent y := by
        have hyz : irreducibleComponent y = irreducibleComponent z := hyz
        rw [hyz]
        exact mem_irreducibleComponent
      rw [hy] at hz
      exact hz.symm
    have : Finite (irreducibleComponents Z) := NoetherianSpace.finite_irreducibleComponents
    have : Finite Z := Finite.of_injective (fun z : Z ↦ (⟨irreducibleComponent z,
      irreducibleComponent_mem_irreducibleComponents z⟩ : irreducibleComponents Z))
      fun y z hyz ↦ hinj congr(($hyz).1)
    exact Set.toFinite Z
  · have := hZ.isClosedMap_subtype_val _ (closure_subset_iff_isClosed.mp (hcl ⟨z, hz⟩).subset)
    simpa using this

end DimensionZero

section ClosurePoint

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

attribute [local instance] specializationOrder in
/-- In a quasi-sober `T₀` space, the dimension of the closure of a point is its height for the
specialization order: the points of `closure {z}` are exactly the specializations of `z`. -/
theorem topologicalKrullDim_closure_singleton (z : X) :
    topologicalKrullDim (closure ({z} : Set X)) = height z := by
  have : QuasiSober (closure ({z} : Set X)) :=
    isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, height_eq_krullDim_Iic]
  exact @krullDim_eq_of_orderIso _ _ (specializationOrder _).toPreorder _
    (@RelIso.mk _ _ (specializationOrder _).le (· ≤ ·)
      (Equiv.subtypeEquivRight fun x ↦ specializes_iff_mem_closure.symm)
      fun {a b} ↦ (IsInducing.subtypeVal.specializes_iff (x := b) (y := a)))

attribute [local instance] specializationOrder in
/-- A quasi-sober `T₀` space of finite positive dimension contains an irreducible closed subset
of dimension one: the closure of a point of minimal positive height. -/
theorem exists_topologicalKrullDim_closure_singleton_eq_one
    (h1 : 1 ≤ topologicalKrullDim X) (htop : topologicalKrullDim X ≠ ⊤) :
    ∃ z : X, topologicalKrullDim (closure ({z} : Set X)) = 1 := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder] at h1 htop
  have hfin (y : X) : height y < ⊤ :=
    WithBot.coe_lt_coe.mp ((height_le_krullDim y).trans_lt (lt_top_iff_ne_top.mpr htop))
  obtain ⟨l, hl⟩ := le_krullDim_iff.mp (by exact_mod_cast h1 : ((1 : ℕ) : WithBot ℕ∞) ≤ _)
  -- A point `z` of minimal height among those of height at least one.
  let S : Set ℕ∞ := {h | ∃ y : X, 1 ≤ height y ∧ height y = h}
  have hne : S.Nonempty := ⟨_, l.last, by simpa [hl] using length_le_height_last (p := l), rfl⟩
  obtain ⟨z, hz1, hz⟩ := WellFounded.min_mem wellFounded_lt _ hne
  refine ⟨z, ?_⟩
  have : height z = ((1 : ℕ) : ℕ∞) := by
    refine height_eq_coe_iff_minimal_le_height.mpr ⟨by simpa using hz1, fun y hy hyz ↦ ?_⟩
    by_contra hzy
    have hlt : y < z := lt_of_le_of_ne hyz fun h ↦ hzy (h ▸ le_rfl)
    have := WellFounded.not_lt_min wellFounded_lt S
      (show height y ∈ S from ⟨y, by simpa using hy, rfl⟩)
    rw [← hz] at this
    exact this (height_strictMono hlt (hfin y))
  rw [topologicalKrullDim_closure_singleton, this]
  rfl

end ClosurePoint

section LocalDimension

variable {X : Type*} [TopologicalSpace X]

/-- The *local dimension* `dim_x X` of a topological space `X` at a point `x`: the infimum of the
topological Krull dimensions of the open neighbourhoods of `x` [Stacks 04NA]. -/
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U

/-- If every open neighbourhood of `x` has dimension `n`, then `dim_x X = n`. -/
theorem topologicalKrullDimAt_eq_of_forall {x : X} {n : WithBot ℕ∞}
    (h : ∀ U : Opens X, x ∈ U → topologicalKrullDim U = n) : topologicalKrullDimAt x = n :=
  le_antisymm ((iInf₂_le ⊤ trivial).trans (h ⊤ trivial).le) (le_iInf₂ fun U hU ↦ (h U hU).ge)

/-- The local dimension at a point of an open subset `W` agrees with the local dimension in the
ambient space: the open neighbourhoods of `x` contained in `W` are cofinal. -/
theorem IsOpen.topologicalKrullDimAt_eq {W : Set X} (hW : IsOpen W) {x : X} (hx : x ∈ W) :
    topologicalKrullDimAt (⟨x, hx⟩ : W) = topologicalKrullDimAt x := by
  apply le_antisymm
  · refine le_iInf₂ fun U hU ↦ ?_
    let U' : Opens W := ⟨Subtype.val ⁻¹' U, U.isOpen.preimage continuous_subtype_val⟩
    refine (iInf₂_le U' hU).trans ?_
    refine IsInducing.topologicalKrullDim_le
      (f := fun p : U' ↦ (⟨p.1.1, p.2⟩ : U)) (.of_comp (g := Subtype.val) (by fun_prop) ?_ ?_)
    · exact continuous_subtype_val
    · change IsInducing ((Subtype.val : W → X) ∘ (Subtype.val : U' → W))
      exact IsInducing.subtypeVal.comp IsInducing.subtypeVal
  · refine le_iInf₂ fun U' hU' ↦ ?_
    let U : Opens X := ⟨Subtype.val '' (U' : Set W), hW.isOpenMap_subtype_val _ U'.isOpen⟩
    refine (iInf₂_le U ⟨_, hU', rfl⟩).trans ?_
    refine IsInducing.topologicalKrullDim_le
      (f := fun p : U ↦ (⟨⟨p.1, by obtain ⟨q, -, hq⟩ := p.2; exact hq ▸ q.2⟩,
        Subtype.val_injective.mem_set_image.mp p.2⟩ : U'))
      (.of_comp (g := Subtype.val ∘ Subtype.val) (by fun_prop) ?_ ?_)
    · exact continuous_subtype_val.comp continuous_subtype_val
    · exact IsInducing.subtypeVal

end LocalDimension

section Specialization

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

/-- Let `W ⊆ Z` be closed subsets of a quasi-sober `T₀` space such that every point of `W` has a
generalization in `Z \ W`. If `dim Z < d + 1`, then `dim W < d`: a chain of specializations in
`W` extends in `Z` by such a generalization of its generic end. -/
theorem topologicalKrullDim_lt_of_forall_exists_specializes {Z W : Set X} (hZ : IsClosed Z)
    (hW : IsClosed W) (hWZ : W ⊆ Z) (h : ∀ w ∈ W, ∃ z ∈ Z, z ⤳ w ∧ z ∉ W) {d : ℕ}
    (hd : topologicalKrullDim Z < d + 1) : topologicalKrullDim W < d := by
  have := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have := hW.isClosedEmbedding_subtypeVal.quasiSober
  let := specializationOrder Z
  let := specializationOrder W
  rw [topologicalKrullDim_eq_krullDim_specializationOrder] at hd ⊢
  by_contra! hle
  obtain ⟨l, hl⟩ := le_krullDim_iff.1 hle
  obtain ⟨z, hzZ, hzw, hzW⟩ := h _ l.last.2
  let i : W → Z := fun w ↦ ⟨w, hWZ w.2⟩
  have hi : StrictMono i := strictMono_of_le_iff_le fun a b ↦
    (IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).symm.trans
      (IsInducing.subtypeVal.specializes_iff (x := i b) (y := i a))
  have hlast : (l.map i hi).last < ⟨z, hzZ⟩ := by
    rw [LTSeries.last_map]
    refine lt_of_le_of_ne (IsInducing.subtypeVal.specializes_iff.1 hzw) fun heq ↦ hzW ?_
    obtain rfl : (l.last : X) = z := congrArg Subtype.val heq
    exact l.last.2
  have hlen := LTSeries.length_le_krullDim ((l.map i hi).snoc _ hlast)
  rw [RelSeries.snoc_length, LTSeries.map_length, hl, Nat.cast_add_one] at hlen
  exact (hlen.trans_lt hd).false

/-- A closed subset `Z` of a noetherian quasi-sober `T₀` space contains a finite set of points
of which every point of `Z` is a specialization: the generic points of the finitely many
irreducible closed subsets covering `Z`. -/
theorem IsClosed.exists_finite_forall_exists_specializes [NoetherianSpace X] {Z : Set X}
    (hZ : IsClosed Z) : ∃ G : Set X, G.Finite ∧ G ⊆ Z ∧ ∀ z ∈ Z, ∃ ξ ∈ G, ξ ⤳ z := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine ⟨⋃ t ∈ S, {x | IsGenericPoint x t},
    hSf.biUnion fun t _ ↦ Set.Subsingleton.finite fun x hx y hy ↦ hx.eq hy, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_sUnion_of_mem hxt.mem ht
  · intro z hz
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    exact ⟨ξ, Set.mem_iUnion₂.2 ⟨t, ht, hξ⟩, hξ.specializes hzt⟩

/-- A closed subset `Z` of a noetherian quasi-sober `T₀` space has only finitely many maximal
points, i.e. points of `Z` without proper generalization in `Z` (the generic points of the
irreducible components of `Z`). -/
theorem IsClosed.finite_setOf_maximal_specializes [NoetherianSpace X] {Z : Set X}
    (hZ : IsClosed Z) : {η | η ∈ Z ∧ ∀ z ∈ Z, z ⤳ η → z = η}.Finite := by
  obtain ⟨G, hGf, hGZ, hG⟩ := hZ.exists_finite_forall_exists_specializes
  refine hGf.subset fun η ⟨hηZ, hη⟩ ↦ ?_
  obtain ⟨ξ, hξG, hξη⟩ := hG η hηZ
  rwa [← hη ξ (hGZ hξG) hξη]

/-- Every point of a closed subset `Z` of a noetherian quasi-sober `T₀` space is a specialization
of a maximal point of `Z`, i.e. a point of `Z` without proper generalization in `Z`. -/
theorem IsClosed.exists_maximal_specializes [NoetherianSpace X] {Z : Set X} (hZ : IsClosed Z)
    {z : X} (hz : z ∈ Z) : ∃ η ∈ Z, (∀ y ∈ Z, y ⤳ η → y = η) ∧ η ⤳ z := by
  let := specializationOrder X
  obtain ⟨G, hGf, hGZ, hG⟩ := hZ.exists_finite_forall_exists_specializes
  obtain ⟨ξ, hξG, hξz⟩ := hG z hz
  obtain ⟨η, -, ⟨hηG, hηz⟩, hη⟩ :=
    (hGf.subset (Set.sep_subset G (· ⤳ z))).exists_le_maximal ⟨hξG, hξz⟩
  refine ⟨η, hGZ hηG, fun y hy hyη ↦ ?_, hηz⟩
  obtain ⟨ξ', hξ'G, hξ'y⟩ := hG y hy
  have hηξ' : η ⤳ ξ' := hη ⟨hξ'G, hξ'y.trans (hyη.trans hηz)⟩ (hξ'y.trans hyη)
  exact (hyη.antisymm (hηξ'.trans hξ'y)).eq

attribute [local instance] specializationOrder in
/-- In a quasi-sober `T₀` space with generic point `x` and of dimension at least `d + 1`, there is
a proper specialization `w` of `x` whose closure has dimension at least `d`: the penultimate
point of a chain of length `d + 1`. -/
theorem exists_specializes_ne_le_topologicalKrullDim_closure {x : X}
    (hx : closure {x} = Set.univ) {d : ℕ}
    (hd : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ w : X, x ⤳ w ∧ w ≠ x ∧ (d : WithBot ℕ∞) ≤ topologicalKrullDim (closure {w} : Set X) := by
  have hgen (y : X) : x ⤳ y := specializes_iff_mem_closure.2 (hx ▸ Set.mem_univ y)
  rw [topologicalKrullDim_eq_krullDim_specializationOrder] at hd
  obtain ⟨l, hl⟩ := le_krullDim_iff.1 hd
  have hlt : l.eraseLast.last < l.last := l.eraseLast_last_rel_last (by omega)
  refine ⟨l.eraseLast.last, hgen _, fun h ↦ (hlt.trans_le (hgen l.last)).ne h, ?_⟩
  rw [topologicalKrullDim_closure_singleton]
  exact_mod_cast le_trans (by simp [hl]) (length_le_height_last (p := l.eraseLast))

attribute [local instance] specializationOrder in
/-- A quasi-sober `T₀` space of dimension at least `d` contains a point whose closure has
dimension at least `d`: the generic end of a chain of length `d`. -/
theorem exists_le_topologicalKrullDim_closure_singleton {d : ℕ}
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ x : X, (d : WithBot ℕ∞) ≤ topologicalKrullDim (closure {x} : Set X) := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder] at hd
  obtain ⟨l, hl⟩ := le_krullDim_iff.1 hd
  refine ⟨l.last, ?_⟩
  rw [topologicalKrullDim_closure_singleton, ← hl]
  exact_mod_cast length_le_height_last (p := l)

end Specialization

/-- An embedding `f : Y → X` identifies the dimension of `Y` with that of its range. -/
theorem Topology.IsEmbedding.topologicalKrullDim_eq_range {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : Y → X} (hf : IsEmbedding f) :
    topologicalKrullDim Y = topologicalKrullDim (Set.range f) :=
  IsHomeomorph.topologicalKrullDim_eq _ hf.toHomeomorph.isHomeomorph

/-- A quasi-sober space of positive topological Krull dimension has a point which is not
closed: the generic point of the larger member of a chain of length one of irreducible closed
subsets. -/
theorem exists_not_isClosed_singleton_of_topologicalKrullDim_pos {X : Type*}
    [TopologicalSpace X] [QuasiSober X] (hX : 0 < topologicalKrullDim X) :
    ∃ x : X, ¬ IsClosed ({x} : Set X) := by
  obtain ⟨Z₀, Z₁, hZ⟩ := Order.krullDim_pos_iff.1 hX
  have hη := Z₁.isIrreducible.isGenericPoint_genericPoint Z₁.isClosed
  set η := Z₁.isIrreducible.genericPoint
  refine ⟨η, fun hc ↦ ?_⟩
  have h₁ : (Z₁ : Set X) = {η} := by rw [← hη.def]; exact hc.closure_eq
  obtain ⟨z, hz⟩ := Z₀.isIrreducible.nonempty
  have h₀ : (Z₀ : Set X) ⊆ Z₁ := hZ.le
  have hzη : z = η := by have := h₀ hz; rw [h₁] at this; exact this
  have : (Z₁ : Set X) ⊆ Z₀ := by
    rw [h₁, Set.singleton_subset_iff, ← hzη]
    exact hz
  exact hZ.ne (SetLike.coe_injective (h₀.antisymm this))
