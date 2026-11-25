/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.Sheaves.Godement

/-!
# Supports of sections and dimension bounds

This file collects the ingredients of the proof of Grothendieck vanishing.

* `TopologicalSpace.DimLT S n`: every chain of irreducible closed subsets of `X` contained in
  `S` has length `< n`. For a closed subset `Z` of a noetherian quasi-sober space written as an
  irredundant union of the closures of finitely many points `η ∈ E`
  (`TopologicalSpace.exists_finset_irredundant`), a closed subset of `Z` missing every `η`
  has smaller dimension (`TopologicalSpace.DimLT.of_subset_of_forall_not_mem`).
* `TopCat.Sheaf.sectionSupport s`: the points where the germ of a section `s` is nonzero.
* `TopCat.Sheaf.godementOn E F`: the flasque sheaf `V ↦ ∏_{x ∈ V ∩ E} F_x`, with the germ map
  `TopCat.Sheaf.toGodementOn E F : F ⟶ godementOn E F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- A subset `S` of `X` has dimension `< n`: every chain `T₀ < ⋯ < T_k` of irreducible closed
subsets of `X` with `T_k ⊆ S` has length `k < n`. -/
def DimLT (S : Set X) (n : ℕ) : Prop :=
  ∀ p : LTSeries (IrreducibleCloseds X), (p.last : Set X) ⊆ S → p.length < n

lemma DimLT.mono {S T : Set X} {n : ℕ} (h : DimLT T n) (hST : S ⊆ T) : DimLT S n :=
  fun p hp ↦ h p (hp.trans hST)

lemma dimLT_empty (n : ℕ) : DimLT (∅ : Set X) n := fun p hp ↦
  absurd (Set.subset_empty_iff.1 hp) p.last.isIrreducible.nonempty.ne_empty


lemma DimLT.union {S T : Set X} {n : ℕ} (hS : DimLT S n) (hT : DimLT T n) (hS' : IsClosed S)
    (hT' : IsClosed T) : DimLT (S ∪ T) n := fun p hp ↦ by
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 p.last.isIrreducible.isPreirreducible
    S T hS' hT' hp with h | h
  · exact hS p h
  · exact hT p h

lemma eq_empty_of_dimLT_zero {S : Set X} (h : DimLT S 0) (hS : IsClosed S) : S = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  exact Nat.not_lt_zero _ (h (RelSeries.singleton _
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (closure_minimal (Set.singleton_subset_iff.2 hx) hS))

lemma dimLT_of_topologicalKrullDim_lt {q : ℕ} (h : topologicalKrullDim X < q) (S : Set X) :
    DimLT S q := fun p _ ↦ by
  have := (Order.LTSeries.length_le_krullDim p).trans_lt h
  exact_mod_cast this

/-- In a noetherian quasi-sober space, a closed subset `Z` is the union of the closures of
finitely many of its points `η ∈ E`, none of which lies in the closure of another. -/
lemma exists_finset_irredundant [NoetherianSpace X] [QuasiSober X] {Z : Set X}
    (hZ : IsClosed Z) : ∃ E : Finset X, Z = ⋃ η ∈ E, closure {η} ∧
      ∀ η ∈ E, ∀ η' ∈ E, η ∈ closure {η'} → η = η' := by
  classical
  have hex : ∃ k, ∃ E : Finset X, E.card = k ∧ Z = ⋃ η ∈ E, closure {η} := by
    obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
    choose η hη using fun t : S ↦ QuasiSober.sober (hSi t.1 t.2) (hSc t.1 t.2)
    have := hSf.fintype
    refine ⟨_, Finset.univ.image η, rfl, ?_⟩
    ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hη ⟨t, ht⟩).def ▸ hx⟩
    · rintro ⟨_, ⟨t, rfl⟩, hx⟩
      exact ⟨t.1, t.2, (hη t).def ▸ hx⟩
  obtain ⟨E, hE, hZE⟩ := Nat.find_spec hex
  refine ⟨E, hZE, fun η hη η' hη' h ↦ by_contra fun hne ↦ ?_⟩
  refine Nat.find_min hex (m := (E.erase η).card) ?_ ⟨E.erase η, rfl, ?_⟩
  · rw [Finset.card_erase_of_mem hη, ← hE]
    exact Nat.sub_lt (Finset.card_pos.2 ⟨η, hη⟩) one_pos
  · rw [hZE]
    refine subset_antisymm (Set.iUnion₂_subset fun ζ hζ ↦ ?_)
      (Set.biUnion_subset_biUnion_left fun ζ hζ ↦ Finset.mem_of_mem_erase hζ)
    by_cases hζη : ζ = η
    · subst hζη
      exact (closure_minimal (Set.singleton_subset_iff.2 h) isClosed_closure).trans
        (Set.subset_biUnion_of_mem (u := fun η ↦ closure {η})
          (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hne, hη'⟩)))
    · exact Set.subset_biUnion_of_mem (u := fun η ↦ closure {η})
        (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hζη, hζ⟩))

/-- **Dimension drops off the generic points**: if a closed set `Z` with `DimLT Z (n + 1)` is the
union of the closures of the points of `E`, then a closed subset of `Z` containing no point of
`E` has `DimLT _ n`. -/
lemma DimLT.of_subset_of_forall_notMem {Z Z' : Set X} {n : ℕ} {E : Finset X} (hZ : DimLT Z (n + 1))
    (hZE : Z = ⋃ η ∈ E, closure {η}) (hZ' : Z' ⊆ Z) (hE : ∀ η ∈ E, η ∉ Z') : DimLT Z' n := by
  classical
  intro p hp
  obtain ⟨t, ht, hpt⟩ := isIrreducible_iff_sUnion_isClosed.1 p.last.isIrreducible
    (E.image fun η ↦ closure {η}) (by simp)
    (by
      rw [Finset.coe_image, Set.sUnion_image]
      have := hp.trans (hZ'.trans hZE.le)
      simpa using this)
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.1 ht
  let T : IrreducibleCloseds X := ⟨closure {η}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : p.last < T := lt_of_le_of_ne (show (p.last : Set X) ≤ T from hpt) fun h ↦
    hE η hη (hp (h ▸ subset_closure rfl : η ∈ (p.last : Set X)))
  have := hZ (p.snoc T hlt) (by
    rw [RelSeries.last_snoc, hZE]
    exact Set.subset_biUnion_of_mem (u := fun η ↦ closure {η}) (Finset.mem_coe.2 hη))
  simpa using this

/-- A subset `S` of an open `V` meets the closure of a point `η` of an irredundant family `E` only
if `η ∈ V`; so if moreover `S ⊆ Z = ⋃_{η ∈ E} closure {η}` and the closure of `S` contains no
`η ∈ E ∩ V`, it contains no `η ∈ E` at all. -/
lemma notMem_closure_of_subset {Z S V : Set X} {E : Finset X}
    (hZE : Z = ⋃ η ∈ E, closure {η}) (hE : ∀ η ∈ E, ∀ η' ∈ E, η ∈ closure {η'} → η = η')
    (hV : IsOpen V) (hS : S ⊆ V ∩ Z) (hSE : ∀ η ∈ E, η ∈ V → η ∉ closure S) :
    ∀ η ∈ E, η ∉ closure S := by
  classical
  intro η hη hηS
  by_cases hηV : η ∈ V
  · exact hSE η hη hηV hηS
  have hY : IsClosed (⋃ η' ∈ E.filter (· ∈ V), closure {η'}) :=
    (E.filter (· ∈ V)).finite_toSet.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hSY : S ⊆ ⋃ η' ∈ E.filter (· ∈ V), closure {η'} := by
    intro y hy
    have hyZ := (hS hy).2
    rw [hZE] at hyZ
    obtain ⟨η', hη', hyη'⟩ := Set.mem_iUnion₂.1 hyZ
    have : η' ∈ V := by
      obtain ⟨z, hz, rfl⟩ := mem_closure_iff.1 hyη' V hV (hS hy).1
      exact hz
    exact Set.mem_iUnion₂.2 ⟨η', Finset.mem_filter.2 ⟨hη', this⟩, hyη'⟩
  obtain ⟨η', hη', hηη'⟩ := Set.mem_iUnion₂.1 (closure_minimal hSY hY hηS)
  rw [Finset.mem_filter] at hη'
  exact hηV (hE η hη η' hη'.1 hηη' ▸ hη'.2)

end TopologicalSpace

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section Support

variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The support of a section `s` of an abelian sheaf over `V`: the points of `V` at which the
germ of `s` is nonzero. -/
def sectionSupport {V : Opens X} (s : F.obj.obj (op V)) : Set X :=
  {x | ∃ h : x ∈ V, TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.obj V x h s ≠ 0}

variable {F}

lemma sectionSupport_subset {V : Opens X} (s : F.obj.obj (op V)) :
    sectionSupport F s ⊆ V := fun _ ⟨h, _⟩ ↦ h

lemma germ_eq_zero_iff {V : Opens X} (s : F.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.obj V x hx s = 0 ↔
      ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ V), F.obj.map i.op s = 0 := by
  constructor
  · intro h
    obtain ⟨W, hxW, i, i', hW⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u}) F.obj x hx hx
      s 0 (by rw [h, map_zero])
    exact ⟨W, hxW, i, by rw [hW, map_zero]⟩
  · rintro ⟨W, hxW, i, hW⟩
    rw [← TopCat.Presheaf.germ_res_apply F.obj i x hxW, hW, map_zero]

lemma notMem_sectionSupport_iff {V : Opens X} (s : F.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    x ∉ sectionSupport F s ↔
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.obj V x hx s = 0 := by
  simp [sectionSupport, hx]

/-- A section vanishes near every point of its domain off its support. -/
lemma exists_disjoint_sectionSupport {V : Opens X} (s : F.obj.obj (op V)) {x : X} (hx : x ∈ V)
    (hxs : x ∉ sectionSupport F s) :
    ∃ W : Opens X, x ∈ W ∧ Disjoint (W : Set X) (sectionSupport F s) := by
  obtain ⟨W, hxW, i, hW⟩ := (germ_eq_zero_iff s hx).1 ((notMem_sectionSupport_iff s hx).1 hxs)
  refine ⟨W, hxW, Set.disjoint_left.2 fun y hyW ⟨hyV, hy⟩ ↦ hy ?_⟩
  exact (germ_eq_zero_iff s hyV).2 ⟨W, hyW, i, hW⟩

lemma eq_zero_of_sectionSupport_eq_empty {V : Opens X} (s : F.obj.obj (op V))
    (h : sectionSupport F s = ∅) : s = 0 := by
  refine TopCat.Presheaf.section_ext F V s 0 fun x hx ↦ ?_
  rw [map_zero]
  exact (notMem_sectionSupport_iff s hx).1 (h ▸ Set.notMem_empty x)

lemma sectionSupport_map_subset {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (f : F ⟶ G) {V : Opens X} (s : F.obj.obj (op V)) :
    sectionSupport G (f.hom.app (op V) s) ⊆ sectionSupport F s := by
  intro x ⟨hx, hfx⟩
  refine ⟨hx, fun h ↦ hfx ?_⟩
  obtain ⟨W, hxW, i, hW⟩ := (germ_eq_zero_iff s hx).1 h
  refine (germ_eq_zero_iff _ hx).2 ⟨W, hxW, i, ?_⟩
  rw [← NatTrans.naturality_apply, hW, map_zero]

lemma sectionSupport_map_of_injective {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (f : F ⟶ G) (hf : ∀ W : Opens X, Function.Injective (f.hom.app (op W)))
    {V : Opens X} (s : F.obj.obj (op V)) :
    sectionSupport G (f.hom.app (op V) s) = sectionSupport F s := by
  refine subset_antisymm (sectionSupport_map_subset f s) fun x ⟨hx, hfx⟩ ↦ ⟨hx, fun h ↦ hfx ?_⟩
  obtain ⟨W, hxW, i, hW⟩ := (germ_eq_zero_iff _ hx).1 h
  refine (germ_eq_zero_iff s hx).2 ⟨W, hxW, i, hf W ?_⟩
  rw [NatTrans.naturality_apply, hW, map_zero]

end Support

section Elements

variable {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- A section of a sheaf which is killed by a morphism lifts to the kernel. -/
lemma exists_kernel_ι_app_eq (ψ : F ⟶ G) {W : Opens X} (x : F.obj.obj (op W))
    (hx : ψ.hom.app (op W) x = 0) :
    ∃ t : (kernel ψ).obj.obj (op W), (kernel.ι ψ).hom.app (op W) t = x := by
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op W)
  let e := PreservesKernel.iso E ψ ≪≫ AddCommGrpCat.kernelIsoKer (E.map ψ)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have h₁ := PreservesKernel.iso_inv_ι E ψ
  have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map ψ)
  change (e.inv ≫ E.map (kernel.ι ψ)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, h₁, h₂]
  rfl

/-- A monomorphism of abelian sheaves is injective on sections. -/
lemma injective_app_of_mono (ψ : F ⟶ G) [Mono ψ] (W : Opens X) :
    Function.Injective (ψ.hom.app (op W)) := by
  have : Mono ψ.hom := (sheafToPresheaf _ _).map_mono ψ
  have : Mono (ψ.hom.app (op W)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- An epimorphism of abelian sheaves is locally surjective on sections. -/
lemma exists_mem_forall_exists_app_eq_of_epi (ψ : F ⟶ G) [Epi ψ] {V : Opens X}
    (s : G.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ V) (t : F.obj.obj (op W)),
      ψ.hom.app (op W) t = G.obj.map i.op s := by
  have : Sheaf.IsLocallySurjective ψ :=
    (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) ψ).2 inferInstance
  obtain ⟨W, i, ⟨t, ht⟩, hxW⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X) ψ.hom s x hx
  exact ⟨W, hxW, i, t, ht⟩

end Elements

section GodementOn

variable (E : Set X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The family of the stalks of `F` at the points of `E` (and `0` elsewhere). -/
abbrev stalkOn (x : X) : Type u :=
  PLift (x ∈ E) → (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u)

/-- The flasque sheaf `V ↦ ∏_{x ∈ V ∩ E} F_x` of all, not necessarily continuous, families of
germs of `F` at the points of `E`. -/
noncomputable def godementOn : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} :=
  ⟨Presheaf.godement (stalkOn E F), Presheaf.isSheaf_godement _⟩

instance : Presheaf.IsFlasque (godementOn E F).obj :=
  Presheaf.isFlasque_godement (stalkOn E F)

/-- The germ map `F ⟶ godementOn E F`. -/
noncomputable def toGodementOn : F ⟶ godementOn E F :=
  ObjectProperty.homMk (Presheaf.toGodement F ≫
    Presheaf.godementMap fun _ ↦ AddMonoidHom.pi fun _ ↦ AddMonoidHom.id _)

lemma toGodementOn_app_apply {V : Opens X} (s : F.obj.obj (op V)) (x : V) (hx : x.1 ∈ E) :
    (toGodementOn E F).hom.app (op V) s x ⟨hx⟩ =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.obj V x.1 x.2 s :=
  rfl

variable {E F}

lemma toGodementOn_app_eq_zero_iff {V : Opens X} (s : F.obj.obj (op V)) :
    (toGodementOn E F).hom.app (op V) s = 0 ↔ ∀ x ∈ E, x ∉ sectionSupport F s := by
  constructor
  · intro h x hxE ⟨hxV, hx⟩
    exact hx (congrFun (congrFun h ⟨x, hxV⟩) ⟨hxE⟩)
  · intro h
    funext x hx
    exact (notMem_sectionSupport_iff s x.2).1 (h x.1 hx.down)

lemma godementOn_eq_zero {V : Opens X} (t : (godementOn E F).obj.obj (op V))
    (h : Disjoint (V : Set X) E) : t = 0 :=
  funext fun x ↦ funext fun hx ↦ absurd hx.down (Set.disjoint_left.1 h x.2)

end GodementOn

end TopCat.Sheaf
