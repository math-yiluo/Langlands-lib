/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Spectral.Basic
public import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# Restriction of sheaves to a closed subset of a spectral space

Let `T` be a spectral space and `T₀ ⊆ T` a closed subset such that every irreducible closed
subset `C ⊆ T` meets `T₀` in a nonempty connected set. Then for every sheaf of abelian
groups `F` on `T`, restriction `Γ(T, F) ⟶ Γ(T₀, F|_{T₀})` is bijective.

The proof works with germs. Since every point of `T` specializes to a point of `T₀`, a global
section is determined by its germs along `T₀`, which gives injectivity. For surjectivity, a
section `t` over `T₀` is represented on a finite cover of `T₀` by quasi-compact opens `Uᵢ` of `T`
by sections `sᵢ ∈ F(Uᵢ)`. At a point `y` of `T`, two of these sections whose opens both contain
a specialization of `y` lying in `T₀` have the same germ at `y`: this is where the
connectedness of `closure {y} ∩ T₀` enters. The opens `Uᵢ` are then shrunk, by removing the
closure of the set of points where this compatibility could fail, to opens on which the `sᵢ`
glue. The shrunk opens still cover `T`, because in a spectral space the closure of a set which
is closed in the constructible topology consists of specializations of its points.

## Main statements

- `TopCat.Sheaf.bijective_app_top_of_bijective_stalk`: the criterion for a morphism
  `F ⟶ i_* G` inducing bijections on the stalks along `T₀`.
- `TopCat.Sheaf.bijective_unit_app_top`: the restriction is bijective.

## References

- Stacks Project, Lemma 59.82.4, <https://stacks.math.columbia.edu/tag/09ZG>
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Topology

namespace TopCat.Sheaf

variable {T : TopCat.{u}} [SpectralSpace T] {T₀ : Set T}

-- The inclusion of `T₀`, as a morphism of topological spaces.
set_option quotPrecheck false in
local notation "ι₀" => (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of T₀ ⟶ T)

/-- **Global sections along a closed subset of a spectral space.** Let `T` be a spectral space
and `T₀ ⊆ T` a closed subset such that every irreducible closed subset `C ⊆ T` meets `T₀` in a
nonempty connected set. Let `F` be a sheaf of abelian groups on `T`, `G` one on `T₀`, and
`η : F ⟶ i_* G` a morphism, for the inclusion `i : T₀ ⟶ T`, which induces bijections
`F_z ⟶ G_z` on the stalks at the points `z` of `T₀`. Then `η` is bijective on global
sections. -/
theorem bijective_app_top_of_bijective_stalk (hT₀ : IsClosed T₀)
    (hC : ∀ C : Set T, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    {F : T.Sheaf AddCommGrpCat.{u}} {G : (TopCat.of T₀).Sheaf AddCommGrpCat.{u}}
    (η : F.1 ⟶ (Presheaf.pushforward _
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of T₀ ⟶ T)).obj G.1)
    (φ : ∀ z : T₀, Presheaf.stalk F.presheaf z.1 ⟶ Presheaf.stalk G.presheaf z)
    (hφ : ∀ z, Function.Bijective (φ z))
    (hgerm : ∀ (z : T₀) (U : Opens T) (hz : z.1 ∈ U) (s : ToType (F.1.obj (op U))),
      φ z (Presheaf.germ F.presheaf U z.1 hz s) =
        Presheaf.germ G.presheaf ⟨Subtype.val ⁻¹' U, U.2.preimage continuous_subtype_val⟩ z hz
          (η.app (op U) s)) :
    Function.Bijective (η.app (op ⊤)) := by
  -- Every point of `T` specializes to a point of `T₀`.
  have hspec : ∀ y : T, ∃ z ∈ T₀, y ⤳ z := fun y ↦ by
    obtain ⟨z, hz, hz₀⟩ := (hC _ isClosed_closure isIrreducible_singleton.closure).nonempty
    exact ⟨z, hz₀, specializes_iff_mem_closure.mpr hz⟩
  -- Sections over opens of `T₀` that are restrictions of global sections.
  let res : ∀ U : Opens T, ToType (G.1.obj (op ⊤)) →
      ToType (G.1.obj (op ⟨Subtype.val ⁻¹' U, U.2.preimage continuous_subtype_val⟩)) :=
    fun U ↦ G.1.map (homOfLE le_top).op
  constructor
  · -- Injectivity: germs along `T₀` determine a global section.
    intro a b hab
    refine Presheaf.section_ext F ⊤ a b fun y _ ↦ ?_
    obtain ⟨z, hz₀, hyz⟩ := hspec y
    have h₁ : Presheaf.germ F.presheaf ⊤ z True.intro a =
        Presheaf.germ F.presheaf ⊤ z True.intro b := by
      apply (hφ ⟨z, hz₀⟩).1
      rw [hgerm, hgerm]
      exact congrArg _ hab
    obtain ⟨W, hzW, iU, iV, e⟩ := Presheaf.germ_eq (U := ⊤) (V := ⊤) F.presheaf z True.intro
      True.intro a b h₁
    have hyW : y ∈ W := hyz.mem_open W.2 hzW
    rw [← Presheaf.germ_res_apply F.presheaf iU y hyW,
      ← Presheaf.germ_res_apply F.presheaf iV y hyW, e]
  · -- Surjectivity.
    intro t
    -- Local representatives of `t` by sections over quasi-compact opens of `T`.
    have hloc : ∀ z : T₀, ∃ (N : Opens T) (_ : IsCompact (N : Set T)) (_ : z.1 ∈ N)
        (s : ToType (F.1.obj (op N))), η.app (op N) s = res N t := by
      intro z
      obtain ⟨a, ha⟩ := (hφ z).2 (Presheaf.germ G.presheaf ⊤ z True.intro t)
      obtain ⟨U, hzU, s₀, rfl⟩ := Presheaf.exists_germ_eq F.presheaf a
      rw [hgerm] at ha
      obtain ⟨W', hzW', iU, iV, e⟩ := Presheaf.germ_eq (V := ⊤) G.presheaf z hzU True.intro _ t ha
      obtain ⟨V, hV, hVW'⟩ := isOpen_induced_iff.mp W'.2
      replace hVW' : Subtype.val ⁻¹' V = (W' : Set T₀) := hVW'
      obtain ⟨N, ⟨hNo, hNc⟩, hzN, hNUV⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
          (a := z.1) (u := U ∩ V) ⟨hzU, show z ∈ Subtype.val ⁻¹' V from hVW' ▸ hzW'⟩
          (U.2.inter hV)
      have hNU : (⟨N, hNo⟩ : Opens T) ≤ U := fun x hx ↦ (hNUV hx).1
      have hNW' : (⟨Subtype.val ⁻¹' N, hNo.preimage continuous_subtype_val⟩ : Opens T₀) ≤ W' :=
        fun x hx ↦ show x ∈ (W' : Set T₀) from hVW' ▸ (hNUV hx).2
      refine ⟨⟨N, hNo⟩, hNc, hzN, F.1.map (homOfLE hNU).op s₀, ?_⟩
      have := congrArg (G.1.map (homOfLE hNW').op) e
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← G.1.map_comp,
        ← G.1.map_comp] at this
      rw [← ConcreteCategory.comp_apply, η.naturality, ConcreteCategory.comp_apply]
      exact this
    choose N hNc hzN s hs using hloc
    -- A finite subcover of `T₀`.
    obtain ⟨I, hI⟩ := hT₀.isCompact.elim_finite_subcover (fun z : T₀ ↦ (N z : Set T))
      (fun z ↦ (N z).2) (fun z hz ↦ Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzN _⟩)
    -- The finite family of local representatives.
    let U : I → Opens T := fun m ↦ N m.1
    let σ : ∀ m : I, ToType (F.1.obj (op (U m))) := fun m ↦ s m.1
    have hσ : ∀ m, η.app (op (U m)) (σ m) = res (U m) t := fun m ↦ hs m.1
    have hcov : ∀ z ∈ T₀, ∃ m : I, z ∈ U m := fun z hz ↦ by
      obtain ⟨m, hm, hzm⟩ := Set.mem_iUnion₂.mp (hI hz)
      exact ⟨⟨m, hm⟩, hzm⟩
    -- `Agree k l y`: the sections `σ k` and `σ l` are both defined at `y`, with the same germ.
    let Agree : I → I → T → Prop := fun k l y ↦ ∃ (hk : y ∈ U k) (hl : y ∈ U l),
      Presheaf.germ F.presheaf (U k) y hk (σ k) = Presheaf.germ F.presheaf (U l) y hl (σ l)
    have agree_trans : ∀ {k l m y}, Agree k l y → Agree l m y → Agree k m y :=
      fun ⟨hk, _, e₁⟩ ⟨_, hm, e₂⟩ ↦ ⟨hk, hm, e₁.trans e₂⟩
    have agree_symm : ∀ {k l y}, Agree k l y → Agree l k y :=
      fun ⟨hk, hl, e⟩ ↦ ⟨hl, hk, e.symm⟩
    have agree_open : ∀ k l, IsOpen {y | Agree k l y} := by
      intro k l
      refine isOpen_iff_forall_mem_open.mpr fun y ⟨hk, hl, e⟩ ↦ ?_
      obtain ⟨W, hyW, iU, iV, e'⟩ := Presheaf.germ_eq F.presheaf y hk hl _ _ e
      refine ⟨W, fun x hx ↦ ⟨iU.le hx, iV.le hx, ?_⟩, W.2, hyW⟩
      rw [← Presheaf.germ_res_apply F.presheaf iU x hx,
        ← Presheaf.germ_res_apply F.presheaf iV x hx, e']
    have agree_gen : ∀ {k l y w}, y ⤳ w → Agree k l w → Agree k l y :=
      fun h hw ↦ h.mem_open (agree_open _ _) hw
    -- Along `T₀`, any two of the sections agree, as both represent `t`.
    have agree_T₀ : ∀ k l, ∀ w ∈ T₀, w ∈ U k → w ∈ U l → Agree k l w := by
      intro k l w hw hk hl
      refine ⟨hk, hl, (hφ ⟨w, hw⟩).1 ((hgerm ⟨w, hw⟩ (U k) hk (σ k)).trans
        (Eq.trans ?_ (hgerm ⟨w, hw⟩ (U l) hl (σ l)).symm))⟩
      rw [hσ, hσ]
      exact (Presheaf.germ_res_apply G.presheaf _ _ _ t).trans
        (Presheaf.germ_res_apply G.presheaf _ _ _ t).symm
    -- The connectedness argument: two sections defined near specializations of `y` lying in
    -- `T₀` agree at `y`.
    have key : ∀ y k l, (∃ w ∈ (U k : Set T) ∩ T₀, y ⤳ w) →
        (∃ w ∈ (U l : Set T) ∩ T₀, y ⤳ w) → Agree k l y := by
      intro y k l ⟨wk, ⟨hwk, hwk₀⟩, hyk⟩ ⟨wl, ⟨hwl, hwl₀⟩, hyl⟩
      have hconn :=
        (hC _ isClosed_closure (isIrreducible_singleton (x := y)).closure).isPreconnected
      by_contra hkl
      obtain ⟨w, ⟨hwc, hw₀⟩, hwu, hwv⟩ := hconn (⋃ m, ⋃ (_ : Agree k m y), (U m : Set T))
        (⋃ m, ⋃ (_ : ¬ Agree k m y), (U m : Set T))
        (isOpen_iUnion fun m ↦ isOpen_iUnion fun _ ↦ (U m).2)
        (isOpen_iUnion fun m ↦ isOpen_iUnion fun _ ↦ (U m).2)
        (fun w ⟨_, hw₀⟩ ↦ by
          obtain ⟨m, hm⟩ := hcov w hw₀
          by_cases h : Agree k m y
          · exact Or.inl (Set.mem_iUnion₂.mpr ⟨m, h, hm⟩)
          · exact Or.inr (Set.mem_iUnion₂.mpr ⟨m, h, hm⟩))
        ⟨wk, ⟨specializes_iff_mem_closure.mp hyk, hwk₀⟩, Set.mem_iUnion₂.mpr
          ⟨k, ⟨hyk.mem_open (U k).2 hwk, hyk.mem_open (U k).2 hwk, rfl⟩, hwk⟩⟩
        ⟨wl, ⟨specializes_iff_mem_closure.mp hyl, hwl₀⟩, Set.mem_iUnion₂.mpr ⟨l, hkl, hwl⟩⟩
      obtain ⟨m₁, h₁, hw₁⟩ := Set.mem_iUnion₂.mp hwu
      obtain ⟨m₂, h₂, hw₂⟩ := Set.mem_iUnion₂.mp hwv
      exact h₂ (agree_trans h₁ (agree_gen (specializes_iff_mem_closure.mpr hwc)
        (agree_T₀ m₁ m₂ w hw₀ hw₁ hw₂)))
    -- The points of `U i` where `σ i` may fail to agree with another `σ j`.
    let K : I → Set T := fun m ↦ (U m : Set T) ∩ T₀
    have hK : ∀ m, IsCompact (K m) := fun m ↦ (hNc m.1).inter_right hT₀
    let Bd : I → Set T := fun i ↦
      (U i : Set T) ∩ ⋃ j, (generalizationHull (K j) ∩ {y | Agree i j y}ᶜ)
    have hBd : ∀ i, IsClosed[constructibleTopology T] (Bd i) := fun i ↦
      @IsClosed.inter T _ _ (constructibleTopology T)
        ((hNc i.1).isClosed_constructibleTopology_of_isOpen (U i).2)
        (@isClosed_iUnion_of_finite T I (constructibleTopology T) _ _ fun j ↦
          @IsClosed.inter T _ _ (constructibleTopology T)
            (hK j).isClosed_constructibleTopology_generalizationHull
            (isClosed_compl_iff.mpr (agree_open i j)).isClosed_constructibleTopology)
    have claim₁ : ∀ i y, (∃ z ∈ K i, y ⤳ z) → y ∉ closure (Bd i) := by
      intro i y ⟨z, hz, hyz⟩ hy
      obtain ⟨y', ⟨_, hy'⟩, hy'y⟩ :=
        exists_specializes_of_isClosed_constructibleTopology_of_mem_closure (hBd i) hy
      obtain ⟨j, hjgen, hjnot⟩ := Set.mem_iUnion.mp hy'
      obtain ⟨w, hw, hy'w⟩ := mem_generalizationHull_iff.mp hjgen
      exact hjnot (key y' i j ⟨z, hz, hy'y.trans hyz⟩ ⟨w, hw, hy'w⟩)
    -- The shrunk opens.
    let W : I → Opens T := fun i ↦
      ⟨(U i : Set T) \ closure (Bd i), (U i).2.sdiff isClosed_closure⟩
    have hWU : ∀ i, W i ≤ U i := fun i y hy ↦ hy.1
    have hWcov : ∀ y, ∃ i, y ∈ W i := by
      intro y
      obtain ⟨z, hz₀, hyz⟩ := hspec y
      obtain ⟨i, hzi⟩ := hcov z hz₀
      exact ⟨i, hyz.mem_open (U i).2 hzi, claim₁ i y ⟨z, ⟨hzi, hz₀⟩, hyz⟩⟩
    have hWagree : ∀ i j y, y ∈ W i → y ∈ W j → Agree i j y := by
      intro i j y hyi hyj
      obtain ⟨z, hz₀, hyz⟩ := hspec y
      obtain ⟨k, hzk⟩ := hcov z hz₀
      have hgen : y ∈ generalizationHull (K k) :=
        mem_generalizationHull_iff.mpr ⟨z, ⟨hzk, hz₀⟩, hyz⟩
      have hik : Agree i k y := by
        by_contra h
        exact hyi.2 (subset_closure ⟨hyi.1, Set.mem_iUnion.mpr ⟨k, hgen, h⟩⟩)
      have hjk : Agree j k y := by
        by_contra h
        exact hyj.2 (subset_closure ⟨hyj.1, Set.mem_iUnion.mpr ⟨k, hgen, h⟩⟩)
      exact agree_trans hik (agree_symm hjk)
    -- Glue the restrictions of the `σ i` to the `W i`.
    obtain ⟨σ', hσ', -⟩ := existsUnique_gluing' F W ⊤ (fun i ↦ homOfLE le_top)
      (fun y _ ↦ by
        obtain ⟨i, hi⟩ := hWcov y
        exact Opens.mem_iSup.mpr ⟨i, hi⟩)
      (fun i ↦ F.1.map (homOfLE (hWU i)).op (σ i)) (fun i j ↦ by
        refine Presheaf.section_ext F _ _ _ fun y hy ↦ ?_
        obtain ⟨_, _, e⟩ := hWagree i j y hy.1 hy.2
        simpa only [Presheaf.germ_res_apply] using e)
    refine ⟨σ', Presheaf.section_ext G _ _ _ fun z hz ↦ ?_⟩
    obtain ⟨i, hzi⟩ := hcov z.1 z.2
    have hzW : z.1 ∈ W i := ⟨hzi, claim₁ i z.1 ⟨z.1, ⟨hzi, z.2⟩, specializes_rfl⟩⟩
    have h₁ : Presheaf.germ F.presheaf ⊤ z.1 True.intro σ' =
        Presheaf.germ F.presheaf (U i) z.1 hzi (σ i) := by
      rw [← Presheaf.germ_res_apply F.presheaf (homOfLE le_top : W i ⟶ ⊤) z.1 hzW, hσ' i,
        Presheaf.germ_res_apply]
    calc _ = φ z (Presheaf.germ F.presheaf ⊤ z.1 True.intro σ') :=
          (hgerm z ⊤ True.intro σ').symm
      _ = φ z (Presheaf.germ F.presheaf (U i) z.1 hzi (σ i)) := by rw [h₁]
      _ = _ := hgerm z (U i) hzi (σ i)
      _ = _ := by
        rw [hσ i]
        exact Presheaf.germ_res_apply G.presheaf _ _ _ t

/-- **Zariski restriction on a spectral space.** Let `T` be a spectral space and `T₀ ⊆ T` a
closed subset such that every irreducible closed subset `C ⊆ T` meets `T₀` in a nonempty
connected set. Then for every sheaf of abelian groups `F` on `T`, the restriction map
`Γ(T, F) ⟶ Γ(T₀, F|_{T₀})`, the unit of the adjunction `i⁻¹ ⊣ i_*` for the inclusion
`i : T₀ ⟶ T` evaluated on `T`, is bijective. The blueprint states this for locally constant
sheaves only; it holds for all abelian sheaves.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
@[stacks 09ZG]
theorem bijective_unit_app_top (hT₀ : IsClosed T₀)
    (hC : ∀ C : Set T, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    (F : T.Sheaf AddCommGrpCat.{u}) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of T₀ ⟶ T)).unit.app
          F).hom.app (op ⊤)).hom := by
  have : (Opens.map ι₀).IsContinuous (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology (TopCat.of T₀)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map ι₀)
      (coverPreserving_opens_map ι₀)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map ι₀)
    AddCommGrpCat.{u} (Opens.grothendieckTopology T) (Opens.grothendieckTopology (TopCat.of T₀))
  have hb : Function.Bijective ((adj.unit.app F).hom.app (op ⊤)) := by
    refine bijective_app_top_of_bijective_stalk hT₀ hC (adj.unit.app F).hom
      (fun z ↦ Presheaf.stalkPullbackHom _ ι₀ F.1 z ≫
        (Presheaf.stalkFunctor (X := TopCat.of T₀) AddCommGrpCat.{u} z).map
          (toSheafify (Opens.grothendieckTopology (TopCat.of T₀))
            ((Presheaf.pullback _ ι₀).obj F.1))) (fun z ↦ ?_) (fun z U hz s ↦ ?_)
    · have : IsIso (Presheaf.stalkPullbackHom AddCommGrpCat.{u} ι₀ F.1 z) :=
        (Presheaf.stalkPullbackIso AddCommGrpCat.{u} ι₀ F.1 z).isIso_hom
      have := Presheaf.stalkFunctor_map_unit_toSheafify_isIso z AddCommGrpCat.{u}
        ((Presheaf.pullback _ ι₀).obj F.1)
      exact ConcreteCategory.bijective_of_isIso _
    · have hu : (adj.unit.app F).hom.app (op U) =
          ((Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₀).unit.app F.1).app
              (op U) ≫
            (toSheafify (Opens.grothendieckTopology (TopCat.of T₀))
              ((Presheaf.pullback _ ι₀).obj F.1)).app (op ((Opens.map ι₀).obj U)) := rfl
      have h₁ := ConcreteCategory.congr_hom
        (Presheaf.germ_stalkPullbackHom AddCommGrpCat.{u} ι₀ F.1 z U hz) s
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₁
      rw [hu, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      erw [h₁]
      exact Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₀) adj F
  have key : (adj.unit.app F).hom.app (op ⊤) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₀).unit.app F).hom.app
        (op ⊤) ≫ ((Sheaf.pushforward _ ι₀).map ((Adjunction.leftAdjointUniq
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₀) adj).hom.app
            F)).hom.app (op ⊤) := by
    rw [← hunit]
    rfl
  rw [key] at hb
  set a := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₀).unit.app
    F).hom.app (op ⊤)
  set b := ((Sheaf.pushforward _ ι₀).map ((Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₀) adj).hom.app
      F)).hom.app (op ⊤)
  have hcomp : ⇑(ConcreteCategory.hom (a ≫ b)) =
      ⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a) :=
    funext fun x ↦ ConcreteCategory.comp_apply _ _ x
  replace hb : Function.Bijective (⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a)) :=
    hcomp ▸ hb
  exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso b) _).mp hb

end TopCat.Sheaf
