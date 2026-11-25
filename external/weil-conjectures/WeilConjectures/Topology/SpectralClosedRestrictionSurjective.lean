/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Topology.SpectralSpace.Constructible

/-! # Surjectivity of spectral closed restriction, Stacks Tag 09ZG -/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Germ-and-gluing criterion, adapted to sheaves of sets from
`TopCat.Sheaf.bijective_app_top_of_bijective_stalk` in the source library.
Only connectedness of point closures is used. -/
private theorem restriction_bijective_of_stalk
    {T : TopCat.{u}} [SpectralSpace T] {T₀ : Set T} (hT₀ : IsClosed T₀)
    (hC : ∀ y : T, IsConnected (closure ({y} : Set T) ∩ T₀))
    {F : T.Sheaf (Type u)} {G : (TopCat.of T₀).Sheaf (Type u)}
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
    obtain ⟨z, hz, hz₀⟩ := (hC y).nonempty
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
        (hC y).isPreconnected
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
      (U i : Set T) ∩ ⋃ j,
        (generalizationHull (K j) ∩ {y | Agree i j y}ᶜ)
    have hBd : ∀ i, @IsClosed T (constructibleTopology T) (Bd i) := fun i ↦
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
    obtain ⟨σ', hσ', -⟩ := Sheaf.existsUnique_gluing' F W ⊤ (fun i ↦ homOfLE le_top)
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

/-- Source: Stacks Project, Etale Cohomology, Lemma 59.82.1 (Tag 09ZG),
its finite constant-sheaf, subsheaf and filtered-colimit arguments.
(blueprint: lem-weil-pbc-h0-spectral-closed-restriction-surjective)

Proof:
1. Restriction of locally constant maps with finite values is surjective. Split
   the closed subset by one value of the map. The clopen-decomposition lifting
   lemma lifts this split to the spectral ambient space. Induction on the finite
   number of values gives the extension on each piece, which glues since the
   pieces are open. The empty-value case forces the ambient space to be empty.
2. A finite product of finite constant sheaves pushed forward from closed subsets
   also has surjective restriction. Inverse image preserves finite products.
   For a factor, closed-pushforward restriction identifies the restricted sections
   with locally constant maps on the intersection of the two closed subsets.
   Closed subspaces are spectral, and the connectedness hypothesis is inherited
   because the closure of a point in a closed subspace equals its ambient closure.
   Apply step 1 in each closed subspace and take the product of the lifts.
3. If a sheaf embeds sectionwise into such a product, lift the image of the given
   restricted section to a global product section. At each point of the closed
   subset, the inverse-image stalk comparison gives a local preimage in the
   subsheaf. Equality of germs shrinks the neighbourhood so this preimage maps
   to the chosen product section. Each ambient point specializes to a point of
   the closed subset, so these neighbourhoods cover the ambient space. The local
   preimages agree on overlaps by sectionwise injectivity, hence glue. Inverse
   image preserves this injectivity on stalks and therefore on sections, so the
   glued section restricts to the prescribed section.
4. Present the arbitrary sheaf as the directed colimit of sheaves embedding in
   the finite products of step 2. Inverse image preserves this colimit. The
   closed subset is spectral; its global sections commute with directed colimits
   since finite coverings by compact opens with compact intersections are cofinal.
   Thus the given section comes from one term. Step 3 lifts it globally in that
   term. Apply its cocone map; naturality of the adjunction unit shows that this
   image has the required restriction. -/
theorem spectral_closed_restriction_surjective
    (X : TopCat.{u}) [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, ConnectedSpace (↥(Z ∩ closure ({x} : Set X))))
    (F : X.Sheaf (Type u)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let R := (Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F
    Function.Surjective
      (fun s : F.1.obj (op ⊤) =>
        (R.1.app (op ⊤)) s) := by
  -- Alternative proof: use germs and constructible-topology shrinking, rather than
  -- the finite-constant-sheaf presentation in the original docstring above.
  let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hC (y : X) : IsConnected (closure ({y} : Set X) ∩ Z) := by
    rw [Set.inter_comm]
    exact isConnected_iff_connectedSpace.mpr (hconn y)
  have hbij : Function.Bijective
      (((Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F).hom.app (op ⊤)) := by
    have : (Opens.map i).IsContinuous (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (TopCat.of Z)) :=
      Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map i)
        (coverPreserving_opens_map i)
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map i)
      (Type u) (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))
    have hb : Function.Bijective ((adj.unit.app F).hom.app (op ⊤)) := by
      refine restriction_bijective_of_stalk hZ hC (adj.unit.app F).hom
        (fun z ↦ Presheaf.stalkPullbackHom _ i F.1 z ≫
          (Presheaf.stalkFunctor (X := TopCat.of Z) (Type u) z).map
            (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
              ((Presheaf.pullback _ i).obj F.1))) (fun z ↦ ?_) (fun z U hz s ↦ ?_)
      · have : IsIso (Presheaf.stalkPullbackHom (Type u) i F.1 z) :=
          (Presheaf.stalkPullbackIso (Type u) i F.1 z).isIso_hom
        have := Presheaf.stalkFunctor_map_unit_toSheafify_isIso z (Type u)
          ((Presheaf.pullback _ i).obj F.1)
        exact ConcreteCategory.bijective_of_isIso _
      · have hu : (adj.unit.app F).hom.app (op U) =
            ((Presheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F.1).app
                (op U) ≫
              (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
                ((Presheaf.pullback _ i).obj F.1)).app (op ((Opens.map i).obj U)) := rfl
        have h₁ := ConcreteCategory.congr_hom
          (Presheaf.germ_stalkPullbackHom (Type u) i F.1 z U hz) s
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₁
        rw [hu, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        erw [h₁]
        exact Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
    have hunit := Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i) adj F
    have key : (adj.unit.app F).hom.app (op ⊤) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F).hom.app
          (op ⊤) ≫ ((Sheaf.pushforward _ i).map ((Adjunction.leftAdjointUniq
            (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i) adj).hom.app
              F)).hom.app (op ⊤) := by
      rw [← hunit]
      rfl
    rw [key] at hb
    set a := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app
      F).hom.app (op ⊤)
    set b := ((Sheaf.pushforward _ i).map ((Adjunction.leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i) adj).hom.app
        F)).hom.app (op ⊤)
    change Function.Bijective (b ∘ a) at hb
    exact (Function.Bijective.of_comp_iff'
      ((CategoryTheory.isIso_iff_bijective b).mp inferInstance) _).mp hb
  exact hbij.2

end TopCat
