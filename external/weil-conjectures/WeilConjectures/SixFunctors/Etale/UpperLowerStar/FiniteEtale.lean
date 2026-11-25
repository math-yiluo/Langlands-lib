/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The direct image along a finite étale morphism is left adjoint to the pullback

Let `f : X ⟶ Y` be separated and étale. For an étale `X`-scheme `u : U ⟶ X` the graph
`Γ_u : U ⟶ U ×_Y X` is a section of the separated étale projection `U ×_Y X ⟶ U`, hence an open
and closed immersion. A sheaf `G` on `X_ét` therefore has
`G(U ×_Y X) = G(U) × G(U ×_Y X ∖ Γ_u)`, and extending a section of `G` over `U` by zero
off the graph defines a natural map

`η_G : G ⟶ f^* f_* G`,

a section of the counit `f^* f_* G ⟶ G`, which is restriction to the graph.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.isLimitBinaryFanOfIsCompl`: the sections of a sheaf on the
  small étale site over an object split as a product along a decomposition into two
  complementary open subschemes.
- `AlgebraicGeometry.Etale.lowerStarUnit`: the extension by zero off the graphs
  `η_G : G ⟶ f^* f_* G`.
- `AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`: for a finite étale `f`, the
  adjunction `f_* ⊣ f^*` with unit `η`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_lowerStarUnit_comp_map`: for a finite étale `f`, every
  morphism `G ⟶ f^* F` factors uniquely as `η_G ≫ f^* φ`. For concrete coefficients this
  follows from the comparison `f_! G ⟶ f_* G` with the extension by zero
  `AlgebraicGeometry.Etale.etaleLowerShriek` being an isomorphism, checked on stalks; the
  general case reduces to abelian groups via `Hom(a, -)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] {X : Scheme.{u}}

section Clopen

variable (G : Sheaf X.smallEtaleTopology A) {P U W : X.Etale} (i : U ⟶ P) (j : W ⟶ P)
  [IsOpenImmersion i.left] [IsOpenImmersion j.left]
  (h : IsCompl (Set.range i.left.base) (Set.range j.left.base))

include h in
/-- The sections of a sheaf on the small étale site over `P` are determined by their
restrictions to two complementary open subschemes `U` and `W` of `P`, and any pair of sections
over `U` and `W` glues. -/
lemma Etale.existsUnique_of_isCompl {a : A} (s : a ⟶ G.obj.obj (op U))
    (t : a ⟶ G.obj.obj (op W)) :
    ∃! σ : a ⟶ G.obj.obj (op P), σ ≫ G.obj.map i.op = s ∧ σ ≫ G.obj.map j.op = t := by
  let Z : Bool → X.Etale := fun b ↦ bif b then U else W
  let π : ∀ b, Z b ⟶ P := fun b ↦ match b with
    | true => i
    | false => j
  have hcov : Sieve.ofArrows Z π ∈ X.smallEtaleTopology P := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    have hx : x ∈ Set.range i.left.base ∪ Set.range j.left.base := by
      have h₀ : x ∈ (⊤ : Set P.left) := trivial
      rwa [← h.sup_eq_top] at h₀
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have hsh := (G.property a).isSheafFor (Presieve.ofArrows Z π) hcov
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  let x : ∀ b, (G.obj ⋙ coyoneda.obj (op a)).obj (op (Z b)) := fun b ↦ match b with
    | true => s
    | false => t
  have hmono : Mono i := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono i.left).1 (congrArg (fun g ↦ g.left) hg :))⟩
  have hmono' : Mono j := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono j.left).1 (congrArg (fun g ↦ g.left) hg :))⟩
  -- maps into both `U` and `W` over `P` have empty source
  have hempty {T : X.Etale} (g₁ : T ⟶ U) (g₂ : T ⟶ W) (hg : g₁ ≫ i = g₂ ≫ j) :
      IsEmpty T.left := by
    refine ⟨fun z ↦ ?_⟩
    have h₁ : i.left (g₁.left z) = j.left (g₂.left z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun g ↦ g.left z) hg
    have h₂ : j.left (g₂.left z) ∈ Set.range i.left := ⟨_, h₁⟩
    exact Set.disjoint_iff.1 h.disjoint ⟨h₂, ⟨_, rfl⟩⟩
  obtain ⟨σ, hσ, hσu⟩ := hsh x (by
    intro b b' T g₁ g₂ hg
    have hsub : ∀ (T : X.Etale) [IsEmpty T.left] (c c' : a ⟶ G.obj.obj (op T)), c = c' :=
      fun T _ c c' ↦ (Etale.isTerminalSectionsOfIsEmpty G T).hom_ext _ _
    cases b <;> cases b'
    · obtain rfl : g₁ = g₂ := (cancel_mono j).1 hg
      rfl
    · have := hempty g₂ g₁ hg.symm
      exact hsub _ _ _
    · have := hempty g₁ g₂ hg
      exact hsub _ _ _
    · obtain rfl : g₁ = g₂ := (cancel_mono i).1 hg
      rfl)
  refine ⟨σ, ⟨hσ true, hσ false⟩, fun σ' hσ' ↦ hσu σ' ?_⟩
  rintro (_ | _)
  · exact hσ'.2
  · exact hσ'.1

/-- The sections of a sheaf on the small étale site over `P` are the product of its sections
over two complementary open subschemes `U` and `W` of `P`. -/
noncomputable def Etale.isLimitBinaryFanOfIsCompl :
    IsLimit (BinaryFan.mk (G.obj.map i.op) (G.obj.map j.op)) :=
  BinaryFan.IsLimit.mk _
    (fun s t ↦ (Etale.existsUnique_of_isCompl G i j h s t).exists.choose)
    (fun s t ↦ (Etale.existsUnique_of_isCompl G i j h s t).exists.choose_spec.1)
    (fun s t ↦ (Etale.existsUnique_of_isCompl G i j h s t).exists.choose_spec.2)
    (fun s t _ h₁ h₂ ↦ (Etale.existsUnique_of_isCompl G i j h s t).unique ⟨h₁, h₂⟩
      (Etale.existsUnique_of_isCompl G i j h s t).exists.choose_spec)

end Clopen

section Graph

variable {Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Etale f] [IsSeparated f]

/-- For an étale `X`-scheme `U`, the étale `X`-scheme `U ×_Y X`, with structure morphism the
second projection: the sections of `f^* f_* G` over `U` are the sections of `G` over it. -/
noncomputable abbrev Etale.graphTarget (U : X.Etale) : X.Etale :=
  f.Etale.obj ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U)

/-- The graph `U ⟶ U ×_Y X` of the structure morphism of an étale `X`-scheme `U`, the unit of
the adjunction between `MorphismProperty.Over.map` and base change along `f`. -/
noncomputable def Etale.graph (U : X.Etale) : U ⟶ Etale.graphTarget f U :=
  (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ f
    ‹AlgebraicGeometry.Etale f› _root_.trivial).unit.app U

omit [IsSeparated f] in
lemma Etale.graph_left (U : X.Etale) :
    (Etale.graph f U).left = pullback.lift (𝟙 U.left) U.hom (by simp) := rfl


omit [IsSeparated f] in
@[reassoc (attr := simp)]
lemma Etale.graph_left_snd (U : X.Etale) :
    (Etale.graph f U).left ≫
      pullback.snd ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U).hom f =
        U.hom := by
  exact pullback.lift_snd _ _ _

omit [IsSeparated f] in
@[reassoc (attr := simp)]
lemma Etale.graph_left_fst (U : X.Etale) :
    (Etale.graph f U).left ≫
      pullback.fst ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U).hom f =
        𝟙 U.left := by
  exact pullback.lift_fst _ _ _

instance (U : X.Etale) : IsOpenImmersion (Etale.graph f U).left :=
  IsOpenImmersion.of_section_of_etale (pullback.fst (U.hom ≫ f) f) _ (Etale.graph_left_fst f U)

lemma Etale.isClosed_range_graph_left (U : X.Etale) :
    IsClosed (Set.range (Etale.graph f U).left) :=
  (IsClosedImmersion.of_section_of_isSeparated (pullback.fst (U.hom ≫ f) f) _
    (Etale.graph_left_fst f U)).isClosedEmbedding.isClosed_range

/-- The open subscheme of `U ×_Y X` complementary to the graph of `U ⟶ X`. -/
noncomputable def Etale.graphCompl (U : X.Etale) : (Etale.graphTarget f U).left.Opens :=
  ⟨(Set.range (Etale.graph f U).left)ᶜ, (Etale.isClosed_range_graph_left f U).isOpen_compl⟩

/-- The complement of the graph of `U ⟶ X` in `U ×_Y X`, as an étale `X`-scheme. -/
noncomputable abbrev Etale.graphComplObj (U : X.Etale) : X.Etale :=
  MorphismProperty.Over.mk ⊤ ((Etale.graphCompl f U).ι ≫ (Etale.graphTarget f U).hom)
    inferInstance

/-- The inclusion of the complement of the graph of `U ⟶ X` into `U ×_Y X`. -/
noncomputable abbrev Etale.graphComplι (U : X.Etale) :
    Etale.graphComplObj f U ⟶ Etale.graphTarget f U :=
  MorphismProperty.Over.homMk (Etale.graphCompl f U).ι rfl trivial

instance (U : X.Etale) : IsOpenImmersion (Etale.graphComplι f U).left :=
  inferInstanceAs (IsOpenImmersion (Etale.graphCompl f U).ι)

lemma Etale.isCompl_range_graph (U : X.Etale) :
    IsCompl (Set.range (Etale.graph f U).left) (Set.range (Etale.graphComplι f U).left) := by
  change IsCompl _ (Set.range (Etale.graphCompl f U).ι)
  rw [Scheme.Opens.range_ι]
  exact isCompl_compl

omit [IsSeparated f] in
lemma Etale.graph_comp_map {U U' : X.Etale} (φ : U' ⟶ U) :
    (Etale.graph f U').left ≫
        (f.Etale.map ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map φ)).left =
      φ.left ≫ (Etale.graph f U).left :=
  (congrArg (fun g ↦ g.left) ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤
    f ‹AlgebraicGeometry.Etale f› _root_.trivial).unit.naturality φ)).symm

omit [IsSeparated f] in
/-- The graphs are compatible with base change: for `φ : U' ⟶ U` the square
```
U' ──graph──→ U' ×_Y X
│φ               │φ × 𝟙
U ───graph──→ U ×_Y X
```
is cartesian. -/
lemma Etale.isPullback_graph {U U' : X.Etale} (φ : U' ⟶ U) :
    IsPullback (Etale.graph f U').left φ.left
      (f.Etale.map ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map φ)).left
      (Etale.graph f U).left := by
  refine IsPullback.of_isLimit' ⟨Etale.graph_comp_map f φ⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ s.fst ≫ pullback.fst _ _) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ _ ↦ ?_))
  · have h₁ : (f.Etale.map ((MorphismProperty.Over.map ⊤
        ‹AlgebraicGeometry.Etale f›).map φ)).left ≫ pullback.fst _ f =
        pullback.fst _ f ≫ φ.left :=
      Hom.etale_map_left_comp_fst f _
    have h₂ := Hom.etale_map_left_comp_snd f ((MorphismProperty.Over.map ⊤
      ‹AlgebraicGeometry.Etale f›).map φ)
    have hc := s.condition
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Etale.graph_left_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, Etale.graph_left_snd, ← h₂, reassoc_of% hc,
        Etale.graph_left_snd, ← MorphismProperty.Over.w φ, ← reassoc_of% h₁,
        reassoc_of% hc, Etale.graph_left_fst_assoc]
  · have h₁ : (f.Etale.map ((MorphismProperty.Over.map ⊤
        ‹AlgebraicGeometry.Etale f›).map φ)).left ≫ pullback.fst _ f =
        pullback.fst _ f ≫ φ.left :=
      Hom.etale_map_left_comp_fst f _
    rw [Category.assoc, ← h₁, reassoc_of% s.condition, Etale.graph_left_fst, Category.comp_id]
  · rw [← h₁, Category.assoc, Etale.graph_left_fst, Category.comp_id]

/-- The base change `U' ×_Y X ⟶ U ×_Y X` of a morphism `φ : U' ⟶ U` of étale `X`-schemes. -/
noncomputable abbrev Etale.graphTargetMap {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graphTarget f U' ⟶ Etale.graphTarget f U :=
  f.Etale.map ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map φ)

omit [IsSeparated f] in
lemma Etale.graph_comp_graphTargetMap {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graph f U' ≫ Etale.graphTargetMap f φ = φ ≫ Etale.graph f U :=
  MorphismProperty.Over.Hom.ext (Etale.graph_comp_map f φ)

/-- The base change of a morphism of étale `X`-schemes carries the complement of the graph into
the complement of the graph. -/
noncomputable def Etale.graphComplMap {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graphComplObj f U' ⟶ Etale.graphComplObj f U :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift (Etale.graphComplι f U).left
    ((Etale.graphComplι f U').left ≫ (Etale.graphTargetMap f φ).left) (by
      rintro _ ⟨z, rfl⟩
      change _ ∈ Set.range (Etale.graphCompl f U).ι
      rw [Scheme.Opens.range_ι]
      intro hz
      have h := Scheme.range_snd_of_isPullback (Etale.isPullback_graph f φ).flip
      have hz' : (Etale.graphComplι f U').left z ∈ Set.range (Etale.graph f U').left := by
        rw [h]
        exact hz
      have : (Etale.graphComplι f U').left z ∈ Etale.graphCompl f U' := z.2
      exact this hz')) (by
        change _ ≫ (Etale.graphComplι f U).left ≫ _ = (Etale.graphComplι f U').left ≫ _
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
          MorphismProperty.Over.w]) trivial

@[reassoc (attr := simp)]
lemma Etale.graphComplMap_comp_graphComplι {U U' : X.Etale} (φ : U' ⟶ U) :
    Etale.graphComplMap f φ ≫ Etale.graphComplι f U =
      Etale.graphComplι f U' ≫ Etale.graphTargetMap f φ :=
  MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

end Graph

section Unit

variable {Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Etale f] [IsSeparated f]
  [HasZeroMorphisms A] (G : Sheaf X.smallEtaleTopology A)

omit [HasZeroMorphisms A] in
lemma Etale.graph_hom_ext {U : X.Etale} {a : A} {σ σ' : a ⟶ G.obj.obj (op (Etale.graphTarget f U))}
    (h₁ : σ ≫ G.obj.map (Etale.graph f U).op = σ' ≫ G.obj.map (Etale.graph f U).op)
    (h₂ : σ ≫ G.obj.map (Etale.graphComplι f U).op = σ' ≫ G.obj.map (Etale.graphComplι f U).op) :
    σ = σ' :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) _ _).unique
    ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

/-- The extension by zero of a section of `G` over an étale `X`-scheme `U` to `U ×_Y X`: the
section restricting to the given one on the graph of `U ⟶ X` and to zero off it. -/
noncomputable def Etale.graphExtend (U : X.Etale) :
    G.obj.obj (op U) ⟶ G.obj.obj (op (Etale.graphTarget f U)) :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) (𝟙 _) 0).exists.choose

@[reassoc (attr := simp)]
lemma Etale.graphExtend_graph (U : X.Etale) :
    Etale.graphExtend f G U ≫ G.obj.map (Etale.graph f U).op = 𝟙 _ :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) (𝟙 _) 0).exists.choose_spec.1

@[reassoc (attr := simp)]
lemma Etale.graphExtend_graphComplι (U : X.Etale) :
    Etale.graphExtend f G U ≫ G.obj.map (Etale.graphComplι f U).op = 0 :=
  (Etale.existsUnique_of_isCompl G _ _ (Etale.isCompl_range_graph f U) (𝟙 _) 0).exists.choose_spec.2

@[reassoc]
lemma Etale.graphExtend_naturality {U U' : X.Etale} (φ : U' ⟶ U) :
    G.obj.map φ.op ≫ Etale.graphExtend f G U' =
      Etale.graphExtend f G U ≫ G.obj.map (Etale.graphTargetMap f φ).op := by
  refine Etale.graph_hom_ext f G ?_ ?_
  · rw [Category.assoc, Etale.graphExtend_graph, Category.comp_id, Category.assoc,
      ← Functor.map_comp, ← op_comp, Etale.graph_comp_graphTargetMap, op_comp,
      Functor.map_comp, Etale.graphExtend_graph_assoc]
  · rw [Category.assoc, Etale.graphExtend_graphComplι, comp_zero, Category.assoc,
      ← Functor.map_comp, ← op_comp, ← Etale.graphComplMap_comp_graphComplι, op_comp,
      Functor.map_comp, Etale.graphExtend_graphComplι_assoc, zero_comp]

lemma Etale.graphExtend_natural {G G' : Sheaf X.smallEtaleTopology A} (ψ : G ⟶ G')
    (U : X.Etale) :
    ψ.hom.app (op U) ≫ Etale.graphExtend f G' U =
      Etale.graphExtend f G U ≫ ψ.hom.app (op (Etale.graphTarget f U)) := by
  refine Etale.graph_hom_ext f G' ?_ ?_
  · rw [Category.assoc, Etale.graphExtend_graph, Category.comp_id, Category.assoc,
      ← ψ.hom.naturality, Etale.graphExtend_graph_assoc]
  · rw [Category.assoc, Etale.graphExtend_graphComplι, comp_zero, Category.assoc,
      ← ψ.hom.naturality, Etale.graphExtend_graphComplι_assoc, zero_comp]
end Unit

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Etale



variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [AlgebraicGeometry.Etale f] [IsSeparated f]

/-- For a separated étale `f : X ⟶ Y`, extension by zero off the graphs is a natural map
`G ⟶ f^* f_* G`, where `f^*` is computed as the restriction along `X_ét ⟶ Y_ét`. It is a
section of the counit of `f^* ⊣ f_*` (`AlgebraicGeometry.Etale.lowerStarUnit_comp_counit`), and
for a finite étale `f` it is the unit of an adjunction `f_* ⊣ f^*`. -/
noncomputable def Etale.lowerStarUnit :
    𝟭 (Sheaf X.smallEtaleTopology A) ⟶ (f)_*[A] ⋙ Etale.localizationRestriction A f ‹_› where
  app G := ObjectProperty.homMk
    { app U := Scheme.Etale.graphExtend f G U.unop
      naturality _ _ φ := Scheme.Etale.graphExtend_naturality f G φ.unop }
  naturality _ _ ψ := by
    ext U
    exact Scheme.Etale.graphExtend_natural f ψ U.unop

omit [IsGrothendieckAbelian.{u + 1} A] in
lemma Etale.lowerStarUnit_app_hom_app (G : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((Etale.lowerStarUnit A f).app G).hom.app U = Scheme.Etale.graphExtend f G U.unop :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [IsSeparated f] in
lemma Etale.localizationRestrictionLowerStarAdjunction_counit_app_hom_app
    (G : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((Etale.localizationRestrictionLowerStarAdjunction A f ‹_›).counit.app G).hom.app U =
      G.obj.map (Scheme.Etale.graph f U.unop).op := by
  simp [Etale.localizationRestrictionLowerStarAdjunction, Scheme.Etale.graph]

omit [IsGrothendieckAbelian.{u + 1} A] in
/-- Extension by zero off the graphs is a section of the counit of `f^* ⊣ f_*`, which is
restriction to the graphs: the composite
```
G ──η_G──▶ f^* f_* G ──ε_G──▶ G
```
is the identity of `G`. -/
@[reassoc (attr := simp)]
lemma Etale.lowerStarUnit_comp_counit :
    Etale.lowerStarUnit A f ≫ (Etale.localizationRestrictionLowerStarAdjunction A f ‹_›).counit =
      𝟙 _ := by
  ext G U
  simp [Etale.localizationRestrictionLowerStarAdjunction_counit_app_hom_app,
    Etale.lowerStarUnit_app_hom_app]

section Stalk

variable [HasSmallSiteSheafify A] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

/-- A geometric point of an étale `X`-scheme `U` over `t` is a geometric point of `U` over
`t ≫ f`, regarded as an étale `Y`-scheme. -/
noncomputable def Etale.fiberMapPoint (t : Scheme.Hom.GeometricFiber f y) (U : X.Etale)
    (x : (Scheme.pointSmallEtale t.1).fiber.obj U) :
    (Scheme.pointSmallEtale y).fiber.obj
      ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U) :=
  CategoryTheory.Over.homMk x.left (by
    change x.left ≫ U.hom ≫ f = y
    have hx : x.left ≫ U.hom = t.1 := CategoryTheory.Over.w x
    rw [← Category.assoc, hx]
    exact t.2)

/-- The germ at a geometric point `t` of `X` over `y` of a section of `G` is sent to the germ
at `y` of its extension by zero off the graph: a map `G_t ⟶ (f_* G)_y`. -/
noncomputable def Etale.sheafFiberToLowerStar (t : Scheme.Hom.GeometricFiber f y)
    (G : Sheaf X.smallEtaleTopology A) :
    (Scheme.pointSmallEtale t.1).sheafFiber.obj G ⟶
      (Scheme.pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) :=
  (Scheme.pointSmallEtale t.1).presheafFiberDesc
    (fun U x ↦ Scheme.Etale.graphExtend f G U ≫
      (Scheme.pointSmallEtale y).toPresheafFiber _ (Etale.fiberMapPoint f t U x)
        ((f)_*[A].obj G).obj)
    (fun U V g x ↦ by
      change G.obj.map g.op ≫ _ ≫ _ = _
      rw [Scheme.Etale.graphExtend_naturality_assoc]
      exact congrArg (Scheme.Etale.graphExtend f G V ≫ ·)
        ((Scheme.pointSmallEtale y).toPresheafFiber_w
          ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).map g) _
            ((f)_*[A].obj G).obj))


omit [HasSmallSiteSheafify A] in
@[reassoc (attr := simp)]
lemma Etale.toPresheafFiber_sheafFiberToLowerStar (t : Scheme.Hom.GeometricFiber f y)
    (G : Sheaf X.smallEtaleTopology A) (U : X.Etale)
    (x : (Scheme.pointSmallEtale t.1).fiber.obj U) :
    (Scheme.pointSmallEtale t.1).toPresheafFiber U x G.obj ≫ Etale.sheafFiberToLowerStar A f t G =
      Scheme.Etale.graphExtend f G U ≫
        (Scheme.pointSmallEtale y).toPresheafFiber _ (Etale.fiberMapPoint f t U x)
          ((f)_*[A].obj G).obj :=
  (Scheme.pointSmallEtale t.1).toPresheafFiber_presheafFiberDesc _ _ U x

omit [IsSeparated f] in
/-- The point `(u, t')` of `U ×_Y X` attached to a geometric point `u` of `U` over `t` and a
geometric point `t'` of `X` over `y`. -/
lemma Etale.basePt_fiberMapPoint (t t' : Scheme.Hom.GeometricFiber f y) (U : X.Etale)
    (x : (Scheme.pointSmallEtale t.1).fiber.obj U) :
    Scheme.Hom.basePt f (Functor.elementsMk _ _ (Etale.fiberMapPoint f t U x)) t' =
      pullback.lift x.left t'.1 (by
        have hx : x.left ≫ U.hom = t.1 := CategoryTheory.Over.w x
        change x.left ≫ U.hom ≫ f = _
        rw [← Category.assoc, hx, t.2, t'.2]) :=
  rfl

omit [HasSmallSiteSheafify A] in
/-- Restricting the germ of the extension by zero of a section back to `t` gives the germ of
the section. -/
@[reassoc (attr := simp)]
lemma Etale.sheafFiberToLowerStar_stalkRestrict (t : Scheme.Hom.GeometricFiber f y)
    (G : Sheaf X.smallEtaleTopology A) :
    Etale.sheafFiberToLowerStar A f t G ≫ Etale.stalkRestrict A f y t G = 𝟙 _ := by
  apply (Scheme.pointSmallEtale t.1).presheafFiber_hom_ext
  intro U x
  refine Eq.trans ?_ (Category.comp_id _).symm
  erw [Etale.toPresheafFiber_sheafFiberToLowerStar_assoc]
  rw [Etale.toPresheafFiber_stalkRestrict A f y t G
    (Functor.elementsMk _ _ (Etale.fiberMapPoint f t U x))]
  have hx : x.left ≫ U.hom = t.1 := CategoryTheory.Over.w x
  have : ((Etale.baseChangeNbhd f y t).obj
      (Functor.elementsMk _ _ (Etale.fiberMapPoint f t U x))).2 =
      (Scheme.pointSmallEtale t.1).fiber.map (Scheme.Etale.graph f U) x := by
    refine CategoryTheory.Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · change Scheme.Hom.basePt f _ t ≫ _ = (x.left ≫ (Scheme.Etale.graph f U).left) ≫ _
      rw [Category.assoc, Scheme.Etale.graph_left_fst]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _).symm
    · change Scheme.Hom.basePt f _ t ≫ _ = (x.left ≫ (Scheme.Etale.graph f U).left) ≫ _
      rw [Category.assoc, Scheme.Etale.graph_left_snd, hx]
      exact pullback.lift_snd _ _ _
  rw [this]
  rw [← (Scheme.pointSmallEtale t.1).toPresheafFiber_w (Scheme.Etale.graph f U) x G.obj]
  exact Scheme.Etale.graphExtend_graph_assoc f G U _

omit [HasSmallSiteSheafify A] in
/-- Restricting the germ of the extension by zero of a section to a geometric point `t'` other
than `t` gives zero: the point `(u, t')` of `U ×_Y X` lies off the graph of `U ⟶ X`. -/
@[reassoc (attr := simp)]
lemma Etale.sheafFiberToLowerStar_stalkRestrict_of_ne {t t' : Scheme.Hom.GeometricFiber f y}
    (htt' : t ≠ t') (G : Sheaf X.smallEtaleTopology A) :
    Etale.sheafFiberToLowerStar A f t G ≫ Etale.stalkRestrict A f y t' G = 0 := by
  apply (Scheme.pointSmallEtale t.1).presheafFiber_hom_ext
  intro U x
  refine Eq.trans ?_ (comp_zero).symm
  erw [Etale.toPresheafFiber_sheafFiberToLowerStar_assoc]
  rw [Etale.toPresheafFiber_stalkRestrict A f y t' G
    (Functor.elementsMk _ _ (Etale.fiberMapPoint f t U x))]
  have hx : x.left ≫ U.hom = t.1 := CategoryTheory.Over.w x
  let b := Scheme.Hom.basePt f (Functor.elementsMk _ _ (Etale.fiberMapPoint f t U x)) t'
  -- the point `(u, t')` lies off the graph
  have hb : Set.range b ⊆ Set.range (Scheme.Etale.graphComplι f U).left := by
    rintro _ ⟨p, rfl⟩
    change _ ∈ Set.range (Scheme.Etale.graphCompl f U).ι
    rw [Scheme.Opens.range_ι]
    rintro ⟨q, hq⟩
    have hsub : Set.range b ⊆ Set.range (Scheme.Etale.graph f U).left := by
      rintro _ ⟨p', rfl⟩
      rw [Subsingleton.elim p' p]
      exact ⟨q, hq⟩
    let v := IsOpenImmersion.lift (Scheme.Etale.graph f U).left b hsub
    have hv : v ≫ (Scheme.Etale.graph f U).left = b := IsOpenImmersion.lift_fac _ _ _
    have h₁ : v = x.left := by
      have := congrArg (· ≫ pullback.fst _ f) hv
      simp only [Category.assoc, Scheme.Etale.graph_left_fst, Category.comp_id] at this
      exact this.trans (pullback.lift_fst _ _ _)
    have h₂ : v ≫ U.hom = t'.1 := by
      have := congrArg (· ≫ pullback.snd _ f) hv
      simp only [Category.assoc, Scheme.Etale.graph_left_snd] at this
      exact this.trans (pullback.lift_snd _ _ _)
    exact htt' (Subtype.ext (hx.symm.trans (h₁ ▸ h₂)))
  let w : (Scheme.pointSmallEtale t'.1).fiber.obj (Scheme.Etale.graphComplObj f U) :=
    CategoryTheory.Over.homMk (IsOpenImmersion.lift (Scheme.Etale.graphComplι f U).left b hb)
      (by
        change _ ≫ (Scheme.Etale.graphComplι f U).left ≫ _ = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact pullback.lift_snd _ _ _)
  have : ((Etale.baseChangeNbhd f y t').obj
      (Functor.elementsMk _ _ (Etale.fiberMapPoint f t U x))).2 =
      (Scheme.pointSmallEtale t'.1).fiber.map (Scheme.Etale.graphComplι f U) w :=
    CategoryTheory.Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _).symm
  rw [this]
  rw [← (Scheme.pointSmallEtale t'.1).toPresheafFiber_w (Scheme.Etale.graphComplι f U) w G.obj]
  rw [Scheme.Etale.graphExtend_graphComplι_assoc f G U]
  exact zero_comp
end Stalk

section Skyscraper

attribute [local instance] Abelian.hasFiniteBiproducts

variable [HasSmallSiteSheafify A] [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (G : Sheaf X.smallEtaleTopology A)

/-- The germs of extensions by zero identify the direct sum of the stalks of `G` at the
geometric points over `y` with the stalk of `f_* G` at `y`. -/
noncomputable def Etale.biproductSheafFiberToLowerStar :
    (⨁ fun t : Scheme.Hom.GeometricFiber f y ↦ (Scheme.pointSmallEtale t.1).sheafFiber.obj G) ⟶
      (Scheme.pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) :=
  biproduct.desc fun t ↦ Etale.sheafFiberToLowerStar A f t G

omit [HasSmallSiteSheafify A] in
lemma Etale.biproductSheafFiberToLowerStar_comp_lift_stalkRestrict :
    Etale.biproductSheafFiberToLowerStar A f y G ≫
        biproduct.lift (fun t ↦ Etale.stalkRestrict A f y t G) = 𝟙 _ := by
  classical
  ext t t'
  simp only [Etale.biproductSheafFiberToLowerStar, biproduct.ι_desc_assoc, Category.assoc,
    biproduct.lift_π, Category.id_comp, biproduct.ι_π]
  by_cases h : t = t'
  · subst h
    simp
  · rw [dite_eq_right (Ne.symm h)]
    exact Etale.sheafFiberToLowerStar_stalkRestrict_of_ne A f (Ne.symm h) G

instance Etale.isIso_biproductSheafFiberToLowerStar :
    IsIso (Etale.biproductSheafFiberToLowerStar A f y G) := by
  have hτ : biproduct.lift (fun t ↦ Etale.stalkRestrict A f y t G) =
      Pi.lift (fun t ↦ Etale.stalkRestrict A f y t G) ≫ (biproduct.isoProduct _).inv := by
    rw [Iso.eq_comp_inv]
    ext t
    simp
  have : IsIso (biproduct.lift (fun t ↦ Etale.stalkRestrict A f y t G)) := by
    rw [hτ]
    infer_instance
  have h := Etale.biproductSheafFiberToLowerStar_comp_lift_stalkRestrict A f y G
  rw [← IsIso.eq_comp_inv, Category.id_comp] at h
  rw [h]
  infer_instance


omit [IsFinite f] [HasSmallSiteSheafify A] in
lemma Etale.lowerStarUnit_comp_map_app_π {M : A}
    (φ : (f)_*[A].obj G ⟶ (Scheme.pointSmallEtale y).skyscraperSheaf M)
    (t : Scheme.Hom.GeometricFiber f y) (U : X.Etale)
    (x : (Scheme.pointSmallEtale t.1).fiber.obj U) :
    ((Etale.lowerStarUnit A f).app G ≫
        (Etale.localizationRestriction A f ‹AlgebraicGeometry.Etale f›).map φ).hom.app (op U) ≫
      Pi.π _ (Etale.fiberMapPoint f t U x) =
    (Scheme.pointSmallEtale t.1).toPresheafFiber U x G.obj ≫
      Etale.sheafFiberToLowerStar A f t G ≫
        ((Scheme.pointSmallEtale y).skyscraperSheafAdjunction.homEquiv _ _).symm φ := by
  erw [GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_symm_apply]
  rw [Etale.toPresheafFiber_sheafFiberToLowerStar_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_skyscraperPresheafHomEquiv_symm]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  rfl

omit [IsFinite f] [HasSmallSiteSheafify A] in
lemma Etale.skyscraperSheaf_map_π {M : A} {V V' : Y.Etale} (g : V ⟶ V')
    (z : (Scheme.pointSmallEtale y).fiber.obj V) :
    ((Scheme.pointSmallEtale y).skyscraperSheaf M).obj.map g.op ≫ Pi.π _ z =
      Pi.π _ ((Scheme.pointSmallEtale y).fiber.map g z) := by
  exact (Pi.map'_comp_π _ _ z).trans (Category.comp_id _)


omit [IsSeparated f] [IsFinite f] in
/-- The geometric point of `U` over `y` underlying a geometric point of `U ⟶ X ⟶ Y`. -/
lemma Etale.exists_fiberMapPoint_eq {U : X.Etale}
    (p : (Scheme.pointSmallEtale y).fiber.obj
      ((MorphismProperty.Over.map ⊤ ‹AlgebraicGeometry.Etale f›).obj U)) :
    ∃ (t : Scheme.Hom.GeometricFiber f y) (x : (Scheme.pointSmallEtale t.1).fiber.obj U),
      Etale.fiberMapPoint f t U x = p := by
  have hp : p.left ≫ U.hom ≫ f = y := CategoryTheory.Over.w p
  exact ⟨⟨p.left ≫ U.hom, by rw [Category.assoc, hp]⟩, CategoryTheory.Over.homMk p.left rfl,
    CategoryTheory.Over.OverMorphism.ext rfl⟩

omit [HasSmallSiteSheafify A] in
/-- **Extension by zero off the graphs is the unit of an adjunction `f_* ⊣ f^*`, tested on
skyscraper sheaves.** For a finite étale `f`, a geometric point `y` of `Y` and `M : A`, every
morphism `G ⟶ f^* (y_* M)` is `η_G ≫ f^* φ` for a unique `φ : f_* G ⟶ y_* M`. -/
lemma Etale.bijective_lowerStarUnit_comp_map_skyscraperSheaf (M : A) :
    Function.Bijective
      (fun φ : (f)_*[A].obj G ⟶ (Scheme.pointSmallEtale y).skyscraperSheaf M ↦
        (Etale.lowerStarUnit A f).app G ≫
          (Etale.localizationRestriction A f ‹AlgebraicGeometry.Etale f›).map φ) := by
  let e := (Scheme.pointSmallEtale y).skyscraperSheafAdjunction.homEquiv ((f)_*[A].obj G) M
  constructor
  · intro φ₁ φ₂ h
    apply e.symm.injective
    rw [← cancel_epi (Etale.biproductSheafFiberToLowerStar A f y G)]
    refine biproduct.hom_ext' _ _ fun t ↦ ?_
    simp only [Etale.biproductSheafFiberToLowerStar, biproduct.ι_desc_assoc]
    apply (Scheme.pointSmallEtale t.1).presheafFiber_hom_ext
    intro U x
    erw [← Etale.lowerStarUnit_comp_map_app_π A f y G φ₁ t U x,
      ← Etale.lowerStarUnit_comp_map_app_π A f y G φ₂ t U x]
    exact congrArg (fun ψ ↦ ψ.hom.app (op U) ≫ _) h
  · intro ψ
    let ψt (t : Scheme.Hom.GeometricFiber f y) :
        (Scheme.pointSmallEtale t.1).sheafFiber.obj G ⟶ M :=
      (Scheme.pointSmallEtale t.1).presheafFiberDesc
        (fun U x ↦ ψ.hom.app (op U) ≫ Pi.π _ (Etale.fiberMapPoint f t U x))
        (fun U V g x ↦ by
          refine (Category.assoc _ _ _).symm.trans ?_
          refine (congrArg (· ≫ Pi.π _ _) (ψ.hom.naturality g.op)).trans ?_
          exact (Category.assoc _ _ _).trans
            (congrArg (ψ.hom.app (op V) ≫ ·) (Etale.skyscraperSheaf_map_π A y _ _)))
    refine ⟨e (inv (Etale.biproductSheafFiberToLowerStar A f y G) ≫ biproduct.desc ψt), ?_⟩
    ext ⟨U⟩ : 3
    refine Pi.hom_ext _ _ fun p ↦ ?_
    obtain ⟨t, x, rfl⟩ := Etale.exists_fiberMapPoint_eq f y p
    rw [Etale.lowerStarUnit_comp_map_app_π A f y G _ t U x, Equiv.symm_apply_apply]
    have : Etale.sheafFiberToLowerStar A f t G =
        biproduct.ι _ t ≫ Etale.biproductSheafFiberToLowerStar A f y G := by
      simp [Etale.biproductSheafFiberToLowerStar]
    rw [this, Category.assoc, IsIso.hom_inv_id_assoc, biproduct.ι_desc]
    exact (Scheme.pointSmallEtale t.1).toPresheafFiber_presheafFiberDesc _ _ U x
end Skyscraper

section LowerShriek

/-- The adjunction `f_! ⊣ f^*` for an étale `f`
(`AlgebraicGeometry.Etale.etaleLowerShriekUpperStarAdjunction`), with `f^*` computed as
restriction along the localization functor `X_ét ⥤ Y_ét`. -/
noncomputable def Etale.etaleLowerShriekRestrictionAdjunction :
    Etale.etaleLowerShriek A f ‹_› ⊣ Etale.localizationRestriction A f ‹_› :=
  (Etale.etaleLowerShriekUpperStarAdjunction A f ‹_›).ofNatIsoRight
    (Etale.upperStarIsoLocalizationRestriction A f ‹_›)

/-- The comparison `f_! G ⟶ f_* G` for a separated étale `f`, adjoint to the extension by
zero off the graphs. -/
noncomputable def Etale.etaleLowerShriekToLowerStar
    (G : Sheaf X.smallEtaleTopology A) :
    (Etale.etaleLowerShriek A f ‹_›).obj G ⟶ (f)_*[A].obj G :=
  ((Etale.etaleLowerShriekRestrictionAdjunction A f).homEquiv _ _).symm
    ((Etale.lowerStarUnit A f).app G)

lemma Etale.etaleLowerShriekRestrictionAdjunction_homEquiv_comp
    (G : Sheaf X.smallEtaleTopology A) {F : Sheaf Y.smallEtaleTopology A}
    (φ : (f)_*[A].obj G ⟶ F) :
    (Etale.etaleLowerShriekRestrictionAdjunction A f).homEquiv _ _
        (Etale.etaleLowerShriekToLowerStar A f G ≫ φ) =
      (Etale.lowerStarUnit A f).app G ≫ (Etale.localizationRestriction A f ‹_›).map φ := by
  rw [Adjunction.homEquiv_naturality_right, Etale.etaleLowerShriekToLowerStar,
    Equiv.apply_symm_apply]

section Concrete

variable [IsFinite f]
  {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)]
  [ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- For a finite étale `f` and coefficients concrete over `Type (u + 1)` compatibly with
filtered colimits, the comparison `f_! G ⟶ f_* G` is an isomorphism: on the stalk at a
geometric point `y`, maps out of it into `M` are the maps `G ⟶ f^* (y_* M)`, by the
skyscraper adjunction and `f_! ⊣ f^*`, and these are the maps `f_* G ⟶ y_* M`
(`AlgebraicGeometry.Etale.bijective_lowerStarUnit_comp_map_skyscraperSheaf`). -/
instance Etale.isIso_etaleLowerShriekToLowerStar (G : Sheaf X.smallEtaleTopology A) :
    IsIso (Etale.etaleLowerShriekToLowerStar A f G) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  let y := Y.algClosurePoint s
  refine (NatIso.isIso_map_iff ((Scheme.pointSmallEtale y).uliftSheafFiberIso A) _).2 ?_
  refine isIso_of_coyoneda_map_bijective _ fun M ↦ ?_
  let adj := (Scheme.pointSmallEtale y).skyscraperSheafAdjunction (A := A)
  have key : (fun k ↦ (Scheme.pointSmallEtale y).sheafFiber.map
      (Etale.etaleLowerShriekToLowerStar A f G) ≫ k) =
      (adj.homEquiv _ M).symm ∘
        ((Etale.etaleLowerShriekRestrictionAdjunction A f).homEquiv _ _).symm ∘
        (fun φ ↦ (Etale.lowerStarUnit A f).app G ≫
          (Etale.localizationRestriction A f ‹_›).map φ) ∘ adj.homEquiv _ M := by
    funext k
    dsimp only [Function.comp_apply]
    rw [← Etale.etaleLowerShriekRestrictionAdjunction_homEquiv_comp]
    erw [Equiv.symm_apply_apply]
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [key]
  exact (adj.homEquiv _ M).symm.bijective.comp
    (((Etale.etaleLowerShriekRestrictionAdjunction A f).homEquiv _ _).symm.bijective.comp
      ((Etale.bijective_lowerStarUnit_comp_map_skyscraperSheaf A f y G M).comp
        (adj.homEquiv _ M).bijective))

end Concrete
end LowerShriek

section Compose

variable (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  (F : A ⥤ B) [F.PreservesZeroMorphisms] [X.smallEtaleTopology.HasSheafCompose F]
  [Y.smallEtaleTopology.HasSheafCompose F]

omit [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
  [Y.smallEtaleTopology.HasSheafCompose F] in
/-- Extension by zero off the graphs commutes with postcomposition by a functor preserving
zero morphisms. -/
lemma Etale.sheafCompose_map_lowerStarUnit_app (G : Sheaf X.smallEtaleTopology A) :
    (sheafCompose _ F).map ((Etale.lowerStarUnit A f).app G) =
      (Etale.lowerStarUnit B f).app ((sheafCompose _ F).obj G) := by
  ext U : 3
  refine Scheme.Etale.graph_hom_ext f ((sheafCompose _ F).obj G) ?_ ?_
  · erw [Scheme.Etale.graphExtend_graph]
    change F.map _ ≫ F.map _ = _
    rw [← F.map_comp]
    erw [Scheme.Etale.graphExtend_graph]
    exact F.map_id _
  · erw [Scheme.Etale.graphExtend_graphComplι]
    change F.map _ ≫ F.map _ = _
    rw [← F.map_comp]
    erw [Scheme.Etale.graphExtend_graphComplι]
    exact F.map_zero _ _

end Compose

section Bijective

variable [IsFinite f]

/-- For concrete coefficients the extension by zero off the graphs is the unit of an
adjunction `f_* ⊣ f^*`: every morphism `G ⟶ f^* F` is `η_G ≫ f^* φ` for a unique
`φ : f_* G ⟶ F`. -/
lemma Etale.bijective_lowerStarUnit_comp_map_of_concrete
    {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (G : Sheaf X.smallEtaleTopology A) (F : Sheaf Y.smallEtaleTopology A) :
    Function.Bijective (fun φ : (f)_*[A].obj G ⟶ F ↦
      (Etale.lowerStarUnit A f).app G ≫ (Etale.localizationRestriction A f ‹_›).map φ) := by
  have : (fun φ : (f)_*[A].obj G ⟶ F ↦
      (Etale.lowerStarUnit A f).app G ≫ (Etale.localizationRestriction A f ‹_›).map φ) =
      ((Etale.etaleLowerShriekRestrictionAdjunction A f).homEquiv _ _) ∘
        (fun φ ↦ Etale.etaleLowerShriekToLowerStar A f G ≫ φ) := by
    funext φ
    exact (Etale.etaleLowerShriekRestrictionAdjunction_homEquiv_comp A f G φ).symm
  rw [this]
  exact ((Etale.etaleLowerShriekRestrictionAdjunction A f).homEquiv _ _).bijective.comp
    ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun ψ ↦ ⟨inv (Etale.etaleLowerShriekToLowerStar A f G) ≫ ψ,
      IsIso.hom_inv_id_assoc _ _⟩⟩


omit [IsGrothendieckAbelian.{u + 1} A] [AlgebraicGeometry.Etale f] [IsSeparated f] [IsFinite f] in
lemma Etale.sheafCompose_preadditiveCoyoneda_map_hom_app_apply {Z : Scheme.{u}}
    {P Q : Sheaf Z.smallEtaleTopology A} (ψ : P ⟶ Q) {a : A} (U : Z.Etaleᵒᵖ)
    (x : a ⟶ P.obj.obj U) :
    (((sheafCompose _ (preadditiveCoyoneda.obj (op a))).map ψ).hom.app U).hom x =
      x ≫ ψ.hom.app U :=
  rfl

omit [IsGrothendieckAbelian.{u + 1} A] [AlgebraicGeometry.Etale f] [IsSeparated f] [IsFinite f] in
lemma Etale.sheafCompose_map_preadditiveCoyoneda_map_app_hom_app_apply {Z : Scheme.{u}}
    (P : Sheaf Z.smallEtaleTopology A) {a a' : A} (g : a ⟶ a') (U : Z.Etaleᵒᵖ)
    (x : a' ⟶ P.obj.obj U) :
    (((sheafCompose_map _ (preadditiveCoyoneda.map g.op)).app P).hom.app U).hom x = g ≫ x :=
  rfl

omit [IsGrothendieckAbelian.{u + 1} A] in
/-- **Extension by zero off the graphs is the unit of an adjunction `f_* ⊣ f^*`** for a finite
étale `f` and an arbitrary coefficient category: every morphism `G ⟶ f^* F` is `η_G ≫ f^* φ`
for a unique `φ : f_* G ⟶ F`. The case of abelian groups is
`AlgebraicGeometry.Etale.bijective_lowerStarUnit_comp_map_of_concrete`, and the general case
follows by applying it to the sheaves of abelian groups `Hom(a, G(-))` and `Hom(a, F(-))`. -/
lemma Etale.bijective_lowerStarUnit_comp_map (G : Sheaf X.smallEtaleTopology A)
    (F : Sheaf Y.smallEtaleTopology A) :
    Function.Bijective (fun φ : (f)_*[A].obj G ⟶ F ↦
      (Etale.lowerStarUnit A f).app G ≫ (Etale.localizationRestriction A f ‹_›).map φ) := by
  let h (a : A) := sheafCompose X.smallEtaleTopology (preadditiveCoyoneda.obj (op a))
  let h' (a : A) := sheafCompose Y.smallEtaleTopology (preadditiveCoyoneda.obj (op a))
  have hAb (G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Etale.bijective_lowerStarUnit_comp_map_of_concrete AddCommGrpCat.{u + 1} f G' F'
  have hcomp (a : A) {F'' : Sheaf Y.smallEtaleTopology A} {G'' : Sheaf X.smallEtaleTopology A}
      (φ : (f)_*[A].obj G'' ⟶ F'') :
      (h a).map ((Etale.lowerStarUnit A f).app G'' ≫
        (Etale.localizationRestriction A f ‹_›).map φ) =
        (Etale.lowerStarUnit AddCommGrpCat.{u + 1} f).app ((h a).obj G'') ≫
          (Etale.localizationRestriction AddCommGrpCat.{u + 1} f ‹_›).map ((h' a).map φ) := by
    rw [Functor.map_comp, Etale.sheafCompose_map_lowerStarUnit_app]
    rfl
  constructor
  · intro φ₁ φ₂ heq
    ext U : 3
    have h₁ := (hAb ((h (((f)_*[A].obj G).obj.obj U)).obj G)
      ((h' (((f)_*[A].obj G).obj.obj U)).obj F)).1
      (a₁ := (h' _).map φ₁) (a₂ := (h' _).map φ₂) (by
        dsimp only
        rw [← hcomp, ← hcomp]
        exact congrArg _ heq)
    have h₂ : 𝟙 _ ≫ φ₁.hom.app U = 𝟙 _ ≫ φ₂.hom.app U :=
      congrArg (fun ψ ↦ (ψ.hom.app U).hom (𝟙 _)) h₁
    simpa only [Category.id_comp] using h₂
  · intro ψ
    let e (a : A) := Equiv.ofBijective _ (hAb ((h a).obj G) ((h' a).obj F))
    let φa (a : A) : (f)_*[AddCommGrpCat.{u + 1}].obj ((h a).obj G) ⟶ (h' a).obj F :=
      (e a).symm ((h a).map ψ)
    have hφa (a : A) : e a (φa a) = (h a).map ψ := (e a).apply_symm_apply _
    -- the `φa` are natural in `a`
    have hnat {a a' : A} (g : a ⟶ a') :
        (f)_*[AddCommGrpCat.{u + 1}].map
            ((sheafCompose_map _ (preadditiveCoyoneda.map g.op)).app G) ≫
          φa a = φa a' ≫ (sheafCompose_map _ (preadditiveCoyoneda.map g.op)).app F := by
      apply (hAb ((h a').obj G) ((h' a).obj F)).1
      dsimp only
      have hn := (Etale.lowerStarUnit AddCommGrpCat.{u + 1} f).naturality
        ((sheafCompose_map _ (preadditiveCoyoneda.map g.op)).app G)
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc]
      change ((Etale.lowerStarUnit AddCommGrpCat.{u + 1} f).app _ ≫
        ((f)_*[AddCommGrpCat.{u + 1}] ⋙ Etale.localizationRestriction _ f _).map _) ≫ _ = _
      rw [← hn]
      change _ ≫ e a (φa a) = e a' (φa a') ≫ _
      rw [hφa, hφa]
      exact ((sheafCompose_map _ (preadditiveCoyoneda.map g.op)).naturality ψ).symm
    let m (U : Y.Etaleᵒᵖ) : ((f)_*[A].obj G).obj.obj U ⟶ F.obj.obj U :=
      ((φa (((f)_*[A].obj G).obj.obj U)).hom.app U).hom (𝟙 _)
    have hm (a : A) (U : Y.Etaleᵒᵖ) (x : a ⟶ ((f)_*[A].obj G).obj.obj U) :
        ((φa a).hom.app U).hom x = x ≫ m U := by
      have : ((φa a).hom.app U).hom (x ≫ 𝟙 _) = x ≫ m U :=
        congrArg (fun k ↦ (k.hom.app U).hom (𝟙 _)) (hnat x)
      rwa [Category.comp_id] at this
    let φ : (f)_*[A].obj G ⟶ F := ObjectProperty.homMk
      { app U := m U
        naturality U V k := by
          have hk : ((φa (((f)_*[A].obj G).obj.obj U)).hom.app V).hom
              (𝟙 _ ≫ ((f)_*[A].obj G).obj.map k) = m U ≫ F.obj.map k :=
            congrArg (fun k ↦ k (𝟙 _))
              (congrArg AddCommGrpCat.Hom.hom
                ((φa (((f)_*[A].obj G).obj.obj U)).hom.naturality k))
          rw [Category.id_comp, hm] at hk
          exact hk }
    have hφ (a : A) : (h' a).map φ = φa a := by
      ext U : 3
      ext x
      exact (hm a U x).symm
    refine ⟨φ, ?_⟩
    ext U : 3
    have h₁ : (h (G.obj.obj U)).map ((Etale.lowerStarUnit A f).app G ≫
        (Etale.localizationRestriction A f ‹_›).map φ) = (h (G.obj.obj U)).map ψ := by
      rw [hcomp, hφ]
      exact hφa _
    have h₂ : 𝟙 _ ≫ ((Etale.lowerStarUnit A f).app G ≫
        (Etale.localizationRestriction A f ‹_›).map φ).hom.app U = 𝟙 _ ≫ ψ.hom.app U :=
      congrArg (fun ψ ↦ (ψ.hom.app U).hom (𝟙 _)) h₁
    simpa only [Category.id_comp] using h₂

/-- **For a finite étale `f`, the direct image `f_*` is left adjoint to the restriction
`f^*`**, with unit the extension by zero off the graphs. -/
noncomputable def Etale.lowerStarLocalizationRestrictionAdjunction :
    (f)_*[A] ⊣ Etale.localizationRestriction A f ‹_› :=
  Adjunction.mkOfHomEquiv
    { homEquiv G F := Equiv.ofBijective _ (Etale.bijective_lowerStarUnit_comp_map A f G F)
      homEquiv_naturality_left_symm {G' G F} k ψ := by
        apply (Equiv.ofBijective _ (Etale.bijective_lowerStarUnit_comp_map A f G' F)).injective
        erw [Equiv.apply_symm_apply]
        rw [Equiv.ofBijective_apply, Functor.map_comp,
          ← Category.assoc]
        change _ = ((Etale.lowerStarUnit A f).app G' ≫
          ((f)_*[A] ⋙ Etale.localizationRestriction A f ‹_›).map k) ≫ _
        rw [← (Etale.lowerStarUnit A f).naturality, Category.assoc]
        exact congrArg (k ≫ ·) ((Equiv.ofBijective _
          (Etale.bijective_lowerStarUnit_comp_map A f G F)).apply_symm_apply ψ).symm
      homEquiv_naturality_right φ g := by
        simp only [Equiv.ofBijective_apply, Functor.map_comp, Category.assoc] }

omit [IsGrothendieckAbelian.{u + 1} A] in
lemma Etale.lowerStarLocalizationRestrictionAdjunction_unit :
    (Etale.lowerStarLocalizationRestrictionAdjunction A f).unit = Etale.lowerStarUnit A f := by
  ext G : 2
  change (Etale.lowerStarUnit A f).app G ≫ (Etale.localizationRestriction A f ‹_›).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- **For a finite étale `f`, the direct image `f_*` is left adjoint to the pullback `f^*`.** -/
noncomputable def Etale.lowerStarUpperStarAdjunctionOfIsFinite :
    (f)_*[A] ⊣ (f)^*[A] :=
  (Etale.lowerStarLocalizationRestrictionAdjunction A f).ofNatIsoRight
    (Etale.upperStarIsoLocalizationRestriction A f ‹_›).symm

end Bijective

end AlgebraicGeometry
