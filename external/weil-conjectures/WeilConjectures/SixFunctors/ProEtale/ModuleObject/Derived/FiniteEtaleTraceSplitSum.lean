/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceGlue

/-!
# The trace on the sections of a split cover

Let `g : Y ⟶ X` be weakly étale and `B = map_g ∘ pullback_g` the endofunctor
`V ↦ V ×_X Y` of the small pro-étale site of `X`, with projection `ε_V : V ×_X Y ⟶ V`. For a
sheaf `G` on `X_proét`, the sections of `g_* g^* G` over `V` are `G(V ×_X Y)`.

A *splitting* of `V ×_X Y` (`AlgebraicGeometry.ProEtale.TraceSplitting`) is a finite family of
sections of `ε_V` exhibiting `V ×_X Y` as the coproduct of copies of `V`. The *trace* along a
splitting is the sum of the restrictions along its sections
(`AlgebraicGeometry.ProEtale.TraceSplitting.trace`), and:

* `AlgebraicGeometry.ProEtale.TraceSplitting.restriction_comp_trace`: composed with the
  restriction along `ε_V` it is multiplication by the number of sheets;
* `AlgebraicGeometry.ProEtale.TraceSplitting.trace_eq`: it does not depend on the splitting.
  Indeed, Zariski locally on `V` two splittings differ by a bijection of their index sets
  (`AlgebraicGeometry.finiteSectionCoproduct_local_permutation`), and `G` is separated;
* `AlgebraicGeometry.ProEtale.TraceSplitting.trace_naturality`: it is compatible with
  restriction along morphisms `V' ⟶ V`, for compatible splittings.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]

/-- The base change endofunctor `V ↦ V ×_X Y` of the small pro-étale site of `X`. -/
noncomputable abbrev traceBaseChange : X.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)

/-- The projection `V ×_X Y ⟶ V`, the counit of `map_g ⊣ pullback_g`. -/
noncomputable abbrev traceProj (V : X.ProEt) : (traceBaseChange g).obj V ⟶ V :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).counit.app V

lemma traceProj_left (V : X.ProEt) : (traceProj g V).left = pullback.fst V.hom g := rfl

lemma traceBaseChange_map_comp_traceProj {V V' : X.ProEt} (f : V' ⟶ V) :
    (traceBaseChange g).map f ≫ traceProj g V = traceProj g V' ≫ f :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).counit.naturality
    f

/-- A **splitting** of `V ×_X Y` over `V`: a finite family of sections of the projection
`V ×_X Y ⟶ V` exhibiting `V ×_X Y` as a coproduct of copies of `V`. -/
structure TraceSplitting (V : X.ProEt) where
  /-- The index type of the sheets. -/
  J : Type u
  [fintype : Fintype J]
  /-- The sections. -/
  s : J → (V ⟶ (traceBaseChange g).obj V)
  s_proj : ∀ j, s j ≫ traceProj g V = 𝟙 V
  isColimit : IsColimit (Cofan.mk (pullback V.hom g) fun j ↦ (s j).left)

attribute [instance] TraceSplitting.fintype

namespace TraceSplitting

variable {g} {A : Type u'} [Category.{u + 1} A] [Preadditive A] (G : Sheaf (ProEt.topology X) A)

/-- The **trace along a splitting**: the sum of the restrictions along its sections,
`G(V ×_X Y) ⟶ G(V)`. -/
noncomputable def trace {V : X.ProEt} (D : TraceSplitting g V) :
    G.obj.obj (op ((traceBaseChange g).obj V)) ⟶ G.obj.obj (op V) :=
  ∑ j, G.obj.map (D.s j).op

/-- The restriction along the projection followed by the trace along a splitting with `n`
sheets is multiplication by `n`. -/
lemma restriction_comp_trace {V : X.ProEt} (D : TraceSplitting g V) :
    G.obj.map (traceProj g V).op ≫ D.trace G = Fintype.card D.J • 𝟙 _ := by
  simp only [trace, Preadditive.comp_sum, ← G.obj.map_comp, ← op_comp, D.s_proj, op_id,
    G.obj.map_id, Finset.sum_const, Finset.card_univ]

/-- The trace along splittings is compatible with restriction along a morphism `f : V' ⟶ V`,
for splittings whose sections correspond under `f`. -/
lemma trace_naturality {V V' : X.ProEt} (D : TraceSplitting g V) (D' : TraceSplitting g V')
    (f : V' ⟶ V) (e : D'.J ≃ D.J)
    (he : ∀ j, D'.s j ≫ (traceBaseChange g).map f = f ≫ D.s (e j)) :
    G.obj.map ((traceBaseChange g).map f).op ≫ D'.trace G = D.trace G ≫ G.obj.map f.op := by
  simp only [trace, Preadditive.comp_sum, Preadditive.sum_comp, ← G.obj.map_comp, ← op_comp,
    he]
  exact Fintype.sum_equiv e _ _ fun _ ↦ rfl

/-- **The trace does not depend on the splitting.** Zariski locally on `V`, two splittings
differ by a bijection of their index sets. -/
lemma trace_eq {V : X.ProEt} (D D' : TraceSplitting g V) : D.trace G = D'.trace G := by
  classical
  have hloc (z : V.left) : ∃ (U : V.left.Opens), z ∈ U ∧ ∃ e : D.J ≃ D'.J,
      ∀ j, U.ι ≫ (D.s j).left = U.ι ≫ (D'.s (e j)).left :=
    finiteSectionCoproduct_local_permutation V.left (pullback V.hom g) (pullback.fst V.hom g)
      D.J D'.J (fun j ↦ (D.s j).left) (fun j ↦ (D'.s j).left) D.isColimit D'.isColimit
      (fun j ↦ by exact congrArg (fun k ↦ k.left) (D.s_proj j))
      (fun j ↦ by exact congrArg (fun k ↦ k.left) (D'.s_proj j)) z
  choose U hU e he using hloc
  let S : Sieve V :=
    { arrows := fun T k ↦ ∃ e : D.J ≃ D'.J, ∀ j, k ≫ D.s j = k ≫ D'.s (e j)
      downward_closed := fun {T T'} k ⟨e, he⟩ k' ↦ ⟨e, fun j ↦ by
        rw [Category.assoc, he, Category.assoc]⟩ }
  have hS : S ∈ ProEt.topology X V :=
    ProEt.mem_topology_of_openImmersion S (fun z ↦ (U z).ι)
      (fun z ↦ ⟨z, ⟨⟨z, hU z⟩, rfl⟩⟩)
      (fun z ↦ ⟨e z, fun j ↦ MorphismProperty.Over.Hom.ext (he z j)⟩)
  refine G.property.hom_ext ⟨S, hS⟩ _ _ fun I ↦ ?_
  obtain ⟨e, he⟩ := I.hf
  simp only [trace, Preadditive.sum_comp, ← G.obj.map_comp, ← op_comp]
  refine (Fintype.sum_equiv e _ _ fun j ↦ ?_)
  rw [he]


section Pullback

variable {V V' : X.ProEt} (D : TraceSplitting g V) (f : V' ⟶ V)

/-- The section of `V' ×_X Y ⟶ V'` obtained by base change of a section `s` of
`V ×_X Y ⟶ V` along `f : V' ⟶ V`. -/
noncomputable def pullbackSection (s : V ⟶ (traceBaseChange g).obj V)
    (hs : s ≫ traceProj g V = 𝟙 V) : V' ⟶ (traceBaseChange g).obj V' :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 V'.left) (f.left ≫ s.left ≫ pullback.snd V.hom g) (by
      have h₁ : s.left ≫ pullback.fst V.hom g = 𝟙 V.left := congrArg (fun k ↦ k.left) hs
      rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% h₁,
        Category.id_comp, MorphismProperty.Over.w f]))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd V'.hom g ≫ g = V'.hom
      rw [← pullback.condition, pullback.lift_fst_assoc]
      exact Category.id_comp _)

lemma pullbackSection_left (s : V ⟶ (traceBaseChange g).obj V)
    (hs : s ≫ traceProj g V = 𝟙 V) :
    (pullbackSection f s hs).left = pullback.lift (𝟙 V'.left)
      (f.left ≫ s.left ≫ pullback.snd V.hom g) (by
        have h₁ : s.left ≫ pullback.fst V.hom g = 𝟙 V.left := congrArg (fun k ↦ k.left) hs
        rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% h₁,
          Category.id_comp, MorphismProperty.Over.w f]) := rfl

lemma pullbackSection_proj (s : V ⟶ (traceBaseChange g).obj V)
    (hs : s ≫ traceProj g V = 𝟙 V) : pullbackSection f s hs ≫ traceProj g V' = 𝟙 V' :=
  MorphismProperty.Over.Hom.ext (by
    change (pullbackSection f s hs).left ≫ pullback.fst V'.hom g = 𝟙 V'.left
    rw [pullbackSection_left, pullback.lift_fst])

lemma pullbackSection_comp (s : V ⟶ (traceBaseChange g).obj V)
    (hs : s ≫ traceProj g V = 𝟙 V) :
    pullbackSection f s hs ≫ (traceBaseChange g).map f = f ≫ s := by
  have h₁ : s.left ≫ pullback.fst V.hom g = 𝟙 V.left := congrArg (fun k ↦ k.left) hs
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
  · change (pullbackSection f s hs).left ≫ ((traceBaseChange g).map f).left ≫
      pullback.fst V.hom g = f.left ≫ s.left ≫ pullback.fst V.hom g
    rw [pullbackSection_left]
    simp only [Functor.comp_map, MorphismProperty.Over.map_map_left,
      MorphismProperty.Over.pullback_map_left, limit.lift_π, PullbackCone.mk_π_app,
      limit.lift_π_assoc, cospan_left, h₁]
    exact Category.id_comp _
  · change (pullbackSection f s hs).left ≫ ((traceBaseChange g).map f).left ≫
      pullback.snd V.hom g = f.left ≫ s.left ≫ pullback.snd V.hom g
    rw [pullbackSection_left]
    simp [traceBaseChange]

/-- The square relating the base change `V' ×_X Y ⟶ V ×_X Y` to the projections is cartesian. -/
lemma isPullback_traceBaseChange_map :
    IsPullback ((traceBaseChange g).map f).left (pullback.fst V'.hom g)
      (pullback.fst V.hom g) f.left := by
  refine IsPullback.of_right ?_ (by simp [traceBaseChange])
    (IsPullback.of_hasPullback V.hom g).flip
  have h : ((traceBaseChange g).map f).left ≫ pullback.snd V.hom g = pullback.snd V'.hom g := by
    simp [traceBaseChange]
  have h' : f.left ≫ V.hom = V'.hom := MorphismProperty.Over.w f
  rw [h, h']
  exact (IsPullback.of_hasPullback V'.hom g).flip

/-- The **pullback of a splitting** along `f : V' ⟶ V`: the base changes of its sections, which
again exhibit `V' ×_X Y` as a coproduct, coproducts of schemes being universal. -/
noncomputable def restrict : TraceSplitting g V' where
  J := D.J
  s j := pullbackSection f (D.s j) (D.s_proj j)
  s_proj j := pullbackSection_proj f (D.s j) (D.s_proj j)
  isColimit := by
    refine (FinitaryPreExtensive.isUniversal_finiteCoproducts D.isColimit
      (Cofan.mk (pullback V'.hom g) fun j ↦ (pullbackSection f (D.s j) (D.s_proj j)).left)
      (Discrete.natTrans fun _ ↦ f.left) ((traceBaseChange g).map f).left ?_
      (NatTrans.Equifibered.of_discrete _) fun j ↦ ?_).some
    · ext ⟨j⟩
      exact (congrArg (fun k ↦ k.left) (pullbackSection_comp f (D.s j) (D.s_proj j))).symm
    · have hsq := isPullback_traceBaseChange_map (g := g) f
      refine IsPullback.of_right (h₁₂ := pullback.fst V'.hom g)
        (h₂₂ := pullback.fst V.hom g)
        ?_ ?_ hsq.flip
      · have h₁ : (pullbackSection f (D.s j.as) (D.s_proj j.as)).left ≫
            pullback.fst V'.hom g = 𝟙 _ :=
          congrArg (fun k ↦ k.left) (pullbackSection_proj f (D.s j.as) (D.s_proj j.as))
        have h₂ : (D.s j.as).left ≫ pullback.fst V.hom g = 𝟙 _ :=
          congrArg (fun k ↦ k.left) (D.s_proj j.as)
        dsimp
        rw [h₁, h₂]
        exact IsPullback.id_horiz f.left
      · exact (congrArg (fun k ↦ k.left) (pullbackSection_comp f (D.s j.as) (D.s_proj j.as)))

lemma restrict_s_comp (j : D.J) :
    (D.restrict f).s j ≫ (traceBaseChange g).map f = f ≫ D.s j :=
  pullbackSection_comp f (D.s j) (D.s_proj j)

/-- The trace is compatible with restriction along `f : V' ⟶ V`. -/
lemma trace_restrict_naturality {A : Type u'} [Category.{u + 1} A] [Preadditive A]
    (G : Sheaf (ProEt.topology X) A) (D' : TraceSplitting g V') :
    G.obj.map ((traceBaseChange g).map f).op ≫ D'.trace G = D.trace G ≫ G.obj.map f.op := by
  rw [trace_eq G D' (D.restrict f)]
  exact trace_naturality G D (D.restrict f) f (Equiv.refl _) (restrict_s_comp D f)

end Pullback

end TraceSplitting

end AlgebraicGeometry.ProEtale
