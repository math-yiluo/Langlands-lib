/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Support

/-!
# Globally generated étale sheaves

An étale sheaf `F` of `Λ`-modules on a scheme `X` is globally generated
(`AlgebraicGeometry.Etale.IsGloballyGenerated`, blueprint
`corollary-open-direct-image-over-field--2`) if its evaluation morphism `⊕_{s ∈ Γ(X, F)} Λ_X ⟶ F` is
an epimorphism. This file collects the formal properties of this notion.

## Main statements

- `AlgebraicGeometry.Etale.isGloballyGenerated_iff_forall_epi_sheafFiber_map`
  (`corollary-open-direct-image-over-field--2`): global generation is stalkwise surjectivity of the
  evaluation morphism.
- `AlgebraicGeometry.Etale.isGloballyGenerated_of_epi_sigmaDesc`: a sheaf which is jointly
  covered by globally generated sheaves is globally generated.
- `AlgebraicGeometry.Etale.isGloballyGenerated_of_isColimit`
(`corollary-open-direct-image-over-field--2`):
  colimits of globally generated sheaves are globally generated.
- `AlgebraicGeometry.Etale.isZero_of_isGloballyGenerated`: a globally generated sheaf without
  nonzero global sections is zero.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The global sections `Γ(X, F) = F(𝟙 X)` of étale sheaves of `Λ`-modules, the sections over
the terminal object `AlgebraicGeometry.Etale.etaleTerminal X` of the small étale site. -/
noncomputable abbrev terminalSections (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (etaleTerminal X))

/-- Every global section of `F` lies in the image of the evaluation morphism on global
sections: it is the image of the unit section `1` of the summand indexed by it. -/
lemma surjective_terminalSections_map_globalSectionsEvaluation (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Surjective ((terminalSections Λ X).map (globalSectionsEvaluation Λ X F)) := by
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleTerminal X)
  let Γ := terminalSections Λ X
  intro s
  refine ⟨(adj.unit.app (ModuleCat.of Λ Λ) ≫ Γ.map (Sigma.ι
    (fun _ : F.obj.obj (op (etaleTerminal X)) ↦ (constantSheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) s)) (1 : Λ), ?_⟩
  have h := adj.homEquiv_unit (ModuleCat.of Λ Λ) F
    ((adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ s)))
  rw [Equiv.apply_symm_apply] at h
  rw [← ConcreteCategory.comp_apply, Category.assoc, ← Γ.map_comp,
    globalSectionsEvaluation, Sigma.ι_comp_desc, ← h]
  simp only [ModuleCat.hom_ofHom]
  exact one_smul Λ s

/-- The evaluation morphisms are natural: for `ψ : G ⟶ F`, the composite of the evaluation
morphism of `G` with `ψ` factors through the evaluation morphism of `F`, by reindexing the
summands along `Γ(X, ψ)`. -/
lemma globalSectionsEvaluation_comp {X : Scheme.{u}}
    {G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : G ⟶ F) :
    globalSectionsEvaluation Λ X G ≫ ψ =
      Sigma.desc (fun s ↦ Sigma.ι (fun _ : F.obj.obj (op (etaleTerminal X)) ↦
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
          (ψ.hom.app _ s)) ≫ globalSectionsEvaluation Λ X F := by
  refine Sigma.hom_ext _ _ fun s ↦ ?_
  rw [globalSectionsEvaluation, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc,
    globalSectionsEvaluation, Sigma.ι_comp_desc, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext
  simp

/-- A sheaf `F` admitting a jointly epimorphic family of morphisms `ψ i : G i ⟶ F` from
globally generated sheaves is globally generated: the evaluation morphism of each `G i`
followed by `ψ i` factors through the evaluation morphism of `F`. -/
theorem isGloballyGenerated_of_epi_sigmaDesc {X : Scheme.{u}} {ι : Type w}
    {G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [HasCoproduct G]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : ∀ i, G i ⟶ F)
    [Epi (Sigma.desc ψ)] (hG : ∀ i, IsGloballyGenerated Λ X (G i)) :
    IsGloballyGenerated Λ X F := by
  refine ⟨fun {T} g h e ↦ ?_⟩
  refine (cancel_epi (Sigma.desc ψ)).1 (Sigma.hom_ext _ _ fun i ↦ ?_)
  have : Epi (globalSectionsEvaluation Λ X (G i)) := hG i
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc,
    ← cancel_epi (globalSectionsEvaluation Λ X (G i)),
    reassoc_of% globalSectionsEvaluation_comp Λ (ψ i),
    reassoc_of% globalSectionsEvaluation_comp Λ (ψ i), e]

/-- Blueprint `corollary-open-direct-image-over-field--2`: **colimits of globally generated
sheaves.** The point of a colimit cocone of a diagram of globally generated étale sheaves of
`Λ`-modules (for instance a filtered colimit) is globally generated: the legs of a colimit cocone
are jointly epimorphic. -/
theorem isGloballyGenerated_of_isColimit {X : Scheme.{u}} {J : Type w} [Category J]
    {D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [HasCoproduct D.obj]
    {c : Cocone D} (hc : IsColimit c) (hD : ∀ j, IsGloballyGenerated Λ X (D.obj j)) :
    IsGloballyGenerated Λ X c.pt :=
  have : Epi (Sigma.desc c.ι.app) := ⟨fun {T} g h e ↦ hc.hom_ext fun j ↦ by
    simpa using Sigma.ι _ j ≫= e⟩
  isGloballyGenerated_of_epi_sigmaDesc Λ c.ι.app hD

/-- A globally generated sheaf without nonzero global sections is zero: its evaluation
morphism vanishes. -/
theorem isZero_of_isGloballyGenerated {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsGloballyGenerated Λ X F)
    (h : Subsingleton (F.obj.obj (op (etaleTerminal X)))) : IsZero F := by
  have h0 : globalSectionsEvaluation Λ X F = 0 := by
    refine Sigma.hom_ext _ _ fun s ↦ ?_
    rw [globalSectionsEvaluation, Sigma.ι_comp_desc, comp_zero, Subsingleton.elim s 0,
      Adjunction.homEquiv_counit]
    have hz (M : ModuleCat.{u + 1} Λ) :
        ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M (0 : M)) = 0 := by
      ext
      simp
    rw [hz, Functor.map_zero, zero_comp]
  have : Epi (globalSectionsEvaluation Λ X F) := hF
  refine (IsZero.iff_id_eq_zero _).2 ((cancel_epi (globalSectionsEvaluation Λ X F)).1 ?_)
  rw [h0, zero_comp, comp_zero]

/-- Blueprint `corollary-open-direct-image-over-field--2`: **global generation is stalkwise
surjectivity.** An étale sheaf `F` of `Λ`-modules is globally generated if and only if its
evaluation morphism is surjective on every geometric stalk. The stalk functors preserve
epimorphisms, being left adjoints; conversely, the cokernel projection of the evaluation
morphism vanishes on all stalks, hence vanishes
(`AlgebraicGeometry.Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint`). -/
theorem isGloballyGenerated_iff_forall_epi_sheafFiber_map {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsGloballyGenerated Λ X F ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ X),
      Epi ((pointSmallEtale s).sheafFiber.map (globalSectionsEvaluation Λ X F)) := by
  refine ⟨fun h Ω _ _ s ↦ ?_, fun h ↦ ?_⟩
  · have : Epi (globalSectionsEvaluation Λ X F) := h
    infer_instance
  · have : AB5OfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) := inferInstance
    have hπ : cokernel.π (globalSectionsEvaluation Λ X F) = 0 :=
      sheafHom_ext_of_sheafFiber_map_algClosurePoint fun x ↦ by
        have := h _ (X.algClosurePoint x)
        rw [Functor.map_zero, ← cancel_epi ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.map
          (globalSectionsEvaluation Λ X F)), ← Functor.map_comp, cokernel.condition,
          Functor.map_zero, comp_zero]
    exact Abelian.epi_of_cokernel_π_eq_zero _ hπ


/-- Re-basing the global sections from the chosen terminal object `⊤_ X.Etale` to
`AlgebraicGeometry.Etale.etaleTerminal X`. -/
noncomputable def sectionsTerminalIsoTerminalSections (X : Scheme.{u}) :
    (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (⊤_ X.Etale)) ≅
      terminalSections Λ X :=
  NatIso.ofComponents
    (fun H ↦ H.obj.mapIso (terminalIsoIsTerminal (isTerminalEtaleTerminal X)).symm.op)
    (fun α ↦ (α.hom.naturality _).symm)

/-- Global sections are invariant under pushforward: `Γ(X, f_* H) ≅ Γ(Z, H)`. -/
noncomputable def lowerStarCompTerminalSectionsIso {Z X : Scheme.{u}} (f : Z ⟶ X) :
    (f)_*[ModuleCat.{u + 1} Λ] ⋙ terminalSections Λ X ≅ terminalSections Λ Z :=
  Functor.isoWhiskerLeft _ (sectionsTerminalIsoTerminalSections Λ X).symm ≪≫
    lowerStarCompSheafSectionsTerminalIso _ f ≪≫ sectionsTerminalIsoTerminalSections Λ Z

/-- **Pullback of the evaluation morphism to a separably closed point.** Let
`f : Spec k ⟶ X` with `k` separably closed. If every global section of `f^* G` is the pullback
of a global section of `G`, that is, if the unit `G ⟶ f_* f^* G` is surjective on global
sections, then the pullback along `f` of the evaluation morphism of `G` is an epimorphism:
over `Spec k` epimorphisms are detected on global sections. -/
lemma epi_upperStar_map_globalSectionsEvaluation {X : Scheme.{u}} {k : Type u} [Field k]
    [IsSepClosed k] (f : Spec (.of k) ⟶ X) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Function.Surjective ((terminalSections Λ X).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))) :
    Epi ((f)^*[ModuleCat.{u + 1} Λ].map (globalSectionsEvaluation Λ X G)) := by
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  let E := (f)_*[ModuleCat.{u + 1} Λ] ⋙ terminalSections Λ X
  have : (terminalSections Λ (Spec (.of k))).IsEquivalence :=
    isEquivalence_sheafSections_etalePoint Λ
  have : E.IsEquivalence :=
    Functor.isEquivalence_of_iso (lowerStarCompTerminalSectionsIso Λ f).symm
  refine E.epi_of_epi_map ?_
  rw [ModuleCat.epi_iff_surjective]
  have hc : Function.Surjective ((terminalSections Λ X).map
      (globalSectionsEvaluation Λ X G ≫ adj.unit.app G)) := by
    rw [Functor.map_comp]
    intro y
    obtain ⟨x, hx⟩ := h y
    obtain ⟨w, rfl⟩ := surjective_terminalSections_map_globalSectionsEvaluation Λ X G x
    exact ⟨w, (ConcreteCategory.comp_apply _ _ w).trans hx⟩
  have hn : globalSectionsEvaluation Λ X G ≫ adj.unit.app G = adj.unit.app _ ≫
      (f)_*[ModuleCat.{u + 1} Λ].map ((f)^*[ModuleCat.{u + 1} Λ].map
        (globalSectionsEvaluation Λ X G)) := adj.unit.naturality _
  rw [hn, Functor.map_comp] at hc
  intro y
  obtain ⟨x, hx⟩ := hc y
  exact ⟨_, (ConcreteCategory.comp_apply _ _ x).symm.trans hx⟩

/-- **Sheaves supported on finitely many closed points split.** Let `U` be an open subset of a
scheme `X` whose complement is a finite set of closed points, and `G` an étale sheaf of
`Λ`-modules on `X` whose restriction to `U` vanishes. Writing `iₓ : Spec κ(x) ⟶ X` for the
points `x ∉ U`, the units assemble to an isomorphism `G ≅ ⨁ₓ iₓ_* iₓ^* G`, as can be
checked after restricting to `U` and to every point `x` (compare
`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar`). -/
theorem isIso_biproductLift_unit_of_isZero_upperStar {X : Scheme.{u}} (U : X.Opens)
    [Finite {x : X // x ∉ U}]
    [HasFiniteBiproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj G)) :
    IsIso (biproduct.lift fun x : {x : X // x ∉ U} ↦
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (X.fromSpecResidueField x.1)).unit.app G) := by
  let ι := {x : X // x ∉ U}
  have (x : ι) : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.1 (hcl x.1 x.2)
  let adj (x : ι) :=
    upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (X.fromSpecResidueField x.1)
  let G' (x : ι) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (X.fromSpecResidueField x.1)_*[ModuleCat.{u + 1} Λ].obj
      ((X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ].obj G)
  let φ : G ⟶ ⨁ G' := biproduct.lift fun x ↦ (adj x).unit.app G
  let V : Option ι → Scheme.{u} := fun o ↦ o.elim (U : Scheme.{u})
    fun x ↦ Spec (X.residueField x.1)
  let a : ∀ o, V o ⟶ X := fun o ↦ match o with
    | none => U.ι
    | some x => X.fromSpecResidueField x.1
  have ha (y : X) : ∃ (o : Option ι) (z : V o), (a o).base z = y := by
    by_cases hy : y ∈ U
    · exact ⟨none, ⟨y, hy⟩, rfl⟩
    · exact ⟨some ⟨y, hy⟩, IsLocalRing.closedPoint _, X.fromSpecResidueField_apply _ _⟩
  have := Fintype.ofFinite ι
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha φ
    fun o ↦ ?_
  rcases o with _ | x
  · let P := (U.ι)^*[ModuleCat.{u + 1} Λ]
    have hz (x : ι) : IsZero (P.obj (G' x)) :=
      isZero_upperStar_lowerStar_of_disjoint_range _ U.ι (X.fromSpecResidueField x.1)
        (by
          rw [Scheme.range_fromSpecResidueField, Set.disjoint_singleton_right]
          simpa using x.2) _
    have : IsZero (P.obj (⨁ G')) := by
      rw [IsZero.iff_id_eq_zero, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'),
        P.map_sum]
      exact Finset.sum_eq_zero fun j _ ↦ by
        rw [P.map_comp, (hz j).eq_of_tgt (P.map (biproduct.π G' j)) 0, zero_comp]
    exact (hG.eq_of_src (P.map φ) (hG.iso this).hom) ▸ Iso.isIso_hom _
  · let P := (X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ]
    have hz (y : ι) (hxy : y ≠ x) : IsZero (P.obj (G' y)) := by
      -- `iₓ` factors through the open complement `V` of `y`, over which `G' y` vanishes
      let V : X.Opens := ⟨{y.1}ᶜ, (hcl y.1 y.2).isOpen_compl⟩
      have hV : Set.range (X.fromSpecResidueField x.1) ⊆ Set.range V.ι := by
        rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
        exact fun h ↦ hxy (Subtype.ext h).symm
      have h0 := isZero_upperStar_lowerStar_of_disjoint_range _ V.ι (X.fromSpecResidueField y.1)
        (by rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]; simp [V])
        ((X.fromSpecResidueField y.1)^*[ModuleCat.{u + 1} Λ].obj G)
      exact (Functor.map_isZero (IsOpenImmersion.lift V.ι _ hV)^*[ModuleCat.{u + 1} Λ]
        h0).of_iso ((upperStarComp (ModuleCat.{u + 1} Λ) (IsOpenImmersion.lift V.ι _ hV)
          V.ι _ (IsOpenImmersion.lift_fac _ _ _).symm).app _)
    have hπ : IsIso (P.map (biproduct.π G' x)) := by
      refine ⟨P.map (biproduct.ι G' x), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'), P.map_sum,
          Finset.sum_eq_single x (fun y _ hxy ↦ ?_) (by simp)]
        rw [P.map_comp, (hz y hxy).eq_zero_of_tgt (P.map (biproduct.π G' y)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have hunit : IsIso (P.map ((adj x).unit.app G)) := by
      have : IsIso (P.map ((adj x).unit.app G) ≫ (adj x).counit.app (P.obj G)) := by
        rw [(adj x).left_triangle_components G]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ ((adj x).counit.app (P.obj G))
    have : IsIso (P.map φ ≫ P.map (biproduct.π G' x)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this

/-- **Sheaves supported on finitely many closed points are globally generated.** Let `U` be
an open subset of a scheme `X` whose complement is a finite set of closed points with separably
closed residue fields, and `G` an étale sheaf of `Λ`-modules on `X` whose restriction to `U`
vanishes. Then `G` is globally generated.

Writing `iₓ : Spec κ(x) ⟶ X` for the points `x ∉ U`, the units assemble to an isomorphism
`G ≅ ⨁ₓ iₓ_* iₓ^* G`
(`AlgebraicGeometry.Etale.isIso_biproductLift_unit_of_isZero_upperStar`), so each unit
`G ⟶ iₓ_* iₓ^* G` is a split epimorphism, in particular surjective on global sections.
The cokernel of the evaluation morphism then vanishes after pullback to `U` (where `G`
vanishes) and to every `Spec κ(x)`
(`AlgebraicGeometry.Etale.epi_upperStar_map_globalSectionsEvaluation`), hence vanishes. -/
theorem isGloballyGenerated_of_isZero_upperStar {X : Scheme.{u}} (U : X.Opens)
    (hfin : (U : Set X)ᶜ.Finite) (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (hsep : ∀ x ∉ U, IsSepClosed (X.residueField x))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj G)) : IsGloballyGenerated Λ X G := by
  let ι := {x : X // x ∉ U}
  have : Finite ι := hfin.to_subtype
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have (x : ι) : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.1 (hcl x.1 x.2)
  let adj (x : ι) :=
    upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (X.fromSpecResidueField x.1)
  let G' (x : ι) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (X.fromSpecResidueField x.1)_*[ModuleCat.{u + 1} Λ].obj
      ((X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ].obj G)
  let φ : G ⟶ ⨁ G' := biproduct.lift fun x ↦ (adj x).unit.app G
  -- the family consisting of `U` and of the points `x ∉ U` is jointly surjective
  let V : Option ι → Scheme.{u} := fun o ↦ o.elim (U : Scheme.{u})
    fun x ↦ Spec (X.residueField x.1)
  let a : ∀ o, V o ⟶ X := fun o ↦ match o with
    | none => U.ι
    | some x => X.fromSpecResidueField x.1
  have ha (y : X) : ∃ (o : Option ι) (z : V o), (a o).base z = y := by
    by_cases hy : y ∈ U
    · exact ⟨none, ⟨y, hy⟩, rfl⟩
    · exact ⟨some ⟨y, hy⟩, IsLocalRing.closedPoint _, X.fromSpecResidueField_apply _ _⟩
  have hφ : IsIso φ := isIso_biproductLift_unit_of_isZero_upperStar Λ U hcl G hG
  -- each unit `G ⟶ iₓ_* iₓ^* G` is a split epimorphism, hence surjective on global sections
  have hsurj (x : ι) : Function.Surjective ((terminalSections Λ X).map ((adj x).unit.app G)) := by
    have hφπ : φ ≫ biproduct.π G' x = (adj x).unit.app G := biproduct.lift_π _ x
    have : IsSplitEpi ((adj x).unit.app G) :=
      ⟨⟨biproduct.ι G' x ≫ inv φ, by
        rw [Category.assoc, ← hφπ,
          IsIso.inv_hom_id_assoc, biproduct.ι_π_self]
        rfl⟩⟩
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  -- the cokernel of the evaluation morphism vanishes after pullback along every `a o`
  let e := globalSectionsEvaluation Λ X G
  have hC : IsZero (cokernel e) := by
    have : IsIso (0 : cokernel e ⟶ 0) := by
      refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha _
        fun o ↦ ?_
      have he : Epi ((a o)^*[ModuleCat.{u + 1} Λ].map e) := by
        rcases o with _ | x
        · exact hG.epi _
        · have := hsep x.1 x.2
          exact epi_upperStar_map_globalSectionsEvaluation Λ (k := X.residueField x.1)
            (X.fromSpecResidueField x.1) G (hsurj x)
      have h₁ : IsZero ((a o)^*[ModuleCat.{u + 1} Λ].obj (cokernel e)) :=
        (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ e)
      have h₂ : IsZero ((a o)^*[ModuleCat.{u + 1} Λ].obj 0) :=
        Functor.map_isZero _ (isZero_zero _)
      exact isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
    exact (isZero_zero _).of_iso (asIso (0 : cokernel e ⟶ 0))
  exact Abelian.epi_of_cokernel_π_eq_zero _ (hC.eq_of_tgt _ _)

end Etale

end AlgebraicGeometry
