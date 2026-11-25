/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Constructibility by Noetherian induction over integral closed subschemes

Let `X` be a Noetherian scheme and `F` an étale sheaf of `Λ`-modules on `X`. If for every
integral closed subscheme `i : Z ⟶ X` the restriction of `F` to some nonempty open of `Z` is
constructible, then `F` is constructible
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_forall_isIntegral`). This is the Noetherian
induction closing the proof of `proposition-proper-direct-image-finite-coefficients`: the generic
statement over integral bases spreads to the whole base.

The induction runs over the closed subsets of `X`, each with a reduced closed subscheme
structure. A nonempty reduced Noetherian scheme `Z` has a nonempty open `V` contained in one of
its irreducible components `C`; the reduced induced structure on `C` is integral, and the open
`V`, being reduced, maps into it (`AlgebraicGeometry.Scheme.exists_opens_factor_of_isReduced`).
Finally `F` is constructible as soon as its restriction to the reduction of `X` is
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_upperStar_of_surjective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- A nonempty Noetherian space has a nonempty open subset contained in an irreducible closed
subset: the complement of the union of all but one irreducible component. -/
lemma _root_.TopologicalSpace.NoetherianSpace.exists_isOpen_subset_isIrreducible {Z : Type*}
    [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Z] [Nonempty Z] :
    ∃ (C : Set Z) (V : Set Z), IsIrreducible C ∧ IsClosed C ∧ IsOpen V ∧ V.Nonempty ∧ V ⊆ C := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  let C := irreducibleComponent z
  have hC : C ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Z)
  have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton hfin C hC
  have hD : IsClosed (⋃₀ (irreducibleComponents Z \ {C})) :=
    Set.sUnion_eq_biUnion ▸ (hfin.subset Set.sdiff_subset).isClosed_biUnion fun C' hC' ↦
      isClosed_of_mem_irreducibleComponents C' hC'.1
  refine ⟨C, _, hC.1, isClosed_of_mem_irreducibleComponents C hC, hD.isOpen_compl, ?_,
    fun x hx ↦ hcl ▸ subset_closure hx⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, closure_empty] at hcl
  exact hC.1.1.ne_empty hcl.symm

/-- **Opens of a reduced scheme inside an integral closed subscheme.** A nonempty reduced
Noetherian scheme `Z` has an integral closed subscheme `c : C ⟶ Z` such that every nonempty open
`W` of `C` contains, up to a morphism `e` over `Z`, a nonempty open `V` of `Z`: take `C` an
irreducible component with its reduced induced structure and `V` an open of `Z` inside `c(W)`
missing the other components; `V` is reduced, so it maps into `C`. -/
lemma exists_isIntegral_opens_factor {Z : Scheme.{u}} [IsReduced Z] [IsNoetherian Z]
    [Nonempty Z] :
    ∃ (C : Scheme.{u}) (c : C ⟶ Z) (_ : IsClosedImmersion c) (_ : IsIntegral C),
      ∀ W : C.Opens, (W : Set C).Nonempty →
        ∃ (V : Z.Opens) (e : V.toScheme ⟶ W.toScheme), (V : Set Z).Nonempty ∧
          e ≫ W.ι ≫ c = V.ι := by
  obtain ⟨C₀, V₀, hirr, hcl, hV₀, hne, hsub⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_subset_isIrreducible (Z := Z)
  let c := (IdealSheafData.vanishingIdeal ⟨C₀, hcl⟩).subschemeι
  have hc : Set.range c = C₀ := by
    simp [c, IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
  have : IrreducibleSpace (IdealSheafData.vanishingIdeal ⟨C₀, hcl⟩).subscheme := by
    have : IrreducibleSpace (Set.range c) := Subtype.irreducibleSpace (by rw [hc]; exact hirr)
    exact c.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (IdealSheafData.vanishingIdeal ⟨C₀, hcl⟩).subscheme
  refine ⟨_, c, inferInstance, this, fun W hW ↦ ?_⟩
  obtain ⟨O, hO, hWO⟩ := c.isEmbedding.isInducing.isOpen_iff.1 W.isOpen
  -- `V = V₀ ∩ O` is a nonempty open of `Z` inside `c(W)`
  have hcW : c '' W = C₀ ∩ O := by
    rw [← hWO, Set.image_preimage_eq_inter_range, hc, Set.inter_comm]
  have hVne : (V₀ ∩ O).Nonempty := by
    obtain ⟨w, hw⟩ := hW
    obtain ⟨x, hx, hxO⟩ := hirr.2 V₀ O hV₀ hO (hne.mono fun x hx ↦ ⟨hsub hx, hx⟩)
      ⟨c w, hc.le (Set.mem_range_self w), by rw [← Set.mem_preimage, hWO]; exact hw⟩
    exact ⟨x, hxO.1, hxO.2⟩
  let V : Z.Opens := ⟨V₀ ∩ O, hV₀.inter hO⟩
  have hVC : Set.range V.ι ⊆ Set.range c := by
    rw [Opens.range_ι, hc]
    exact fun x hx ↦ hsub hx.1
  -- `V` is reduced, so the surjective closed immersion `c⁻¹ V ⟶ V` is an isomorphism
  have : Surjective (pullback.snd c V.ι) := ⟨fun v ↦ by
    obtain ⟨y, hy⟩ := hVC ⟨v, rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y v hy
    exact ⟨z, hz⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd c V.ι)
  let e₀ : V.toScheme ⟶ _ := inv (pullback.snd c V.ι) ≫ pullback.fst c V.ι
  have he₀ : e₀ ≫ c = V.ι := by
    simp [e₀, pullback.condition]
  have hrange : Set.range e₀ ⊆ Set.range W.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Opens.range_ι, ← hWO, Set.mem_preimage]
    have : c (e₀ v) ∈ V₀ ∩ O := by
      rw [← Scheme.Hom.comp_apply, he₀]
      simp
    exact this.2
  refine ⟨V, IsOpenImmersion.lift W.ι e₀ hrange, hVne, ?_⟩
  rw [IsOpenImmersion.lift_fac_assoc, he₀]

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A sheaf is constructible as soon as its pullback along a surjective closed immersion is: the
complementary open is empty. -/
lemma isConstructibleSheaf_of_upperStar_of_surjective {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Surjective i] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsConstructibleSheaf ((i)^*[ModuleCat.{u + 1} Λ].obj F)) : IsConstructibleSheaf F := by
  have hij : Set.range i = (Set.range (⊥ : X.Opens).ι)ᶜ := by
    rw [Opens.range_ι, TopologicalSpace.Opens.coe_bot, Set.compl_empty, Set.range_eq_univ]
    exact i.surjective
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : X.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  refine (isConstructibleSheaf_iff_upperStar (⊥ : X.Opens).ι i hij F).2 ⟨?_, h⟩
  exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)

/-- **Constructibility by Noetherian induction over integral closed subschemes.** Let `X` be
Noetherian and `F` an étale sheaf of `Λ`-modules on `X`. If for every closed immersion
`i : Z ⟶ X` from an integral scheme some nonempty open `U` of `Z` has `(U ⟶ X)^* F`
constructible, then `F` is constructible. -/
theorem isConstructibleSheaf_of_forall_isIntegral {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      ∃ U : Z.Opens, (U : Set Z).Nonempty ∧
        IsConstructibleSheaf ((U.ι ≫ i)^*[ModuleCat.{u + 1} Λ].obj F)) :
    IsConstructibleSheaf F := by
  classical
  have key : ∀ (C : TopologicalSpace.Closeds X) (Z : Scheme.{u}) [IsReduced Z]
      (i : Z ⟶ X) [IsClosedImmersion i], Set.range i ⊆ C →
      IsConstructibleSheaf ((i)^*[ModuleCat.{u + 1} Λ].obj F) := by
    intro C
    induction C using WellFoundedLT.induction with
    | ind C ih =>
      intro Z _ i _ hiC
      have : IsNoetherian Z := by
        have := LocallyOfFiniteType.isLocallyNoetherian i
        have := QuasiCompact.compactSpace_of_compactSpace i
        exact {}
      cases isEmpty_or_nonempty Z
      · exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
      -- a nonempty open `U` of `Z` on which `F` is constructible
      obtain ⟨C', c, _, _, hc⟩ := exists_isIntegral_opens_factor (Z := Z)
      obtain ⟨W, hW, hWF⟩ := h C' (c ≫ i)
      obtain ⟨U, e, ⟨z, hz⟩, he⟩ := hc W hW
      have hopen : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) := by
        have : IsConstructibleSheaf (((W.ι ≫ c ≫ i)^*[ModuleCat.{u + 1} Λ] ⋙
            (e)^*[ModuleCat.{u + 1} Λ]).obj F) :=
          IsConstructibleSheaf.upperStar e ((W.ι ≫ c ≫ i)^*[ModuleCat.{u + 1} Λ].obj F)
        have he' : e ≫ W.ι ≫ c ≫ i = U.ι ≫ i := by
          rw [← reassoc_of% he]
        exact IsConstructibleSheaf.of_iso (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) e
          (W.ι ≫ c ≫ i)).app F).symm ≪≫ eqToIso (by rw [he']) ≪≫
            (Etale.upperStarComp (ModuleCat.{u + 1} Λ) U.ι i).app F)
      -- the complement of `U`, with its reduced induced structure, is handled by induction
      let D : TopologicalSpace.Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
      let i' := (IdealSheafData.vanishingIdeal D).subschemeι
      have hrange : Set.range i' = (U : Set Z)ᶜ := by
        simp [i', D, IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal]
      let C'' : TopologicalSpace.Closeds X :=
        ⟨i '' (U : Set Z)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : C'' < C := by
        refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiC ⟨t, ht⟩) fun heq ↦ ?_
        have : i z ∈ (C'' : Set X) := heq ▸ hiC ⟨z, rfl⟩
        obtain ⟨t, ht, hti⟩ := this
        exact ht (i.isClosedEmbedding.injective hti ▸ hz)
      have hC'' := ih C'' hlt _ (i' ≫ i) (by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
        exact subset_rfl)
      have hclosed : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i').obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :=
        IsConstructibleSheaf.of_iso
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i' i).app F)
      exact (isConstructibleSheaf_iff_upperStar U.ι i'
        (by rw [Scheme.Opens.range_ι]; exact hrange) _).mpr ⟨hopen, hclosed⟩
  have := key ⊤ X.nilradical.subscheme X.nilradical.subschemeι (by simp)
  have : Surjective X.nilradical.subschemeι := ⟨by
    rw [← Set.range_eq_univ, IdealSheafData.range_subschemeι, ← IdealSheafData.vanishingIdeal_top,
      IdealSheafData.coe_support_vanishingIdeal]
    rfl⟩
  exact isConstructibleSheaf_of_upperStar_of_surjective _ F ‹_›

end AlgebraicGeometry.Scheme
