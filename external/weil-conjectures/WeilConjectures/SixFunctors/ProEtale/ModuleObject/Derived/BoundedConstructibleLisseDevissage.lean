/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization

/-!
# Dévissage of bounded constructible complexes to lisse sheaves on locally closed subschemes

Let `Λ` be a commutative condensed ring and `T` a scheme with noetherian underlying space. A
triangulated functor `Φ : D(Mod_{Λ_T}) ⥤ D(Mod_{Λ_Y})`, where the bounded constructible
complexes on `Y` form a triangulated subcategory, carries `Dᵇc(T)` into `Dᵇc(Y)` as soon as it
does so for the extensions by zero `Rc_* j_! Rc'_* L` of the pro-étale locally finitely presented
(lisse) sheaves `L` along the locally closed immersions `E ⟶ W ⊆ D ⟶ T` (with `c` and `c'` closed
immersions and `W` open in `D`)
(`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse`). Given an open `U` of `T`, it
suffices to treat surjective `c'` and opens `W` lying inside `c⁻¹ U` or inside its complement
(`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`).

The proof is a noetherian induction on the closed subset of `T` containing the image of a closed
immersion `c : D ⟶ T`, for complexes of the form `Rc_* M` with `M` bounded constructible on `D`.
By dévissage along the truncation triangles, `M` is a constructible sheaf `G` placed in degree
`0`. Some stratum of a stratification of `D` adapted to `G` contains a nonempty open `V` of `D`
(`ProEtale.CondensedRing.exists_nonempty_opens_subset_stratum`), and the open–closed triangle
`j_! Lj^* G ⟶ G ⟶ Ri_* Li^* G ⟶` for `V` and its closed complement splits `G` into the extension
by zero of a sheaf which is lisse on (a surjective closed immersion onto) `V`, and a complex
supported on the smaller closed subset `c(D ∖ V)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Support of a closed pushforward**: for a closed immersion `c : D ⟶ X` and an open `U` of
`X`, `L(U ↪ X)^* Rc_* K` vanishes as soon as the restriction of `K` to `c⁻¹ U` does: `K` is then
`Ri_* Li^* K` for the closed complement `i` of `c⁻¹ U`, and `Rc_* Ri_* = R(i ≫ c)_*` is supported
on `c(D ∖ c⁻¹ U)`, which misses `U`. -/
lemma isZero_leftDerivedUpperStar_ι_obj_rightDerivedLowerStar_obj {X D : Scheme.{u}}
    (U : X.Opens) (c : D ⟶ X) [IsClosedImmersion c] [QuasiCompact (c ⁻¹ᵁ U).ι]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D))} (hK : IsZero ((L(((c ⁻¹ᵁ U).ι)^*⟦Λ⟧)).obj K)) :
    IsZero ((L((U.ι)^*⟦Λ⟧)).obj ((R((c)_*⟦Λ⟧)).obj K)) := by
  have hc : IsCompl (Set.range (c ⁻¹ᵁ U).closedComplement.base)
      (Set.range (c ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ (c ⁻¹ᵁ U).ι
    (c ⁻¹ᵁ U).closedComplement hc hK
  refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ U.ι
    ((c ⁻¹ᵁ U).closedComplement ≫ c) ?_ _).of_iso
    ((L((U.ι)^*⟦Λ⟧)).mapIso ((R((c)_*⟦Λ⟧)).mapIso
      (asIso ((derivedUpperStarLowerStarAdjunction Λ (c ⁻¹ᵁ U).closedComplement).unit.app K)) ≪≫
        (rightDerivedLowerStarComp Λ _ c).app _))
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.Opens.range_closedComplement, Set.disjoint_left]
  rintro _ hx ⟨y, hy, rfl⟩
  exact hy hx

section Devissage

variable {T Y : Scheme.{u}} [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated]
  (Φ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
  [Φ.CommShift ℤ] [Φ.IsTriangulated]

omit [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated] [Φ.CommShift ℤ]
  [Φ.IsTriangulated] in
/-- The hypothesis of the dévissage to lisse sheaves: `Φ` maps the extensions by zero
`Rc_* j_! Rc'_* L` of the lisse sheaves `L` along the locally closed immersions
`E ⟶ W ⊆ D ⟶ T` (`c`, `c'` closed immersions, `W` open in `D`) to bounded constructible
complexes. -/
def LisseHypothesis : Prop :=
  ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
    IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj
      (D((W.ι)_!open⟦Λ⟧).obj ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L)))))

omit [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated] [Φ.CommShift ℤ]
  [Φ.IsTriangulated] in
/-- The hypothesis of the dévissage to lisse sheaves *adapted to an open* `U` of `T`: `Φ` maps
the extensions by zero `Rc_* j_! Rc'_* L` of the lisse sheaves `L` along the locally closed
immersions `E ⟶ W ⊆ D ⟶ T` to bounded constructible complexes, whenever `c'` is surjective (so
that `E` is `W` up to nilpotents) and the open `W` of `D` lies either inside `c⁻¹ U` or inside
its complement. -/
def LisseHypothesisAlong (U : T.Opens) : Prop :=
  ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c] (W : D.Opens),
    ((W : Set D) ⊆ c ⁻¹ᵁ U ∨ Disjoint (W : Set D) (c ⁻¹ᵁ U)) →
    ∀ (E : Scheme.{u}) (c' : E ⟶ W) [IsClosedImmersion c'], Surjective c' →
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
    IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj
      (D((W.ι)_!open⟦Λ⟧).obj ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L)))))

variable {Λ Φ}

omit [IsCommMonObj Λ] [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated]
  [Φ.CommShift ℤ] [Φ.IsTriangulated] in
/-- The hypothesis of the dévissage to lisse sheaves implies its variant adapted to any open. -/
lemma LisseHypothesis.along (hΦ : LisseHypothesis Λ Φ) (U : T.Opens) :
    LisseHypothesisAlong Λ Φ U :=
  fun D c _ W _ E c' _ _ L hL ↦ hΦ D c W E c' L hL

omit [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated] [Φ.CommShift ℤ]
  [Φ.IsTriangulated] in
/-- The open piece of the dévissage step: the restriction of a constructible sheaf `G` on `D` to
a nonempty open `V` contained in a stratum is (the pushforward along a surjective closed immersion
of) a lisse sheaf, so `Φ (Rc_* j_! Lj^* G)` is bounded constructible. -/
lemma boundedConstructible_lisse_open {U : T.Opens} (hΦ : LisseHypothesisAlong Λ Φ U)
    {D : Scheme.{u}} (c : D ⟶ T) [IsClosedImmersion c] (S : Scheme.Stratification D)
    (a : Fin S.n) (V : D.Opens) (hVS : (V : Set D) ⊆ S.stratum a)
    (hVU : (V : Set D) ⊆ c ⁻¹ᵁ U ∨ Disjoint (V : Set D) (c ⁻¹ᵁ U))
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
      ((S.immersion a)^*⟦Λ⟧.obj G)) :
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj
      (D((V.ι)_!open⟦Λ⟧).obj ((L((V.ι)^*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))))) := by
  obtain ⟨E, c', b, hcb, _, _⟩ : ∃ (E : Scheme.{u}) (c' : E ⟶ V) (b : E ⟶ S.domain a),
      c' ≫ V.ι = b ≫ S.immersion a ∧ IsClosedImmersion c' ∧ Surjective c' := by
    have : Surjective (pullback.fst V.ι (S.immersion a)) :=
      surjective_pullback_fst_of_range_subset _ _ (by
        rw [Scheme.Opens.range_ι, S.range_immersion]
        exact hVS)
    exact ⟨_, pullback.fst V.ι (S.immersion a), pullback.snd V.ι (S.immersion a),
      pullback.condition, IsClosedImmersion.of_isImmersion_of_surjective _, this⟩
  have : IsEmpty (⊥ : V.toScheme.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have hc : IsCompl (Set.range c'.base) (Set.range (⊥ : V.toScheme.Opens).ι.base) := by
    rw [Set.range_eq_univ.2 c'.surjective, Scheme.Opens.range_ι]
    exact isCompl_top_bot
  have : QuasiCompact (⊥ : V.toScheme.Opens).ι :=
    ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ
    (⊥ : V.toScheme.Opens).ι c' hc
    (K := (L((V.ι)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G))
    (isZero_derivedCategory_of_isEmpty' Λ _)
  have hL : IsLocallyFinitelyPresented (condensedRingObj Λ E) ((c' ≫ V.ι)^*⟦Λ⟧.obj G) :=
    isLocallyFinitelyPresented_upperStar_comp_of_comm (Λ := Λ) hcb hG
  have e : (L((V.ι)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G) ≅
      (R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj ((c' ≫ V.ι)^*⟦Λ⟧.obj G)) :=
    asIso ((derivedUpperStarLowerStarAdjunction Λ c').unit.app _) ≪≫
      (R((c')_*⟦Λ⟧)).mapIso (((leftDerivedUpperStarComp Λ c' V.ι).app _).symm ≪≫
        leftDerivedUpperStarSingleIso Λ (c' ≫ V.ι) G)
  exact (boundedConstructible _).prop_of_iso
    (Φ.mapIso ((R((c)_*⟦Λ⟧)).mapIso (D((V.ι)_!open⟦Λ⟧).mapIso e))).symm
    (hΦ D c V hVU E c' ‹_› _ hL)

/-- The induction step of the dévissage to lisse sheaves, for a constructible sheaf `G` on a
closed subscheme `c : D ⟶ T` with image in the closed subset `Z`: split `G` along a nonempty open
`V` of `D` contained in a stratum; the closed piece is supported on `c(D ∖ V) < Z`. -/
lemma boundedConstructible_lisse_step {U : T.Opens} (hΦ : LisseHypothesisAlong Λ Φ U)
    (Z : TopologicalSpace.Closeds T)
    (ih : ∀ Z' < Z, ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c],
      Set.range c.base ⊆ Z' →
      ∀ M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)), boundedConstructible _ M →
        boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj M)))
    {D : Scheme.{u}} (c : D ⟶ T) [IsClosedImmersion c] [TopologicalSpace.NoetherianSpace D]
    (hcZ : Set.range c.base ⊆ Z)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsConstructibleModuleObject (condensedRingObj Λ D) G) :
    boundedConstructible (condensedRingObj Λ Y)
      (Φ.obj ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · exact boundedConstructible_of_isZero Λ (Φ.map_isZero ((R((c)_*⟦Λ⟧)).map_isZero
      (isZero_derivedCategory_of_isEmpty' Λ _)))
  have hGc := hG
  obtain ⟨S, hS⟩ := hG
  obtain ⟨a, V₀, hV₀, hV₀S⟩ := exists_nonempty_opens_subset_stratum S
  obtain ⟨V, ⟨v, hv⟩, hVV₀, hVU⟩ : ∃ V : D.Opens, (V : Set D).Nonempty ∧ V ≤ V₀ ∧
      ((V : Set D) ⊆ c ⁻¹ᵁ U ∨ Disjoint (V : Set D) (c ⁻¹ᵁ U)) := by
    by_cases h : ((V₀ ⊓ c ⁻¹ᵁ U : D.Opens) : Set D).Nonempty
    · exact ⟨V₀ ⊓ c ⁻¹ᵁ U, h, inf_le_left, Or.inl fun _ hx ↦ hx.2⟩
    · refine ⟨V₀, hV₀, le_rfl, Or.inr (Set.disjoint_iff_inter_eq_empty.2 ?_)⟩
      simpa [Set.not_nonempty_iff_eq_empty] using h
  have hVS : (V : Set D) ⊆ S.stratum a := (SetLike.coe_subset_coe.2 hVV₀).trans hV₀S
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨D'', i', _, hi'⟩ : ∃ (D'' : Scheme.{u}) (i' : D'' ⟶ D), IsClosedImmersion i' ∧
      Set.range i'.base = (V : Set D)ᶜ :=
    ⟨_, V.closedComplement, inferInstance, V.range_closedComplement⟩
  have hc : IsCompl (Set.range i'.base) (Set.range V.ι.base) := by
    rw [hi', Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  obtain ⟨δ, hT⟩ := exists_distTriang_openClosed_derived Λ V.ι i' hc
    ((DerivedCategory.singleFunctor _ 0).obj G)
  refine (boundedConstructible _).ext_of_isTriangulatedClosed₂ _
    ((R((c)_*⟦Λ⟧) ⋙ Φ).map_distinguished _ hT) ?_ ?_
  · exact boundedConstructible_lisse_open hΦ c S a V hVS hVU G
      ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))
  · let Z' : TopologicalSpace.Closeds T := ⟨c.base '' Set.range i'.base,
      c.isClosedEmbedding.isClosedMap _ i'.isClosedEmbedding.isClosed_range⟩
    have hZ' : Z' < Z := by
      refine IsConcreteLE.lt_iff_le_and_exists.2 ⟨fun x ⟨w, _, hw⟩ ↦ hcZ ⟨w, hw⟩,
        c.base v, hcZ ⟨v, rfl⟩, fun ⟨w, hw, hwv⟩ ↦ ?_⟩
      rw [c.isClosedEmbedding.injective hwv, hi'] at hw
      exact hw hv
    have hrange : Set.range (i' ≫ c).base ⊆ Z' := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact subset_rfl
    exact (boundedConstructible _).prop_of_iso
      (Φ.mapIso ((rightDerivedLowerStarComp Λ i' c).app _).symm)
      (ih Z' hZ' D'' (i' ≫ c) hrange _ (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ
        i' _ (boundedConstructible_singleFunctor_zero_obj Λ G hGc)))

include Φ in
/-- **Dévissage of bounded constructible complexes to lisse sheaves on locally closed
subschemes, adapted to an open** `U` of `T`: on a scheme `T` with noetherian underlying space, a
triangulated functor `Φ` which maps the extensions by zero `Rc_* j_! Rc'_* L` of the lisse
sheaves `L` along the locally closed immersions `E ⟶ W ⊆ D ⟶ T`, with `W` inside `c⁻¹ U` or
inside its complement, to bounded constructible complexes
(`ProEtale.CondensedRing.LisseHypothesisAlong`) maps all bounded constructible complexes to
bounded constructible complexes. -/
theorem boundedConstructible_obj_of_forall_lisse_along [TopologicalSpace.NoetherianSpace T]
    {U : T.Opens} (hΦ : LisseHypothesisAlong Λ Φ U)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj K) := by
  have key : ∀ Z : TopologicalSpace.Closeds T, ∀ (D : Scheme.{u}) (c : D ⟶ T)
      [IsClosedImmersion c], Set.range c.base ⊆ Z →
      ∀ M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)), boundedConstructible _ M →
        boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj M)) := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
      intro D c _ hcZ M hM
      have : TopologicalSpace.NoetherianSpace D :=
        c.isClosedEmbedding.isInducing.noetherianSpace
      exact boundedConstructible_obj_of_forall_singleFunctor (R((c)_*⟦Λ⟧) ⋙ Φ)
        (fun G hG ↦ boundedConstructible_lisse_step hΦ Z ih c hcZ G hG) hM
  have : IsEmpty (⊥ : T.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have : QuasiCompact (⊥ : T.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hc : IsCompl (Set.range (𝟙 T : T ⟶ T).base) (Set.range (⊥ : T.Opens).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact ⟨Set.disjoint_iff.2 fun x ⟨_, hx⟩ ↦ hx,
      codisjoint_iff.2 (Set.eq_univ_of_forall fun x ↦ Or.inl ⟨x, rfl⟩)⟩
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ (⊥ : T.Opens).ι (𝟙 T)
    hc (K := K) (isZero_derivedCategory_of_isEmpty' Λ _)
  exact (boundedConstructible _).prop_of_iso
    (Φ.mapIso (asIso ((derivedUpperStarLowerStarAdjunction Λ (𝟙 T)).unit.app K)).symm)
    (key ⊤ T (𝟙 T) (fun _ _ ↦ trivial) _
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ (𝟙 T) K hK))

include Φ in
/-- **Dévissage of bounded constructible complexes to lisse sheaves on locally closed
subschemes**: on a scheme `T` with noetherian underlying space, a triangulated functor `Φ` which
maps the extensions by zero `Rc_* j_! Rc'_* L` of the lisse sheaves `L` along the locally closed
immersions `E ⟶ W ⊆ D ⟶ T` to bounded constructible complexes
(`ProEtale.CondensedRing.LisseHypothesis`) maps all bounded constructible complexes to bounded
constructible complexes. -/
theorem boundedConstructible_obj_of_forall_lisse [TopologicalSpace.NoetherianSpace T]
    (hΦ : LisseHypothesis Λ Φ)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj K) :=
  boundedConstructible_obj_of_forall_lisse_along (hΦ.along ⊤) hK

end Devissage

end AlgebraicGeometry.ProEtale.CondensedRing
