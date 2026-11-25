/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitClosed

/-!
# Continuity of `Hom` out of a constructible sheaf

Blueprint `lemma-continuity-ext-out-constructible-complex--1`. Let `Λ` be a commutative condensed
ring such that `Λ_X` is flat on every scheme `X`, and such that on every scheme with noetherian
underlying space, `Hom(L[0], -[q])` commutes with filtered colimits of module objects for every
pro-étale locally finitely presented (lisse) module object `L`. Then on a scheme `T` with noetherian
underlying space the same holds for every constructible module object `M`
(`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`).

The proof is the noetherian induction of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage`
(not imported, to stay below the localizing subcategories in the import hierarchy):
a constructible sheaf `G` on a closed subscheme `c : D ⟶ T` is split, along a nonempty open `V`
of `D` contained in a stratum, by the open–closed triangle `j_! Lj^* G ⟶ G ⟶ Ri_* Li^* G ⟶`
into the extension by zero of a lisse sheaf and a sheaf supported on a smaller closed subset. The
class of objects whose morphisms commute with filtered colimits is closed under extensions
(`DerivedCategory.HomCommutesWithFilteredColimits.ext₂`), under `j_!` for open immersions
(`ProEtale.CondensedRing.homCommutesWithFilteredColimits_openImmersionLowerShriek`) and under
`Ri_*` for closed immersions
(`homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The open piece of the dévissage: the extension by zero `j_! Lj^* G` of the restriction of a
sheaf `G` on a noetherian `D` to an open `V` contained in a stratum along which `G` is lisse has
morphisms commuting with filtered colimits, as soon as lisse sheaves on noetherian schemes do:
`Lj^* G` is the pushforward along a surjective closed immersion `c' : E ⟶ V` of a lisse sheaf. -/
lemma homCommutesWithFilteredColimits_lisse_open
    (hflat : ∀ X : Scheme.{u}, PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
    (hL : ∀ (E : Scheme.{u}) [TopologicalSpace.NoetherianSpace E]
      (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
      IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
      DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
        ((DerivedCategory.singleFunctor _ 0).obj L))
    {D : Scheme.{u}} [TopologicalSpace.NoetherianSpace D] (S : Scheme.Stratification D)
    (a : Fin S.n) (V : D.Opens) (hVS : (V : Set D) ⊆ S.stratum a)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
      ((S.immersion a)^*⟦Λ⟧.obj G)) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      (D((V.ι)_!open⟦Λ⟧).obj ((L((V.ι)^*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  obtain ⟨E, c', b, hcb, _, _⟩ : ∃ (E : Scheme.{u}) (c' : E ⟶ V) (b : E ⟶ S.domain a),
      c' ≫ V.ι = b ≫ S.immersion a ∧ IsClosedImmersion c' ∧ Surjective c' := by
    have : Surjective (pullback.fst V.ι (S.immersion a)) :=
      surjective_pullback_fst_of_range_subset _ _ (by
        rw [Scheme.Opens.range_ι, S.range_immersion]
        exact hVS)
    exact ⟨_, pullback.fst V.ι (S.immersion a), pullback.snd V.ι (S.immersion a),
      pullback.condition, IsClosedImmersion.of_isImmersion_of_surjective _, this⟩
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace E := c'.isClosedEmbedding.isInducing.noetherianSpace
  have : IsEmpty (⊥ : V.toScheme.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have hc : IsCompl (Set.range c'.base) (Set.range (⊥ : V.toScheme.Opens).ι.base) := by
    rw [Set.range_eq_univ.2 c'.surjective, Scheme.Opens.range_ι]
    exact isCompl_top_bot
  have : QuasiCompact (⊥ : V.toScheme.Opens).ι :=
    ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have := hflat V
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ
    (⊥ : V.toScheme.Opens).ι c' hc
    (K := (L((V.ι)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G))
    (isZero_derivedCategory_of_isEmpty' Λ _)
  have hL' : IsLocallyFinitelyPresented (condensedRingObj Λ E) ((c' ≫ V.ι)^*⟦Λ⟧.obj G) :=
    isLocallyFinitelyPresented_upperStar_comp_of_comm (Λ := Λ) hcb hG
  exact homCommutesWithFilteredColimits_openImmersionLowerShriek Λ V.ι
    ((homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion Λ c'
      (⊥ : V.toScheme.Opens).ι hc (hL E _ hL') 0).of_iso
      (asIso ((derivedUpperStarLowerStarAdjunction Λ c').unit.app _) ≪≫
        (R((c')_*⟦Λ⟧)).mapIso (((leftDerivedUpperStarComp Λ c' V.ι).app _).symm ≪≫
          leftDerivedUpperStarSingleIso Λ (c' ≫ V.ι) G)).symm)

/-- The induction step of the dévissage, for a constructible sheaf `G` on a closed subscheme
`c : D ⟶ T` with image in the closed subset `Z`: split `G` along a nonempty open `V` of `D`
contained in a stratum; the closed piece is supported on `c(D ∖ V) < Z`. -/
lemma homCommutesWithFilteredColimits_lisse_step
    (hflat : ∀ X : Scheme.{u}, PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
    (hL : ∀ (E : Scheme.{u}) [TopologicalSpace.NoetherianSpace E]
      (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
      IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
      DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
        ((DerivedCategory.singleFunctor _ 0).obj L))
    {T : Scheme.{u}} [TopologicalSpace.NoetherianSpace T] (Z : TopologicalSpace.Closeds T)
    (ih : ∀ Z' < Z, ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c],
      Set.range c.base ⊆ Z' →
      ∀ G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D),
        IsConstructibleModuleObject (condensedRingObj Λ D) G →
        DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
          ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G)))
    {D : Scheme.{u}} (c : D ⟶ T) [IsClosedImmersion c] [TopologicalSpace.NoetherianSpace D]
    (hcZ : Set.range c.base ⊆ Z)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsConstructibleModuleObject (condensedRingObj Λ D) G) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · exact DerivedCategory.HomCommutesWithFilteredColimits.of_isZero
      ((R((c)_*⟦Λ⟧)).map_isZero (isZero_derivedCategory_of_isEmpty' Λ _))
  have hGc := hG
  obtain ⟨S, hS⟩ := hG
  obtain ⟨a, V, ⟨v, hv⟩, hVS⟩ := exists_nonempty_opens_subset_stratum S
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
  refine DerivedCategory.HomCommutesWithFilteredColimits.ext₂ _
    ((R((c)_*⟦Λ⟧)).map_distinguished _ hT) ?_ ?_
  · let W : T.Opens := ⟨(Set.range c.base)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have hcW : IsCompl (Set.range c.base) (Set.range W.ι.base) := by
      rw [Scheme.Opens.range_ι]
      exact isCompl_compl
    have := hflat T
    have : DerivedCategory.TStructure.t.IsLE (((V.ι)_!open⟦Λ⟧ ⋙
        DerivedCategory.singleFunctor _ 0).obj ((V.ι)^*⟦Λ⟧.obj G)) 0 :=
      inferInstanceAs (((DerivedCategory.singleFunctor _ 0).obj _).IsLE 0)
    have : (D((V.ι)_!open⟦Λ⟧).obj ((L((V.ι)^*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))).IsLE 0 :=
      DerivedCategory.TStructure.t.isLE_of_iso
        (((((V.ι)_!open⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
          (D((V.ι)_!open⟦Λ⟧).mapIso (leftDerivedUpperStarSingleIso Λ V.ι G)).symm) 0
    exact homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion Λ c W.ι hcW
      (s := D((V.ι)_!open⟦Λ⟧).obj ((L((V.ι)^*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)))
      (homCommutesWithFilteredColimits_lisse_open Λ hflat hL S a V hVS G
        ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))) 0
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
    exact (ih Z' hZ' D'' (i' ≫ c) hrange _
      (IsConstructibleModuleObject.upperStar Λ i' hGc)).of_iso
        (((rightDerivedLowerStarComp Λ i' c).app _).symm ≪≫
          (R((c)_*⟦Λ⟧)).mapIso ((R((i')_*⟦Λ⟧)).mapIso
            (leftDerivedUpperStarSingleIso Λ i' G).symm))

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1`, dévissage to lisse sheaves: if
`Λ_X` is flat on every scheme and `Hom(L[0], -[q])` commutes with filtered colimits for every lisse
`L` on a scheme with noetherian underlying space, then so does `Hom(M[0], -[q])` for every
constructible `M` on a scheme `T` with noetherian underlying space. -/
theorem homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject
    (hflat : ∀ X : Scheme.{u}, PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
    (hL : ∀ (E : Scheme.{u}) [TopologicalSpace.NoetherianSpace E]
      (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
      IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
      DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
        ((DerivedCategory.singleFunctor _ 0).obj L))
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ T) M) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have key : ∀ Z : TopologicalSpace.Closeds T, ∀ (D : Scheme.{u}) (c : D ⟶ T)
      [IsClosedImmersion c], Set.range c.base ⊆ Z →
      ∀ G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D),
        IsConstructibleModuleObject (condensedRingObj Λ D) G →
        DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
          ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G)) := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
      intro D c _ hcZ G hG
      have : TopologicalSpace.NoetherianSpace D :=
        c.isClosedEmbedding.isInducing.noetherianSpace
      exact homCommutesWithFilteredColimits_lisse_step Λ hflat hL Z ih c hcZ G hG
  have : IsEmpty (⊥ : T.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have : QuasiCompact (⊥ : T.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hc : IsCompl (Set.range (𝟙 T : T ⟶ T).base) (Set.range (⊥ : T.Opens).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact ⟨Set.disjoint_iff.2 fun x ⟨_, hx⟩ ↦ hx,
      codisjoint_iff.2 (Set.eq_univ_of_forall fun x ↦ Or.inl ⟨x, rfl⟩)⟩
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ (⊥ : T.Opens).ι (𝟙 T)
    hc (K := (DerivedCategory.singleFunctor _ 0).obj M) (isZero_derivedCategory_of_isEmpty' Λ _)
  exact (key ⊤ T (𝟙 T) (fun _ _ ↦ trivial) _
    (IsConstructibleModuleObject.upperStar Λ (𝟙 T) hM)).of_iso
      ((R((𝟙 T)_*⟦Λ⟧)).mapIso (leftDerivedUpperStarSingleIso Λ (𝟙 T) M).symm ≪≫
        (asIso ((derivedUpperStarLowerStarAdjunction Λ (𝟙 T)).unit.app _)).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
