/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.GenericRegularity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafDevissage

/-!
# Dévissage of constructible sheaves to lisse sheaves on connected regular schemes

Variant of `ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject` for a scheme
`T` locally of finite type over a perfect field `k`: the generators `Rc_* j_! Rc'_* L` of the
dévissage may be taken with `c' : E ⟶ V` a surjective closed immersion from a connected regular
noetherian scheme `E`
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField`).

In the induction step the open `V` contained in a stratum is shrunk, by generic smoothness, to a
nonempty open which is, up to a surjective closed immersion, a connected regular scheme
(`AlgebraicGeometry.exists_isRegular_isClosedImmersion_of_perfectField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The open piece of the dévissage, for a given surjective closed immersion `c' : E ⟶ V` over a
stratum along which `G` is lisse: `Lj^* G ≅ Rc'_* L` for the lisse `Λ_E`-module
`L = (c' ≫ j)^* G`. -/
lemma isLocallyFinitelyPresented_and_iso_openImmersionLowerShriek
    (hflat : ∀ X : Scheme.{u}, PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
    {D : Scheme.{u}} (S : Scheme.Stratification D) (a : Fin S.n) (V : D.Opens)
    {E : Scheme.{u}} (c' : E ⟶ V) [IsClosedImmersion c'] [Surjective c'] (b : E ⟶ S.domain a)
    (hcb : c' ≫ V.ι = b ≫ S.immersion a)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
      ((S.immersion a)^*⟦Λ⟧.obj G)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ E) ((c' ≫ V.ι)^*⟦Λ⟧.obj G) ∧
      Nonempty ((L((V.ι)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G) ≅
        (R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj ((c' ≫ V.ι)^*⟦Λ⟧.obj G))) := by
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
  refine ⟨isLocallyFinitelyPresented_upperStar_comp_of_comm (Λ := Λ) hcb hG, ⟨?_⟩⟩
  exact asIso ((derivedUpperStarLowerStarAdjunction Λ c').unit.app _) ≪≫
    (R((c')_*⟦Λ⟧)).mapIso (((leftDerivedUpperStarComp Λ c' V.ι).app _).symm ≪≫
      leftDerivedUpperStarSingleIso Λ (c' ≫ V.ι) G)

/-- Over a perfect field, a nonempty open `V` of a scheme `D` locally of finite type, contained in
a stratum, contains a nonempty open `V'` which is, up to a surjective closed immersion
`c' : E ⟶ V'`, a connected regular noetherian scheme, `c'` factoring through the stratum. -/
lemma exists_isRegular_isClosedImmersion_stratum {k : Type u} [Field k] [PerfectField k]
    {D : Scheme.{u}} [TopologicalSpace.NoetherianSpace D] (aD : D ⟶ Spec (.of k))
    [LocallyOfFiniteType aD] (S : Scheme.Stratification D) (a : Fin S.n) (V : D.Opens)
    (hV : (V : Set D).Nonempty) (hVS : (V : Set D) ⊆ S.stratum a) :
    ∃ (V' : D.Opens) (E : Scheme.{u}) (c' : E ⟶ V') (b : E ⟶ S.domain a),
      (V' : Set D).Nonempty ∧ IsClosedImmersion c' ∧ Surjective c' ∧
        c' ≫ V'.ι = b ≫ S.immersion a ∧ IsNoetherian E ∧ IsRegular E ∧ ConnectedSpace E := by
  have hsurj : Surjective (pullback.fst V.ι (S.immersion a)) :=
    surjective_pullback_fst_of_range_subset _ _ (by
      rw [Scheme.Opens.range_ι, S.range_immersion]
      exact hVS)
  have : IsClosedImmersion (pullback.fst V.ι (S.immersion a)) :=
    IsClosedImmersion.of_isImmersion_of_surjective _
  obtain ⟨v, hv⟩ := hV
  have : Nonempty ↥(pullback V.ι (S.immersion a)) :=
    ⟨(hsurj.surj ⟨v, hv⟩).choose⟩
  have hq : IsOpen (Set.range (pullback.fst V.ι (S.immersion a) ≫ V.ι).base) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 hsurj.surj, Set.image_univ, Scheme.Opens.range_ι]
    exact V.isOpen
  obtain ⟨V', E, c', e, hV', _, _, hce, _, _, _⟩ :=
    exists_isRegular_isClosedImmersion_of_perfectField
      (pullback.fst V.ι (S.immersion a) ≫ V.ι ≫ aD) (pullback.fst V.ι (S.immersion a) ≫ V.ι) hq
  refine ⟨V', E, c', e ≫ pullback.snd _ _, hV', inferInstance, inferInstance, ?_, inferInstance,
    inferInstance, inferInstance⟩
  rw [hce, Category.assoc, pullback.condition]

variable {Λ} in
/-- The induction step of the dévissage over a perfect field: split `G` along a nonempty open
`V` of `D` which is, up to a surjective closed immersion, a connected regular scheme on which `G`
is lisse; the closed piece is supported on `c(D ∖ V) < Z`. -/
lemma prop_rightDerivedLowerStar_singleFunctor_step_of_perfectField
    (hflat : ∀ X : Scheme.{u}, PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
    {k : Type u} [Field k] [PerfectField k]
    {T : Scheme.{u}} [TopologicalSpace.NoetherianSpace T] (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT]
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))))
    (hzero : ∀ K, IsZero K → P K) (hiso : ∀ {K K'}, (K ≅ K') → P K → P K')
    (hext : ∀ Tr ∈ distTriang _, P Tr.obj₁ → P Tr.obj₃ → P Tr.obj₂)
    (hgen : ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c] (V : D.Opens) (E : Scheme.{u})
      (c' : E ⟶ V) [IsClosedImmersion c'] [IsNoetherian E] [IsRegular E] [ConnectedSpace E]
      (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
      IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
      P ((R((c)_*⟦Λ⟧)).obj (D((V.ι)_!open⟦Λ⟧).obj
        ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L)))))
    (Z : TopologicalSpace.Closeds T)
    (ih : ∀ Z' < Z, ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c],
      Set.range c.base ⊆ Z' →
      ∀ G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D),
        IsConstructibleModuleObject (condensedRingObj Λ D) G →
        P ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G)))
    {D : Scheme.{u}} (c : D ⟶ T) [IsClosedImmersion c] [TopologicalSpace.NoetherianSpace D]
    (hcZ : Set.range c.base ⊆ Z)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsConstructibleModuleObject (condensedRingObj Λ D) G) :
    P ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · exact hzero _ ((R((c)_*⟦Λ⟧)).map_isZero (isZero_derivedCategory_of_isEmpty' Λ _))
  have hGc := hG
  obtain ⟨S, hS⟩ := hG
  obtain ⟨a, V₀, hV₀, hVS⟩ := exists_nonempty_opens_subset_stratum S
  obtain ⟨V, E, c', b, ⟨v, hv⟩, _, _, hcb, _, _, _⟩ :=
    exists_isRegular_isClosedImmersion_stratum (c ≫ aT) S a V₀ hV₀ hVS
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
  refine hext _ ((R((c)_*⟦Λ⟧)).map_distinguished _ hT) ?_ ?_
  · obtain ⟨hL, ⟨e⟩⟩ := isLocallyFinitelyPresented_and_iso_openImmersionLowerShriek Λ hflat S a V
      c' b hcb G ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))
    exact hiso ((R((c)_*⟦Λ⟧)).mapIso (D((V.ι)_!open⟦Λ⟧).mapIso e.symm))
      (hgen D c V E c' _ hL)
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
    exact hiso (((rightDerivedLowerStarComp Λ i' c).app _).symm ≪≫
          (R((c)_*⟦Λ⟧)).mapIso ((R((i')_*⟦Λ⟧)).mapIso
            (leftDerivedUpperStarSingleIso Λ i' G).symm))
      (ih Z' hZ' D'' (i' ≫ c) hrange _ (IsConstructibleModuleObject.upperStar Λ i' hGc))

variable {Λ} in
/-- **Dévissage of constructible sheaves over a perfect field**: on a scheme `T` with noetherian
underlying space, locally of finite type over a perfect field, a class `P` of objects of
`D(T, Λ)` containing the zero objects, closed under isomorphisms and extensions, and containing
the complexes `Rc_* j_! Rc'_* L` (`c : D ⟶ T` and `c' : E ⟶ V` closed immersions, `j : V ⟶ D` an
open subscheme, `E` connected, regular and noetherian, `L` a lisse `Λ_E`-module) contains every
constructible `Λ_T`-module placed in degree `0`. -/
theorem prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField
    (hflat : ∀ X : Scheme.{u}, PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X)))
    {k : Type u} [Field k] [PerfectField k]
    {T : Scheme.{u}} [TopologicalSpace.NoetherianSpace T] (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT]
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))))
    (hzero : ∀ K, IsZero K → P K) (hiso : ∀ {K K'}, (K ≅ K') → P K → P K')
    (hext : ∀ Tr ∈ distTriang _, P Tr.obj₁ → P Tr.obj₃ → P Tr.obj₂)
    (hgen : ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c] (V : D.Opens) (E : Scheme.{u})
      (c' : E ⟶ V) [IsClosedImmersion c'] [IsNoetherian E] [IsRegular E] [ConnectedSpace E]
      (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
      IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
      P ((R((c)_*⟦Λ⟧)).obj (D((V.ι)_!open⟦Λ⟧).obj
        ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ T) M) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have key : ∀ Z : TopologicalSpace.Closeds T, ∀ (D : Scheme.{u}) (c : D ⟶ T)
      [IsClosedImmersion c], Set.range c.base ⊆ Z →
      ∀ G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D),
        IsConstructibleModuleObject (condensedRingObj Λ D) G →
        P ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G)) := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
      intro D c _ hcZ G hG
      have : TopologicalSpace.NoetherianSpace D :=
        c.isClosedEmbedding.isInducing.noetherianSpace
      exact prop_rightDerivedLowerStar_singleFunctor_step_of_perfectField hflat aT P hzero hiso
        hext hgen Z ih c hcZ G hG
  have : IsEmpty (⊥ : T.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have : QuasiCompact (⊥ : T.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hc : IsCompl (Set.range (𝟙 T : T ⟶ T).base) (Set.range (⊥ : T.Opens).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact ⟨Set.disjoint_iff.2 fun x ⟨_, hx⟩ ↦ hx,
      codisjoint_iff.2 (Set.eq_univ_of_forall fun x ↦ Or.inl ⟨x, rfl⟩)⟩
  have := hflat T
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ (⊥ : T.Opens).ι (𝟙 T)
    hc (K := (DerivedCategory.singleFunctor _ 0).obj M) (isZero_derivedCategory_of_isEmpty' Λ _)
  exact hiso ((R((𝟙 T)_*⟦Λ⟧)).mapIso (leftDerivedUpperStarSingleIso Λ (𝟙 T) M).symm ≪≫
      (asIso ((derivedUpperStarLowerStarAdjunction Λ (𝟙 T)).unit.app _)).symm)
    (key ⊤ T (𝟙 T) (fun _ _ ↦ trivial) _ (IsConstructibleModuleObject.upperStar Λ (𝟙 T) hM))

end AlgebraicGeometry.ProEtale.CondensedRing
