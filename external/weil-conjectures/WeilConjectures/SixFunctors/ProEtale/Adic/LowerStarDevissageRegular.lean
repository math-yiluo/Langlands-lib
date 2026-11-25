/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissage

/-!
# Dévissage for the finiteness theorem: reduction to lisse sheaves on regular schemes

Over a perfect field `K`, the finiteness theorem for the derived pushforward of a constructible
`ℓ`-adic sheaf along a morphism `g : T ⟶ Y` between affine schemes, `Y` of finite type over `K`,
reduces to the case of lisse sheaves on *regular* integral affine schemes
(`ProEtale.finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isRegular`).
Regularity is the hypothesis under which lisse sheaves have a monodromy
(`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`).

The proof is the noetherian induction of
`ProEtale.finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isIntegral`,
in which the nonempty open `W` of the inductive step is moreover chosen so that the reduced
structure on the stratum over `W` is smooth over `K`, hence regular: the smooth locus of a
reduced irreducible scheme of finite type over a perfect field contains its generic point
(`AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- **The inductive step of the dévissage, regular form**. Let `g : Z ⟶ Y` be a morphism locally
of finite type from an affine scheme to an affine scheme of finite type over a perfect field `K`,
and assume the finiteness theorem for lisse sheaves on regular integral affine schemes over `K`
(`H`), and for constructible sheaves on the proper closed subschemes of `Z` (`ih`). Then it holds
for constructible sheaves on `Z`.

A constructible sheaf `F` on `Z` is lisse on a stratum containing a nonempty irreducible open
`o`; the reduced structure `R₀` on the stratum over `o` is integral, and its smooth locus over `K`
is a nonempty open, mapped homeomorphically onto an open of `o`. Over an affine open `W` in it,
`j^* F` is the pushforward of a lisse sheaf on the regular integral affine scheme `R₀ ×_Z W`
along the surjective closed immersion `R₀ ×_Z W ⟶ W`. -/
lemma finiteLowerStar_singleFunctor_of_isAffine_step_of_isRegular {K : Type u} [Field K]
    [PerfectField K]
    (H : ∀ ⦃Y : Scheme.{u}⦄ (_ : Y ⟶ Spec (.of K)) [LocallyOfFiniteType ‹Y ⟶ Spec (.of K)›]
      [IsAffine Y] ⦃T : Scheme.{u}⦄ [IsAffine T] [IsIntegral T] [IsRegular T] (g : T ⟶ Y)
      [LocallyOfFiniteType g] ⦃L : AdicSheaf l T⦄,
      IsAdicLisseSheaf L → finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj L))
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsAffine Y]
    {Z : Scheme.{u}} [IsAffine Z] (g : Z ⟶ Y) [LocallyOfFiniteType g]
    (ih : ∀ (Z' : Scheme.{u}) (i : Z' ⟶ Z) [IsClosedImmersion i], ¬ Function.Surjective i.base →
      ∀ F' : AdicSheaf l Z', IsAdicConstructibleSheaf F' →
        finiteLowerStar l (i ≫ g) ((DerivedCategory.singleFunctor _ 0).obj F'))
    {F : AdicSheaf l Z} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ s)
  have : IsNoetherian Z := {}
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact (finiteLowerStar l g).prop_of_isZero (isZero_of_isEmpty l _)
  -- a nonempty irreducible open `o` on which `F` is lisse up to an immersion
  obtain ⟨ι, hι, Zs, a, ha, -, hcov, hL⟩ := hF.isAdicStratifiedLisseSheaf
  obtain ⟨k, o, ho, hoi, hok⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_of_iUnion_eq
      (S := fun k ↦ Set.range (a k).base) (fun k ↦ (a k).isLocallyClosed_range)
      (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (hcov x).exists)
  let O : Z.Opens := ⟨o, ho⟩
  have hOa : Set.range O.ι.base ⊆ Set.range (a k).base := by
    rw [Scheme.Opens.range_ι]
    exact hok
  have := isClosedImmersion_pullback_snd_of_range_subset (a k) O.ι hOa
  have hsnd : Function.Surjective (pullback.snd (a k) O.ι).base :=
    Set.range_eq_univ.1 (range_pullback_snd_eq_univ_of_range_subset (a k) O.ι hOa)
  have : IsLocallyNoetherian (pullback (a k) O.ι) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (a k) O.ι ≫ O.ι ≫ g ≫ s)
  -- the reduced structure `R₀` on the stratum over `o`, an integral scheme
  let r₀ := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds ↥(pullback (a k) O.ι))).subschemeι
  have hr₀ : Function.Surjective r₀.base := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : Nonempty O := ⟨⟨hoi.nonempty.some, hoi.nonempty.some_mem⟩⟩
  have : IrreducibleSpace O := Subtype.irreducibleSpace hoi
  let e : _ ⟶ O.toScheme := r₀ ≫ pullback.snd (a k) O.ι
  have he : Function.Surjective e.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hsnd.comp hr₀
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds ↥(pullback (a k) O.ι))).subscheme :=
    irreducibleSpace_of_isClosedImmersion_of_surjective e he
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds ↥(pullback (a k) O.ι))).subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  -- the immersion `h : R₀ ⟶ Z` is a homeomorphism onto `o`, hence an open map
  let h := e ≫ O.ι
  have heh : IsHomeomorph e.base :=
    isHomeomorph_iff_isEmbedding_surjective.2 ⟨e.isClosedEmbedding.isEmbedding, he⟩
  have hinj : Function.Injective h.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact O.ι.isOpenEmbedding.injective.comp heh.injective
  have hopen : IsOpenMap h.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact O.ι.isOpenEmbedding.isOpenMap.comp heh.isOpenMap
  -- the smooth locus `V` of `R₀` over `K` contains the generic point
  let t := h ≫ g ≫ s
  let V := t.smoothLocus
  have hV : genericPoint _ ∈ V := t.genericPoint_mem_smoothLocus_of_perfectField
  -- an affine open `W` of `Z` contained in `h(V)`
  obtain ⟨W, hW, hxW, hWV⟩ : ∃ W : Z.Opens, W ∈ Z.affineOpens ∧ h (genericPoint _) ∈ W ∧
      (W : Set Z) ⊆ h.base '' V :=
    (Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
      (show h (genericPoint _) ∈ (⟨_, hopen _ V.isOpen⟩ : Z.Opens) from ⟨_, hV, rfl⟩)
  have : IsAffine W := hW
  -- the regular integral affine scheme `R = h⁻¹(W)` and the surjective closed immersion `R ⟶ W`
  let R := h ⁻¹ᵁ W
  let r : R.toScheme ⟶ W := h ∣_ W
  have hr : Function.Surjective r.base := fun w ↦ by
    obtain ⟨v, -, hv⟩ := hWV w.2
    exact ⟨⟨v, show h v ∈ W from hv ▸ w.2⟩, Subtype.ext (by
      rw [morphismRestrict_base_coe]
      exact hv)⟩
  have : IsClosedImmersion r := .of_isPreimmersion _ (Set.range_eq_univ.2 hr ▸ isClosed_univ)
  have : IsAffine R := isAffine_of_isAffineHom r
  have : Nonempty R := ⟨⟨genericPoint _, hxW⟩⟩
  have : IsIntegral R := isIntegral_of_isOpenImmersion R.ι
  have hRV : R ≤ V := fun v hv ↦ by
    obtain ⟨v', hv', hvv'⟩ := hWV hv
    rwa [hinj hvv'] at hv'
  have : Smooth (R.ι ≫ t) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_le_iff.1 fun v _ ↦ hRV v.2
  have : IsRegular R := IsRegular.of_smooth (R.ι ≫ t)
  -- `r^* j^* F` is the pullback of the lisse sheaf `a_k^* F`
  let c := R.ι ≫ r₀ ≫ pullback.fst (a k) O.ι
  have hrc : r ≫ W.ι = c ≫ a k := by
    simp only [r, c, morphismRestrict_ι, h, e, Category.assoc, pullback.condition]
    rfl
  have hLR : IsAdicLisseSheaf ((r)^*ᵃ[l].obj ((W.ι)^*ᵃ[l].obj F)) :=
    ((hL k).upperStar c).of_iso ((adicUpperStarCompIso l hrc).app F).symm
  have : IsLocallyNoetherian W := inferInstance
  have hj : finiteLowerStar l (W.ι ≫ g)
      ((DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F)) :=
    finiteLowerStar_singleFunctor_of_surjective r hr _ _ (H s _ hLR)
  have hjZ : finiteLowerStar l W.ι
      ((DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F)) :=
    finiteLowerStar_singleFunctor_of_surjective r hr _ _ (H (g ≫ s) _ hLR)
  exact finiteLowerStar_singleFunctor_of_opens g ih hF W hxW hj hjZ

/-- **Dévissage for the finiteness theorem: reduction to lisse sheaves on regular schemes**
(SGA 4½, *Th. finitude*). Over a perfect field `K`, if the derived pushforward of every lisse
`ℓ`-adic sheaf along a morphism locally of finite type from a *regular integral* affine scheme
to an affine scheme of finite type over `K` is bounded with constructible cohomology sheaves
(`H`), then so is the derived pushforward of every constructible `ℓ`-adic sheaf along a morphism
locally of finite type between affine schemes.

The proof is the noetherian induction over the closed subschemes of the source of
`ProEtale.finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isIntegral`,
with the inductive step
`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine_step_of_isRegular`. -/
theorem finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isRegular {K : Type u}
    [Field K] [PerfectField K]
    (H : ∀ ⦃Y : Scheme.{u}⦄ (_ : Y ⟶ Spec (.of K)) [LocallyOfFiniteType ‹Y ⟶ Spec (.of K)›]
      [IsAffine Y] ⦃T : Scheme.{u}⦄ [IsAffine T] [IsIntegral T] [IsRegular T] (g : T ⟶ Y)
      [LocallyOfFiniteType g] ⦃L : AdicSheaf l T⦄,
      IsAdicLisseSheaf L → finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj L))
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsAffine Y]
    {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Y) [LocallyOfFiniteType g]
    {F : AdicSheaf l T} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ s)
  have : IsNoetherian T := {}
  suffices key : ∀ C : Closeds T, ∀ (Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i],
      Set.range i.base = C → ∀ F : AdicSheaf l Z, IsAdicConstructibleSheaf F →
        finiteLowerStar l (i ≫ g) ((DerivedCategory.singleFunctor _ 0).obj F) by
    simpa using key ⊤ T (𝟙 T) (by simp) F hF
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i _ hC F hF
  have : IsAffine Z := isAffine_of_isAffineHom i
  refine finiteLowerStar_singleFunctor_of_isAffine_step_of_isRegular H s (i ≫ g)
    (fun Z' i' _ hi' F' hF' ↦ ?_) hF
  have hlt : (⟨Set.range (i' ≫ i).base, (i' ≫ i).isClosedEmbedding.isClosed_range⟩ :
      Closeds T) < C := by
    refine SetLike.coe_ssubset_coe.1 ?_
    change Set.range (i' ≫ i).base ⊂ (C : Set T)
    rw [← hC, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    refine lt_of_le_of_ne (Set.image_subset_range _ _) fun h ↦ hi' fun z ↦ ?_
    have hz : i.base z ∈ i.base '' Set.range i'.base := h ▸ ⟨z, rfl⟩
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hz
    exact ⟨y, i.isClosedEmbedding.injective hy⟩
  simpa only [Category.assoc] using ih _ hlt Z' (i' ≫ i) rfl F' hF'

end AlgebraicGeometry.ProEtale
