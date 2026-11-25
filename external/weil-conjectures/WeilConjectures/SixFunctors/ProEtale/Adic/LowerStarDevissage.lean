/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar

/-!
# Dévissage for the finiteness theorem: reduction to lisse sheaves

The finiteness theorem for the derived pushforward of a constructible `ℓ`-adic sheaf along a
morphism `g : T ⟶ Y` between affine schemes, `Y` of finite type over a field `K`
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`), reduces to the case of
lisse sheaves (SGA 4½, *Th. finitude*):
`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf`.

The proof is a noetherian induction over the closed subschemes of `T`. A constructible sheaf `F`
on `T` is lisse on a stratum containing a nonempty affine open `j : W ⟶ T`; on `W` it is the
pushforward of a lisse sheaf along the surjective closed immersion of the stratum
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_adicUpperStar_of_range_subset`). The
cone of the unit `F ⟶ Rj_* j^* F` vanishes on `W`, hence is `Ri_*` of its restriction to the
closed complement `i` of `W`
(`AlgebraicGeometry.ProEtale.isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero`),
to which the induction hypothesis applies.

## Main results

- `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_of_iUnion_eq`: one piece of a
  finite locally closed cover of a nonempty noetherian space contains a nonempty irreducible open.
- `AlgebraicGeometry.ProEtale.finiteLowerStar_rightDerivedFunctor_obj_iff`: the finiteness
  property for `Rh_* Ri_* K` is the one for `R(i ≫ h)_* K`.
- `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_surjective`: the finiteness
  property can be checked after pullback along a surjective closed immersion.
- `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine_step`: the inductive step.
- `ProEtale.finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isIntegral`:
  the reduction to lisse sheaves on integral affine schemes, and its corollary
  `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

/-- In a nonempty noetherian space covered by finitely many locally closed subsets, one of them
contains a nonempty irreducible open subset: an irreducible nonempty open subset `o` is contained
in one of the closures of the pieces it meets, and its intersection with the open part of that
piece is open, nonempty, irreducible and contained in the piece. -/
lemma TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_of_iUnion_eq
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [Nonempty X] {ι : Type*} [Finite ι]
    {S : ι → Set X} (hS : ∀ k, IsLocallyClosed (S k)) (hcov : ⋃ k, S k = Set.univ) :
    ∃ k, ∃ o : Set X, IsOpen o ∧ IsIrreducible o ∧ o ⊆ S k := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨Z₀, hZ₀, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  obtain ⟨o, ho, hne, hoZ⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
    Z₀ hZ₀
  have hirr : IsIrreducible o := ⟨hne, hZ₀.1.2.open_subset ho hoZ⟩
  choose U C hU hC hUC using hS
  obtain ⟨z, hz, hoz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hirr)
    ((Finset.univ.filter fun k ↦ (o ∩ U k).Nonempty).image C)
    (by simp only [Finset.mem_image]; rintro _ ⟨k, -, rfl⟩; exact hC k) (by
      intro y hy
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcov.symm ▸ Set.mem_univ y : y ∈ ⋃ k, S k)
      rw [hUC] at hk
      exact Set.mem_sUnion.2 ⟨C k, by simpa using ⟨k, ⟨y, hy, hk.1⟩, rfl⟩, hk.2⟩)
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  exact ⟨k, o ∩ U k, ho.inter (hU k),
    ⟨hk, hirr.isPreirreducible.open_subset (ho.inter (hU k)) Set.inter_subset_left⟩,
    fun y hy ↦ hUC k ▸ ⟨hy.2, hoz hy.1⟩⟩

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The finiteness property for `Rh_* (Ri_* K)` is the finiteness property for `R(i ≫ h)_* K`. -/
lemma finiteLowerStar_rightDerivedFunctor_obj_iff {Z X Y : Scheme.{u}} (i : Z ⟶ X) (h : X ⟶ Y)
    (K : DerivedCategory (AdicSheaf l Z)) :
    finiteLowerStar l h ((i)_*ᵃ[l].rightDerivedFunctor.obj K) ↔ finiteLowerStar l (i ≫ h) K := by
  let e : (h)_*ᵃ[l].rightDerivedFunctor.obj ((i)_*ᵃ[l].rightDerivedFunctor.obj K) ≅
      (i ≫ h)_*ᵃ[l].rightDerivedFunctor.obj K :=
    (Functor.rightDerivedFunctorCompIso' (i)_*ᵃ[l] (h)_*ᵃ[l] (adicLowerStarComp l i h)).app K
  exact ⟨fun H ↦ finiteLowerStar_of_iso (i ≫ h) (K := K) e.symm H,
    fun H ↦ finiteLowerStar_of_iso h (K' := K) e H⟩

/-- For a closed immersion `i` into a locally noetherian scheme, the finiteness property for
`i_* L` along `h` is the finiteness property for `L` along `i ≫ h`, `i_*` being exact. -/
lemma finiteLowerStar_singleFunctor_adicLowerStar_obj_iff {Z X Y : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] (h : X ⟶ Y) (L : AdicSheaf l Z) :
    finiteLowerStar l h ((DerivedCategory.singleFunctor _ 0).obj ((i)_*ᵃ[l].obj L)) ↔
      finiteLowerStar l (i ≫ h) ((DerivedCategory.singleFunctor _ 0).obj L) := by
  have := preservesFiniteColimits_adicLowerStar_of_isClosedImmersion (l := l) i
  rw [← finiteLowerStar_rightDerivedFunctor_obj_iff]
  exact (finiteLowerStar l h).prop_iff_of_iso
    (((((i)_*ᵃ[l]).mapDerivedCategorySingleFunctor 0).app L).symm ≪≫
      (((i)_*ᵃ[l]).rightDerivedFunctorIsoMapDerivedCategory.app _).symm)

variable (l) in
/-- Every `ℓ`-adic sheaf on an empty scheme vanishes: the empty family covers it. -/
lemma AdicSheaf.isZero_of_isEmpty {T : Scheme.{u}} [IsEmpty T] (M : AdicSheaf l T) : IsZero M :=
  ((DerivedCategory.homologyFunctor _ 0).map_isZero
    (ProEtale.isZero_of_isEmpty l ((DerivedCategory.singleFunctor _ 0).obj M))).of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm

/-- The base change of `a` along a morphism `j` whose range is contained in that of `a` is
surjective. -/
lemma range_pullback_snd_eq_univ_of_range_subset {X Z' W : Scheme.{u}} (a : Z' ⟶ X) (j : W ⟶ X)
    (hja : Set.range j.base ⊆ Set.range a.base) :
    Set.range (pullback.snd a j).base = Set.univ := by
  rw [Scheme.Pullback.range_snd]
  exact Set.eq_univ_of_forall fun w ↦ hja ⟨w, rfl⟩

/-- The base change of an immersion `a` along a morphism `j` whose range is contained in that of
`a` is a surjective closed immersion. -/
lemma isClosedImmersion_pullback_snd_of_range_subset {X Z' W : Scheme.{u}} (a : Z' ⟶ X)
    [IsImmersion a] (j : W ⟶ X) (hja : Set.range j.base ⊆ Set.range a.base) :
    IsClosedImmersion (pullback.snd a j) :=
  .of_isPreimmersion _ (range_pullback_snd_eq_univ_of_range_subset a j hja ▸ isClosed_univ)

/-- Let `a : Z' ⟶ X` be an immersion and `j : W ⟶ X` an open immersion with range contained in
that of `a`. Then `W ×_X Z' ⟶ W` is a surjective closed immersion, so the restriction `j^* F` of
an `ℓ`-adic sheaf is the pushforward of the restriction of `a^* F` to `W ×_X Z'`: the finiteness
property for `j^* F` along `h` follows from that of `a^* F|_{W ×_X Z'}` along the composite. -/
lemma finiteLowerStar_singleFunctor_adicUpperStar_of_range_subset {X Z' W Y : Scheme.{u}}
    (a : Z' ⟶ X) [IsImmersion a] (j : W ⟶ X) [IsOpenImmersion j] [IsLocallyNoetherian W]
    (hja : Set.range j.base ⊆ Set.range a.base) (F : AdicSheaf l X) (h : W ⟶ Y)
    (H : finiteLowerStar l (pullback.snd a j ≫ h)
      ((DerivedCategory.singleFunctor _ 0).obj ((pullback.fst a j)^*ᵃ[l].obj ((a)^*ᵃ[l].obj F)))) :
    finiteLowerStar l h ((DerivedCategory.singleFunctor _ 0).obj ((j)^*ᵃ[l].obj F)) := by
  have := isClosedImmersion_pullback_snd_of_range_subset a j hja
  have hc : IsCompl (Set.range (pullback.snd a j).base) (Set.range (⊥ : W.Opens).ι.base) := by
    rw [range_pullback_snd_eq_univ_of_range_subset a j hja, Scheme.Opens.range_ι, Opens.coe_bot]
    exact isCompl_top_bot
  have : QuasiCompact (⊥ : W.Opens).ι :=
    ⟨fun _ _ _ ↦ Set.Subsingleton.isCompact fun x _ ↦ x.2.elim⟩
  have : IsEmpty (⊥ : W.Opens).toScheme := ⟨fun x ↦ x.2.elim⟩
  have := isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl (l := l)
    (pullback.snd a j) (⊥ : W.Opens).ι hc ((j)^*ᵃ[l].obj F) (AdicSheaf.isZero_of_isEmpty l _)
  refine (finiteLowerStar l h).prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    ((pullback.snd a j)_*ᵃ[l].mapIso ((adicUpperStarCompIso l pullback.condition).app F) ≪≫
      (asIso ((adicUpperStarLowerStarAdjunction l _).unit.app _)).symm)) ?_
  exact (finiteLowerStar_singleFunctor_adicLowerStar_obj_iff _ h _).2 H

/-- Along a surjective closed immersion `r : R ⟶ P` into a locally noetherian scheme, the
finiteness property for `L` along `h` follows from that of `r^* L` along `r ≫ h`: the unit
`L ⟶ r_* r^* L` is an isomorphism, the open complement of `r` being empty. -/
lemma finiteLowerStar_singleFunctor_of_surjective {R P Y : Scheme.{u}} (r : R ⟶ P)
    [IsClosedImmersion r] [IsLocallyNoetherian P] (hr : Function.Surjective r.base)
    (L : AdicSheaf l P) (h : P ⟶ Y)
    (H : finiteLowerStar l (r ≫ h) ((DerivedCategory.singleFunctor _ 0).obj ((r)^*ᵃ[l].obj L))) :
    finiteLowerStar l h ((DerivedCategory.singleFunctor _ 0).obj L) := by
  have hc : IsCompl (Set.range r.base) (Set.range (⊥ : P.Opens).ι.base) := by
    rw [hr.range_eq, Scheme.Opens.range_ι, Opens.coe_bot]
    exact isCompl_top_bot
  have : QuasiCompact (⊥ : P.Opens).ι :=
    ⟨fun _ _ _ ↦ Set.Subsingleton.isCompact fun x _ ↦ x.2.elim⟩
  have : IsEmpty (⊥ : P.Opens).toScheme := ⟨fun x ↦ x.2.elim⟩
  have := isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl (l := l)
    r (⊥ : P.Opens).ι hc L (AdicSheaf.isZero_of_isEmpty l _)
  refine (finiteLowerStar l h).prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    (asIso ((adicUpperStarLowerStarAdjunction l r).unit.app L)).symm) ?_
  exact (finiteLowerStar_singleFunctor_adicLowerStar_obj_iff _ h _).2 H

/-- A surjective closed immersion `r : R ⟶ W` onto an irreducible scheme has irreducible source,
being a homeomorphism. -/
lemma irreducibleSpace_of_isClosedImmersion_of_surjective {R W : Scheme.{u}} (r : R ⟶ W)
    [IsClosedImmersion r] (hr : Function.Surjective r.base) [IrreducibleSpace W] :
    IrreducibleSpace R := by
  let e := (isHomeomorph_iff_isEmbedding_surjective.2
    ⟨r.isClosedEmbedding.isEmbedding, hr⟩).homeomorph
  refine (irreducibleSpace_def R).2 ?_
  have := (IrreducibleSpace.isIrreducible_univ W).image _ e.symm.continuous.continuousOn
  rwa [Set.image_univ_of_surjective e.symm.surjective] at this

/-- **The inductive step of the dévissage, given a good open.** Let `g : Z ⟶ Y` be a morphism
between locally noetherian schemes, `F` a constructible sheaf on `Z` and `W` a nonempty open of
`Z` such that `j^* F` has bounded constructible derived pushforward along `j : W ⟶ Z` (`hjZ`)
and along `j ≫ g` (`hj`). If the finiteness theorem holds for constructible sheaves on the proper
closed subschemes of `Z` (`ih`), then it holds for `F`: the cone `C` of the unit
`F ⟶ Rj_* j^* F` is bounded with constructible cohomology sheaves and vanishes on `W`, so
`C ≅ Ri_* i^* C` for the closed complement `i : Z₁ ⟶ Z` of `W`. -/
lemma finiteLowerStar_singleFunctor_of_opens {Y Z : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] (g : Z ⟶ Y)
    (ih : ∀ (Z' : Scheme.{u}) (i : Z' ⟶ Z) [IsClosedImmersion i], ¬ Function.Surjective i.base →
      ∀ F' : AdicSheaf l Z', IsAdicConstructibleSheaf F' →
        finiteLowerStar l (i ≫ g) ((DerivedCategory.singleFunctor _ 0).obj F'))
    {F : AdicSheaf l Z} (hF : IsAdicConstructibleSheaf F) (W : Z.Opens) {x : Z} (hxW : x ∈ W)
    (hj : finiteLowerStar l (W.ι ≫ g)
      ((DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F)))
    (hjZ : finiteLowerStar l W.ι
      ((DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F))) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj F) := by
  -- the closed complement `i₁ : Z₁ ⟶ Z` of `W`
  let i₁ := (Scheme.IdealSheafData.vanishingIdeal
    (⟨(W : Set Z)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds Z)).subschemeι
  have hi₁ : Set.range i₁.base = (W : Set Z)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hij : IsCompl (Set.range i₁.base) (Set.range W.ι.base) := by
    rw [hi₁, Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  have hns : ¬ Function.Surjective i₁.base := fun h ↦ by
    obtain ⟨y, hy⟩ := h x
    have hx' : x ∈ Set.range i₁.base := ⟨y, hy⟩
    rw [hi₁] at hx'
    exact hx' hxW
  -- the triangle `F ⟶ Rj_* j^* F ⟶ C ⟶ F[1]`
  let M := (DerivedCategory.singleFunctor (AdicSheaf l Z) 0).obj F
  let adj := adicDerivedUpperStarLowerStarAdjunction l W.ι
  obtain ⟨C, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle (adj.unit.app M)
  let eM : (W.ι)^*ᵃ[l].mapDerivedCategory.obj M ≅
      (DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F) :=
    ((W.ι)^*ᵃ[l].mapDerivedCategorySingleFunctor 0).app F
  have h₂ : finiteLowerStar l g
      ((W.ι)_*ᵃ[l].rightDerivedFunctor.obj ((W.ι)^*ᵃ[l].mapDerivedCategory.obj M)) :=
    (finiteLowerStar_rightDerivedFunctor_obj_iff W.ι g _).2
      ((finiteLowerStar l (W.ι ≫ g)).prop_of_iso eM.symm hj)
  have hiso : IsIso ((W.ι)^*ᵃ[l].mapDerivedCategory.map (adj.unit.app M)) := by
    have h := adj.left_triangle_components M
    have : IsIso ((W.ι)^*ᵃ[l].mapDerivedCategory.map (adj.unit.app M) ≫
        adj.counit.app ((W.ι)^*ᵃ[l].mapDerivedCategory.obj M)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app ((W.ι)^*ᵃ[l].mapDerivedCategory.obj M))
  have hCU : IsZero ((W.ι)^*ᵃ[l].mapDerivedCategory.obj C) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      ((W.ι)^*ᵃ[l].mapDerivedCategory.map_distinguished _ hT) hiso
  -- the cone is bounded with constructible cohomology, and supported on `Z₁`
  have hM : DerivedCategory.boundedConstructibleAdic l Z M :=
    ⟨(bounded_homologyProperty_singleFunctor hF).1, (bounded_homologyProperty_singleFunctor hF).2⟩
  have hR : DerivedCategory.boundedConstructibleAdic l Z
      ((W.ι)_*ᵃ[l].rightDerivedFunctor.obj ((W.ι)^*ᵃ[l].mapDerivedCategory.obj M)) :=
    (DerivedCategory.boundedConstructibleAdic l Z).prop_of_iso
      ((W.ι)_*ᵃ[l].rightDerivedFunctor.mapIso eM.symm) hjZ
  have hC : DerivedCategory.boundedConstructibleAdic l Z C :=
    (DerivedCategory.boundedConstructibleAdic l Z).ext_of_isTriangulatedClosed₃ _ hT hM hR
  have := isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero i₁ W.ι hij hCU
  have hC' := bounded_homologyProperty_mapDerivedCategory_adicUpperStar (l := l) i₁ hC.1 hC.2
  have h₃ : finiteLowerStar l g C :=
    (finiteLowerStar l g).prop_of_iso
      (asIso ((adicDerivedUpperStarLowerStarAdjunction l i₁).unit.app C)).symm
      ((finiteLowerStar_rightDerivedFunctor_obj_iff i₁ g _).2
        (finiteLowerStar_of_bounded (i₁ ≫ g) (fun F' hF' ↦ ih _ i₁ hns F' hF') _ hC'.1 hC'.2))
  exact (finiteLowerStar l g).ext_of_isTriangulatedClosed₁ _ hT h₂ h₃

/-- **The inductive step of the dévissage**. Let `g : Z ⟶ Y` be a morphism locally of finite type
from an affine scheme to an affine scheme of finite type over a field `K`, and assume the
finiteness theorem for lisse sheaves over `K` (`H`), and for constructible sheaves on the proper
closed subschemes of `Z` (`ih`). Then it holds for constructible sheaves on `Z`.

A constructible sheaf `F` on `Z` is lisse on a stratum containing a nonempty affine open `W`,
with closed complement `i : Z₁ ⟶ Z`. By `H`, `j^* F` has bounded constructible derived
pushforward along `j : W ⟶ Z` and along `j ≫ g`. The cone `C` of the unit
`F ⟶ Rj_* j^* F` vanishes on `W`, so `C ≅ Ri_* i^* C`, and `C` is bounded with constructible
cohomology; by `ih`, `R(i ≫ g)_* i^* C` is bounded constructible, hence so is `Rg_* F`. -/
lemma finiteLowerStar_singleFunctor_of_isAffine_step {K : Type u} [Field K]
    (H : ∀ ⦃Y : Scheme.{u}⦄ (_ : Y ⟶ Spec (.of K)) [LocallyOfFiniteType ‹Y ⟶ Spec (.of K)›]
      [IsAffine Y] ⦃T : Scheme.{u}⦄ [IsAffine T] [IsIntegral T] (g : T ⟶ Y)
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
  -- a nonempty affine open `W` on which `F` is lisse up to a surjective closed immersion
  obtain ⟨ι, hι, Zs, a, ha, -, hcov, hL⟩ := hF.isAdicStratifiedLisseSheaf
  obtain ⟨k, o, ho, hoi, hok⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_of_iUnion_eq
      (S := fun k ↦ Set.range (a k).base) (fun k ↦ (a k).isLocallyClosed_range)
      (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (hcov x).exists)
  obtain ⟨x, hx⟩ := hoi.nonempty
  obtain ⟨W, hW, hxW, hWo⟩ : ∃ W : Z.Opens, W ∈ Z.affineOpens ∧ x ∈ W ∧ W ≤ ⟨o, ho⟩ :=
    (Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens) (show x ∈ (⟨o, ho⟩ : Z.Opens) from hx)
  have : IsAffine W := hW
  have : NoetherianSpace W := NoetherianSpace.set (W : Set Z)
  have hWa : Set.range W.ι.base ⊆ Set.range (a k).base := by
    rw [Scheme.Opens.range_ι]
    exact (show (W : Set Z) ⊆ o from hWo).trans hok
  have := isClosedImmersion_pullback_snd_of_range_subset (a k) W.ι hWa
  have : IsAffine (pullback (a k) W.ι) := isAffine_of_isAffineHom (pullback.snd (a k) W.ι)
  -- the reduced structure `R` on the stratum over `W`, an integral affine scheme
  have : IsLocallyNoetherian (pullback (a k) W.ι) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (a k) W.ι ≫ W.ι ≫ g ≫ s)
  let r := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds ↥(pullback (a k) W.ι))).subschemeι
  have hr : Function.Surjective r.base := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsAffine (Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds ↥(pullback (a k) W.ι))).subscheme := isAffine_of_isAffineHom r
  have : IrreducibleSpace W := Subtype.irreducibleSpace
    ⟨⟨x, hxW⟩, hoi.isPreirreducible.open_subset W.isOpen hWo⟩
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds ↥(pullback (a k) W.ι))).subscheme :=
    irreducibleSpace_of_isClosedImmersion_of_surjective (r ≫ pullback.snd (a k) W.ι)
      (by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_eq_univ.1 (range_pullback_snd_eq_univ_of_range_subset (a k) W.ι
          hWa)).comp hr)
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds ↥(pullback (a k) W.ι))).subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hj : finiteLowerStar l (W.ι ≫ g)
      ((DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F)) :=
    finiteLowerStar_singleFunctor_adicUpperStar_of_range_subset (a k) W.ι hWa F _
      (finiteLowerStar_singleFunctor_of_surjective r hr _ _
        (H s _ (((hL k).upperStar _).upperStar r)))
  have hjZ : finiteLowerStar l W.ι
      ((DerivedCategory.singleFunctor _ 0).obj ((W.ι)^*ᵃ[l].obj F)) :=
    finiteLowerStar_singleFunctor_adicUpperStar_of_range_subset (a k) W.ι hWa F _
      (finiteLowerStar_singleFunctor_of_surjective r hr _ _
        (H (g ≫ s) _ (((hL k).upperStar _).upperStar r)))
  exact finiteLowerStar_singleFunctor_of_opens g ih hF W hxW hj hjZ


/-- **Dévissage for the finiteness theorem: reduction to lisse sheaves** (SGA 4½,
*Th. finitude*), integral form. Over a field `K`, if the derived pushforward of every lisse
`ℓ`-adic sheaf along a morphism locally of finite type from an *integral* affine scheme to an
affine scheme of finite type over `K` is bounded with constructible cohomology sheaves (`H`),
then so is the derived pushforward of every constructible `ℓ`-adic sheaf along a morphism
locally of finite type between affine schemes.

The proof is a noetherian induction over the closed subschemes of the source
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine_step`): a constructible
sheaf is lisse, up to a surjective closed immersion from an integral scheme, on a nonempty
irreducible affine open, and the cone of the unit of the restriction to it is supported on the
closed complement. -/
theorem finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isIntegral {K : Type u}
    [Field K]
    (H : ∀ ⦃Y : Scheme.{u}⦄ (_ : Y ⟶ Spec (.of K)) [LocallyOfFiniteType ‹Y ⟶ Spec (.of K)›]
      [IsAffine Y] ⦃T : Scheme.{u}⦄ [IsAffine T] [IsIntegral T] (g : T ⟶ Y)
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
  refine finiteLowerStar_singleFunctor_of_isAffine_step H s (i ≫ g)
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

/-- **Dévissage for the finiteness theorem: reduction to lisse sheaves** (SGA 4½,
*Th. finitude*). Over a field `K`, if the derived pushforward of every lisse `ℓ`-adic sheaf along
a morphism locally of finite type between affine schemes, with target of finite type over `K`,
is bounded with constructible cohomology sheaves (`H`), then so is the derived pushforward of
every constructible `ℓ`-adic sheaf. It suffices to know `H` for integral sources
(`finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isIntegral`). -/
theorem finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf {K : Type u} [Field K]
    (H : ∀ ⦃Y : Scheme.{u}⦄ (_ : Y ⟶ Spec (.of K)) [LocallyOfFiniteType ‹Y ⟶ Spec (.of K)›]
      [IsAffine Y] ⦃T : Scheme.{u}⦄ [IsAffine T] (g : T ⟶ Y) [LocallyOfFiniteType g]
      ⦃L : AdicSheaf l T⦄,
      IsAdicLisseSheaf L → finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj L))
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsAffine Y]
    {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Y) [LocallyOfFiniteType g]
    {F : AdicSheaf l T} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj F) :=
  finiteLowerStar_singleFunctor_of_isAffine_of_isAdicLisseSheaf_of_isIntegral
    (fun _ s _ _ _ _ _ g _ _ hL ↦ H s g hL) s g hF

end AlgebraicGeometry.ProEtale
