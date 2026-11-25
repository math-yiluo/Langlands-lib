/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosurePointDimension
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.ConstructibleSheaf.Simple
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.Algebra.Homology.DerivedCategory.HomologyDevissage
public import WeilConjectures.SixFunctors.Etale.Perverse.StalkSupport
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Stalks of compactly supported pushforwards and the perverse amplitude

This file collects the inputs of Artin–Gabber
(`AlgebraicGeometry.Etale.DerivedCategory.isPerverseLE_lowerShriek`): the stalk of
`Rᵠf_! G` at a point `y` vanishes for `q` larger than twice the dimension of the part of the
support of `G` lying over `y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A sheaf vanishes on every open disjoint from its support. -/
lemma isZero_upperStar_of_disjoint_sheafSupport {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Opens)
    (hV : Disjoint (V : Set X) (sheafSupport G)) :
    IsZero (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj G) := by
  rw [isZero_iff_stalkZeroLocus_eq_univ]
  refine Set.eq_univ_of_forall fun x ↦ mem_stalkZeroLocus_upperStar V.ι G ?_
  have hx : V.ι.base x ∉ sheafSupport G := Set.disjoint_left.1 hV (by simp)
  simp only [sheafSupport, Set.mem_ofPred_eq, not_forall, not_not] at hx
  obtain ⟨U, hxU, hU⟩ := hx
  have h := (isZero_iff_stalkZeroLocus_eq_univ _).1 hU
  have := mem_stalkZeroLocus_of_upperStar U.ι G (y := ⟨_, hxU⟩) (h ▸ Set.mem_univ _)
  simpa using this

variable [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

open _root_.DerivedCategory Pretriangulated in
/-- **Stalks of `Rᵠf_!` above twice the fibre dimension of the support.** Let `f : X ⟶ Y` be a
compactifiable morphism of finite type to a scheme of finite type over a field, `G` a
constructible sheaf on `X`, and `s : Spec Ω ⟶ Y` a point with values in a field, lying over
`y ∈ Y`. If the part `supp G ∩ f⁻¹(y)` of the support of `G` over `y` has dimension at most `e`,
then `s^* Rᵠf_! G = 0` for `q > 2e`; if it is empty, then `s^* Rᵠf_! G = 0` for every `q`.
Writing `G = i_* i^* G` for the closed immersion `i` of the support, `Rf_! G = R(f ∘ i)_! i^* G`,
and by compactly supported base change `s^* R(f ∘ i)_! = R(f ∘ i)_{s,!} t^*` for the base change
`(f ∘ i)_s` of `f ∘ i` along `s`, whose source has dimension at most that of
`supp G ∩ f⁻¹(y)`. -/
theorem isZero_upperStar_homology_rightDerivedLowerShriek_singleFunctor
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ Y) (e : ℕ) (q : ℤ)
    (he : (sheafSupport G ∩ f ⁻¹' {s.base (IsLocalRing.closedPoint Ω)}).Nonempty →
      topologicalKrullDim (sheafSupport G ∩ f ⁻¹' {s.base (IsLocalRing.closedPoint Ω)} : Set X)
        ≤ (e : WithBot ℕ∞) ∧ (2 * e : ℤ) < q) :
    IsZero (((s)^*[ModuleCat.{u + 1} Λ]).obj ((homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((singleFunctor _ 0).obj G)))) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  -- the closed immersion of the support of `G`
  let V : X.Opens := ⟨(sheafSupport G)ᶜ, (isClosed_sheafSupport G).isOpen_compl⟩
  let i := V.closedComplement
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by simp [i]
  have hi : Set.range i.base = sheafSupport G := by
    rw [hij, Scheme.Opens.range_ι]
    simp [V]
  let K := (singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj G
  have hK : IsZero (D((V.ι)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    ((singleFunctor _ 0).map_isZero (isZero_upperStar_of_disjoint_sheafSupport G V
      disjoint_compl_left)).of_iso
      ((((V.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G)
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) V.ι i hij K
  have : IsIso ((mapDerivedUpperStarLowerStarAdjunction _ i).unit.app K) :=
    (Triangle.isZero₁_iff_isIso₂ _ hw).1 (D((V.ι)_!open[ModuleCat.{u + 1} Λ]).map_isZero hK)
  let M := D((i)^*[ModuleCat.{u + 1} Λ]).obj K
  let eK : K ≅ (R(i)_![ModuleCat.{u + 1} Λ]).obj M :=
    asIso ((mapDerivedUpperStarLowerStarAdjunction _ i).unit.app K) ≪≫
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app M).symm
  -- the composite `g = f ∘ i` and its base change along `s`
  let g := i ≫ f
  have : IsSeparated f := inferInstance
  have : HasCompactification g := inferInstance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ i f
  let P := pullback g s
  let t := pullback.fst g s
  let g' := pullback.snd g s
  have sq : IsPullback t g' g s := IsPullback.of_hasPullback g s
  have : QuasiCompact g' := MorphismProperty.of_isPullback sq inferInstance
  have : LocallyOfFiniteType g' := MorphismProperty.of_isPullback sq inferInstance
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  -- the chain of isomorphisms
  let E := ((leftDerivedUpperStarHomologyFunctorIso _ s q).app _ ≪≫
    (homologyFunctor _ q).mapIso ((L((s)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((R(f)_![ModuleCat.{u + 1} Λ]).mapIso eK ≪≫ (c.app M).symm) ≪≫
      asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app M)))
  refine IsZero.of_iso ?_ E
  -- an empty fibre contributes nothing
  by_cases hP : IsEmpty P
  · exact (homologyFunctor _ q).map_isZero ((R(g')_![ModuleCat.{u + 1} Λ]).map_isZero
      (isZero_derivedCategory_of_isEmpty _ P _))
  rw [not_isEmpty_iff] at hP
  obtain ⟨p⟩ := hP
  set y := s.base (IsLocalRing.closedPoint Ω)
  have hgp : g.base (t.base p) = y := by
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact congrArg s.base (Subsingleton.elim _ _)
  obtain ⟨hdim, hq⟩ := he ⟨i.base (t.base p), hi ▸ Set.mem_range_self _, hgp⟩
  -- the dimension of the fibre
  have hdimP : topologicalKrullDim P ≤ (e : WithBot ℕ∞) := by
    refine (topologicalKrullDim_pullback_le_preimage g s).trans (le_trans ?_ hdim)
    let r : g ⁻¹' {y} → (sheafSupport G ∩ f ⁻¹' {y} : Set X) :=
      fun x ↦ ⟨i.base x.1, hi ▸ Set.mem_range_self _, x.2⟩
    refine Topology.IsInducing.topologicalKrullDim_le (f := r)
      (.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val ?_)
    exact i.isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have : HasInvertibleExponent Λ (Spec (.of Ω)) := HasInvertibleExponent.of_hom (s ≫ aY)
  have : IsConstructibleSheaf (((i)^*[ModuleCat.{u + 1} Λ]).obj G) :=
    IsConstructibleSheaf.upperStar i G
  have : IsConstructibleSheaf (((t)^*[ModuleCat.{u + 1} Λ]).obj
      (((i)^*[ModuleCat.{u + 1} Λ]).obj G)) := IsConstructibleSheaf.upperStar t _
  have hv := isZero_homology_rightDerivedLowerShriek_singleFunctor Λ (k := Ω) g' g' (𝟙 _)
    (Category.comp_id _) e (fun Ω' _ _ s' ↦ (topologicalKrullDim_pullback_le g' s').trans hdimP)
    (((t)^*[ModuleCat.{u + 1} Λ]).obj (((i)^*[ModuleCat.{u + 1} Λ]).obj G)) q hq
  refine hv.of_iso ((homologyFunctor _ q).mapIso ((R(g')_![ModuleCat.{u + 1} Λ]).mapIso ?_))
  exact (leftDerivedUpperStarIsoMapDerivedCategory _ t).app M ≪≫
    D((t)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G) ≪≫
    (((t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _


/-- **Pointwise estimate behind Artin–Gabber.** Let `f : X ⟶ Y` be a compactifiable morphism of
finite type to a scheme of finite type over a field, whose fibres have dimension at most `d`,
`G` a constructible sheaf on `X` and `s : Spec Ω ⟶ Y` a point with values in a field, lying over
`y ∈ Y`. If `s^* Rᵠf_! G ≠ 0`, then the support of `G` meets `f⁻¹(y)` in a set of some dimension
`e ≤ d` with `q ≤ 2e`, and `dim {y}⁻ + e ≤ dim supp G`. -/
theorem exists_le_of_not_isZero_upperStar_homology_rightDerivedLowerShriek_singleFunctor
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f] (d : ℕ)
    (hf : ∀ y : Y, topologicalKrullDim (f ⁻¹' {y}) ≤ (d : WithBot ℕ∞))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ Y) (q : ℤ)
    (hs : ¬ IsZero (((s)^*[ModuleCat.{u + 1} Λ]).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))))) :
    ∃ e : ℕ, e ≤ d ∧ q ≤ 2 * e ∧ (sheafSupport G).Nonempty ∧
      topologicalKrullDim (closure {s.base (IsLocalRing.closedPoint Ω)} : Set Y) + e ≤
        topologicalKrullDim (sheafSupport G) := by
  set y := s.base (IsLocalRing.closedPoint Ω)
  have hW : (sheafSupport G ∩ f ⁻¹' {y}).Nonempty := by
    by_contra hW
    exact hs (isZero_upperStar_homology_rightDerivedLowerShriek_singleFunctor aY f G s 0 q
      fun h ↦ absurd h hW)
  have : Nonempty (sheafSupport G ∩ f ⁻¹' {y} : Set X) := hW.to_subtype
  obtain ⟨e, hed, he⟩ := exists_topologicalKrullDim_eq_natCast
    (((Topology.IsEmbedding.inclusion (Set.inter_subset_right (s := sheafSupport G))
      ).isInducing.topologicalKrullDim_le).trans (hf y))
  refine ⟨e, hed, ?_, hW.mono Set.inter_subset_left, ?_⟩
  · by_contra hq
    exact hs (isZero_upperStar_homology_rightDerivedLowerShriek_singleFunctor aY f G s e q
      fun _ ↦ ⟨he.le, by lia⟩)
  · exact Scheme.Hom.topologicalKrullDim_closure_singleton_add_le aY f
      (isClosed_sheafSupport G) y e he.ge

open _root_.DerivedCategory in
/-- **Artin–Gabber**, support side, in the form proved here: for a compactifiable morphism
`f : X ⟶ Y` of finite type to a scheme of finite type over a field, whose fibres have dimension
at most `d`, and a bounded constructible `K` with `K[n]` satisfying the support condition,
`(Rf_! K)[n + d]` satisfies the support condition. Affineness of `f` is not needed. A point `y`
with nonzero stalk of `Hᵐ(Rf_! K)` has, by dévissage, a nonzero stalk of `Rᵐ⁻ᵇf_! Hᵇ K` for some
`b`; then `dim {y}⁻ + e ≤ dim supp Hᵇ K ≤ n - b` for some `e ≤ d` with `m - b ≤ 2e`, whence
`dim {y}⁻ ≤ n + d - m`. (blueprint: `lem-per-artin-gabber-affine-curve`) -/
theorem DerivedCategory.supportCondition_shift_rightDerivedLowerShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f] (d : ℕ)
    (hf : ∀ y : Y, topologicalKrullDim (f ⁻¹' {y}) ≤ (d : WithBot ℕ∞)) {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.SupportCondition (K⟦n⟧))
    (hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.SupportCondition (((R(f)_![ModuleCat.{u + 1} Λ]).obj K)⟦n + d⟧) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
  have hN := boundedConstructible_rightDerivedLowerShriek Λ f (f ≫ aY) aY rfl K hK'
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hKc⟩ := hK'
  intro i hi
  rw [DerivedCategory.sheafSupport_homology_shift] at hi ⊢
  have : IsConstructibleSheaf ((homologyFunctor _ (n + d + -i)).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := hN.2 _
  -- the dimension of the closure of a point with nonzero stalk
  have key (y : Y) (hy : y ∉ stalkZeroLocus ((homologyFunctor _ (n + d + -i)).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))) :
      ∃ δ : ℕ, topologicalKrullDim (closure {y} : Set Y) = δ ∧ (δ : ℤ) ≤ i := by
    obtain ⟨Ω, _, _, s, rfl, hs⟩ := exists_not_isZero_upperStar_of_notMem_stalkZeroLocus _ hy
    let Φ := R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((s)^*[ModuleCat.{u + 1} Λ])
    have hΦ : ¬ IsZero ((homologyFunctor _ (n + d + -i)).obj (Φ.obj K)) := fun h ↦
      hs (h.of_iso ((leftDerivedUpperStarHomologyFunctorIso _ s _).app _))
    have : K.IsLE (a + ((b - a + 1).toNat : ℕ) - 1) :=
      TStructure.t.isLE_of_le K b _ (by lia)
    obtain ⟨c, hc⟩ :=
      _root_.DerivedCategory.exists_not_isZero_homology_obj_singleFunctor Φ _ a K ha this _ hΦ
    have : IsConstructibleSheaf ((homologyFunctor _ c).obj K) := hKc c
    obtain ⟨e, hed, hq, hne, hdim⟩ :=
      exists_le_of_not_isZero_upperStar_homology_rightDerivedLowerShriek_singleFunctor aY f d hf
        ((homologyFunctor _ c).obj K) s _ fun h ↦
          hc (h.of_iso ((leftDerivedUpperStarHomologyFunctorIso _ s _).app _).symm)
    -- the support condition for `Hᶜ K`
    have hG := hK (n - c)
    have hnc : n + -(n - c) = c := by ring
    rw [DerivedCategory.sheafSupport_homology_shift, hnc] at hG
    obtain ⟨h₀, h₁⟩ := hG hne
    have hdim' := hdim.trans h₁
    have : Nonempty (closure {s.base (IsLocalRing.closedPoint Ω)} : Set Y) :=
      ⟨⟨_, subset_closure rfl⟩⟩
    obtain ⟨δ, -, hδ⟩ := exists_topologicalKrullDim_eq_natCast (N := (n - c).toNat)
      ((le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le e)).trans hdim')
    rw [hδ] at hdim'
    have : δ + e ≤ (n - c).toNat := by exact_mod_cast hdim'
    exact ⟨δ, hδ, by lia⟩
  obtain ⟨y, hy⟩ := (sheafSupport_nonempty_iff _).1 hi
  obtain ⟨δ, -, hδi⟩ := key y hy
  refine ⟨by lia, topologicalKrullDim_sheafSupport_le _ _ fun y hy ↦ ?_⟩
  obtain ⟨δ, hδ, hδi⟩ := key y hy
  rw [hδ]
  exact_mod_cast (by lia : δ ≤ i.toNat)

open _root_.DerivedCategory in
/-- The support estimate for the ordinary direct image `Rf_*` along a morphism of finite type
between schemes of finite type over a field, reduced by dévissage to its pointwise form for a
constructible sheaf `G` (Stacks `0F0X`): if every geometric point `s` over `y ∈ Y` with
`s^* Rᵠf_* G ≠ 0` has `q ≤ N` and `dim {y}⁻ ≤ N - q` whenever `dim supp G ≤ N`, then for a
bounded constructible `K` with `K[n]` satisfying the support condition, `(Rf_* K)[n + d]`
satisfies it, for every `d ≥ 0`. (blueprint: `lem-per-artin-gabber-affine-curve`, Step 3) -/
theorem DerivedCategory.supportCondition_shift_rightDerivedLowerStar_of_stalk {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hP : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
      {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) (q : ℤ),
      ¬ IsZero (((s)^*[ModuleCat.{u + 1} Λ]).obj
        ((homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((singleFunctor _ 0).obj G)))) →
      (sheafSupport G).Nonempty ∧ ∀ N : ℕ, topologicalKrullDim (sheafSupport G) ≤ (N : ℕ∞) →
        q ≤ N ∧ topologicalKrullDim (closure {s.base (IsLocalRing.closedPoint Ω)} : Set Y) ≤
          ((N - q).toNat : ℕ∞))
    (d : ℕ) {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.SupportCondition (K⟦n⟧))
    (hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.SupportCondition (((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)⟦n + d⟧) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
  have hN := boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ f
    (f ≫ aY) aY rfl K hK'
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hKc⟩ := hK'
  intro i hi
  rw [DerivedCategory.sheafSupport_homology_shift] at hi ⊢
  have : IsConstructibleSheaf ((homologyFunctor _ (n + d + -i)).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := hN.2 _
  -- the dimension of the closure of a point with nonzero stalk
  have key (y : Y) (hy : y ∉ stalkZeroLocus ((homologyFunctor _ (n + d + -i)).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K))) :
      0 ≤ i ∧ topologicalKrullDim (closure {y} : Set Y) ≤ (i.toNat : ℕ∞) := by
    obtain ⟨Ω, _, _, s, rfl, hs⟩ := exists_not_isZero_upperStar_of_notMem_stalkZeroLocus _ hy
    let Φ := R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((s)^*[ModuleCat.{u + 1} Λ])
    have hΦ : ¬ IsZero ((homologyFunctor _ (n + d + -i)).obj (Φ.obj K)) := fun h ↦
      hs (h.of_iso ((leftDerivedUpperStarHomologyFunctorIso _ s _).app _))
    have : K.IsLE (a + ((b - a + 1).toNat : ℕ) - 1) :=
      TStructure.t.isLE_of_le K b _ (by lia)
    obtain ⟨c, hc⟩ :=
      _root_.DerivedCategory.exists_not_isZero_homology_obj_singleFunctor Φ _ a K ha this _ hΦ
    have : IsConstructibleSheaf ((homologyFunctor _ c).obj K) := hKc c
    obtain ⟨hne, hdim⟩ := hP ((homologyFunctor _ c).obj K) s _ fun h ↦
      hc (h.of_iso ((leftDerivedUpperStarHomologyFunctorIso _ s _).app _).symm)
    -- the support condition for `Hᶜ K`
    have hG := hK (n - c)
    have hnc : n + -(n - c) = c := by ring
    rw [DerivedCategory.sheafSupport_homology_shift, hnc] at hG
    obtain ⟨h₀, h₁⟩ := hG hne
    obtain ⟨hq, hδ⟩ := hdim (n - c).toNat h₁
    refine ⟨by lia, hδ.trans ?_⟩
    exact_mod_cast (by lia : ((((n - c).toNat : ℕ) : ℤ) - (n + d + -i - c)).toNat ≤ i.toNat)
  obtain ⟨y, hy⟩ := (sheafSupport_nonempty_iff _).1 hi
  exact ⟨(key y hy).1, topologicalKrullDim_sheafSupport_le _ _ fun y hy ↦ (key y hy).2⟩

end AlgebraicGeometry.Etale
