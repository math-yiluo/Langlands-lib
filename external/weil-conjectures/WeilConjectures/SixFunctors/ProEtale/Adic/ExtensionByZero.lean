/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Extension by zero of constructible `ℓ`-adic sheaves

Let `j : U ⟶ X` be a quasi-compact open immersion. We show that the extension by zero
`j_! F` of a constructible `ℓ`-adic sheaf `F` on the small pro-étale site of `U` is
constructible. Near a point `x` of `X`, choose an affine open neighbourhood `V`. Then `U ∩ V`
is quasi-compact, so `F` is stratified lisse on `U ∩ V`. The restriction of `j_! F` to
`U ∩ V` is `F`, and its restriction to the closed complement of `U ∩ V` in `V` vanishes.
Together these stratify `V`.

## Main results

- `AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf.of_partition`: stratifications glue
  along a finite partition into locally closed pieces.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isAdicStratifiedLisseSheaf`: on a
  quasi-compact scheme a constructible sheaf is stratified lisse.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.openImmersionLowerShriek`: the
  extension by zero along a quasi-compact open immersion preserves constructibility.

Quasi-compactness of `j` cannot be dropped. Near a point of `X` outside `U`, the open `U`
may meet infinitely many disjoint opens on which `F` needs more and more strata. Then `j_! F`
has no finite stratification near that point.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- **Stratifications glue along a finite partition.** If the ranges of finitely many
immersions `i_k : Z_k ⟶ X` partition `X`, each `i_k` maps constructible subsets of `Z_k` to
constructible subsets of `X`, and each `i_k^* F` is stratified lisse, then so is `F`. The strata
of the `Z_k`, composed with the `i_k`, stratify `X`. -/
theorem IsAdicStratifiedLisseSheaf.of_partition {ι : Type} [Finite ι] {Z : ι → Scheme.{u}}
    (i : (k : ι) → Z k ⟶ X) (hi : ∀ k, IsImmersion (i k))
    (hc : ∀ k (T : Set (Z k)), Topology.IsConstructible T →
      Topology.IsConstructible ((i k).base '' T))
    (hcover : ∀ x : X, ∃! k, x ∈ Set.range (i k).base)
    {F : AdicSheaf l X}
    (h : ∀ k, IsAdicStratifiedLisseSheaf ((i k)^*ᵃ[l].obj F)) :
    IsAdicStratifiedLisseSheaf F := by
  choose κ hκ Z' i' hi' hc' hcover' h' using h
  have : ∀ k, Finite (κ k) := hκ
  refine ⟨Σ k, κ k, inferInstance, fun p ↦ Z' p.1 p.2, fun p ↦ i' p.1 p.2 ≫ i p.1,
    fun p ↦ ?_, fun p ↦ ?_, fun x ↦ ?_, fun p ↦ ?_⟩
  · have := hi p.1
    have := hi' p.1 p.2
    infer_instance
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact hc p.1 _ (hc' p.1 p.2)
  · obtain ⟨k, ⟨z, rfl⟩, hk⟩ := hcover x
    obtain ⟨m, ⟨w, rfl⟩, hm⟩ := hcover' k z
    refine ⟨⟨k, m⟩, ⟨w, rfl⟩, ?_⟩
    rintro ⟨k', m'⟩ ⟨w', hw'⟩
    obtain rfl : k' = k := hk k' ⟨_, hw'⟩
    have := hi k'
    obtain rfl : m' = m := hm m' ⟨w', (i k').isEmbedding.injective hw'⟩
    rfl
  · exact (h' p.1 p.2).of_iso ((adicUpperStarComp l _ _).app F).symm

/-- A quasi-compact open immersion and a closed immersion with complementary ranges stratify:
if both `i₁^* F` and `i₂^* F` are stratified lisse, then so is `F`. Both ranges are
constructible, the range of `i₁` being a retrocompact open. -/
theorem IsAdicStratifiedLisseSheaf.of_isCompl {Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X)
    (i₂ : Z₂ ⟶ X) [IsOpenImmersion i₁] [QuasiCompact i₁] [IsClosedImmersion i₂]
    (h : IsCompl (Set.range i₁.base) (Set.range i₂.base))
    {F : AdicSheaf l X}
    (h₁ : IsAdicStratifiedLisseSheaf ((i₁)^*ᵃ[l].obj F))
    (h₂ : IsAdicStratifiedLisseSheaf ((i₂)^*ᵃ[l].obj F)) :
    IsAdicStratifiedLisseSheaf F := by
  refine of_partition (ι := Bool) (Z := fun b ↦ bif b then Z₁ else Z₂)
    (fun b ↦ match b with | true => i₁ | false => i₂) (by rintro (_ | _) <;> infer_instance)
    ?_ (fun x ↦ ?_) (by rintro (_ | _) <;> assumption)
  · rintro (_ | _) T hT
    · refine hT.image_of_isClosedEmbedding i₂.isClosedEmbedding ?_
      change IsRetrocompact (Set.range i₂.base)ᶜ
      rw [← h.compl_eq, compl_compl]
      exact i₁.isRetrocompact_range
    · exact hT.image_of_isOpenEmbedding i₁.isOpenEmbedding i₁.isRetrocompact_range
  by_cases hx : x ∈ Set.range i₁.base
  · refine ⟨true, hx, fun b hb ↦ ?_⟩
    cases b
    · exact absurd hx (Set.disjoint_right.1 h.disjoint hb)
    · rfl
  · refine ⟨false, show x ∈ Set.range i₂.base from h.compl_eq ▸ hx, fun b hb ↦ ?_⟩
    cases b
    · rfl
    · exact absurd hb hx

/-- A constructible sheaf is stratified lisse on an affine open neighbourhood of each point:
shrink the open neighbourhood of the definition to an affine one. -/
theorem IsAdicConstructibleSheaf.exists_isAffineOpen
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      IsAdicStratifiedLisseSheaf ((V.ι)^*ᵃ[l].obj F) := by
  obtain ⟨W, j, hj, hxW, h⟩ := hF x
  obtain ⟨V, hV, hxV, hVle⟩ : ∃ V : X.Opens, V ∈ X.affineOpens ∧ x ∈ V ∧ V ≤ j.opensRange :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ j.opensRange from hxW)
  have hle : Set.range V.ι.base ⊆ Set.range j.base := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact hVle
  let g := IsOpenImmersion.lift j V.ι hle
  exact ⟨V, hV, hxV, (h.upperStar g).of_iso (((adicUpperStarComp l g j).app F).symm ≪≫
    (adicUpperStarCongr l (IsOpenImmersion.lift_fac j V.ι hle)).app F)⟩

/-- **On a quasi-compact quasi-separated scheme a constructible sheaf is stratified lisse.**
Finitely many affine open neighbourhoods `V_a` on which `F` is stratified lisse cover `X`. The
pieces `V_a ∖ ⋃_{b < a} V_b`, closed in `V_a`, partition `X`; they are constructible, the
quasi-compact opens of the quasi-separated `X` being retrocompact, and on each of them `F` is
stratified lisse. -/
theorem IsAdicConstructibleSheaf.isAdicStratifiedLisseSheaf [CompactSpace X]
    [QuasiSeparatedSpace X] {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) : IsAdicStratifiedLisseSheaf F := by
  choose V hV hx h using hF.exists_isAffineOpen
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  let p : Fin t.card → X := fun a ↦ (t.equivFin.symm a).1
  have hp : ∀ x : X, ∃ a, x ∈ V (p a) := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    rwa [show p (t.equivFin ⟨y, hy⟩) = y by simp [p]]
  -- The open union of the earlier neighbourhoods, pulled back to `V (p a)`, and its closed
  -- complement `C a`.
  let B : Fin t.card → X.Opens := fun a ↦ ⨆ b : {b // b < a}, V (p b)
  have hB : ∀ a, IsCompact (B a : Set X) := fun a ↦ by
    simp only [B, TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun b ↦ (hV (p b)).isCompact
  let C : (a : Fin t.card) → Closeds (V (p a)) := fun a ↦
    ⟨((V (p a)).ι ⁻¹ᵁ B a : Set (V (p a)))ᶜ, ((V (p a)).ι ⁻¹ᵁ B a).isOpen.isClosed_compl⟩
  let s : (a : Fin t.card) → (Scheme.IdealSheafData.vanishingIdeal (C a)).subscheme ⟶ X :=
    fun a ↦ (Scheme.IdealSheafData.vanishingIdeal (C a)).subschemeι ≫ (V (p a)).ι
  have hs : ∀ a x, x ∈ Set.range (s a).base ↔
      x ∈ V (p a) ∧ ∀ b < a, x ∉ V (p b) := by
    intro a x
    have hB : ∀ w, (V (p a)).ι w ∈ B a ↔ ∃ b < a, (V (p a)).ι w ∈ V (p b) := by
      intro w
      simp only [B, Opens.mem_iSup, Subtype.exists]
      exact ⟨fun ⟨b, hb, h⟩ ↦ ⟨b, hb, h⟩, fun ⟨b, hb, h⟩ ↦ ⟨b, hb, h⟩⟩
    constructor
    · rintro ⟨c, rfl⟩
      have hc : (Scheme.IdealSheafData.vanishingIdeal (C a)).subschemeι c ∈ (C a : Set _) := by
        rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal,
          ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨c, rfl⟩
      refine ⟨by simp [s], fun b hb hxb ↦ hc ((hB _).2 ⟨b, hb, hxb⟩)⟩
    · rintro ⟨hxa, hw⟩
      obtain ⟨w, rfl⟩ : x ∈ Set.range (V (p a)).ι.base := by rwa [Scheme.Opens.range_ι]
      have hwC : w ∈ (C a : Set _) := fun hwB ↦ by
        obtain ⟨b, hb, hxb⟩ := (hB w).1 hwB
        exact hw b hb hxb
      rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal,
        ← Scheme.IdealSheafData.range_subschemeι] at hwC
      obtain ⟨c, rfl⟩ := hwC
      exact ⟨c, rfl⟩
  refine IsAdicStratifiedLisseSheaf.of_partition s (fun a ↦ inferInstance) (fun a T hT ↦ ?_)
    (fun x ↦ ?_) (fun a ↦ ((h (p a)).upperStar _).of_iso ((adicUpperStarComp l _ _).app F).symm)
  · have : IsAffine (V (p a)) := hV (p a)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
    refine Topology.IsConstructible.image_of_isOpenEmbedding (V (p a)).ι.isOpenEmbedding
      (V (p a)).ι.isRetrocompact_range (hT.image_of_isClosedEmbedding
        (Scheme.IdealSheafData.vanishingIdeal (C a)).subschemeι.isClosedEmbedding ?_)
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change IsRetrocompact ((((V (p a)).ι ⁻¹ᵁ B a : Set (V (p a)))ᶜ)ᶜ)
    rw [compl_compl]
    exact (QuasiCompact.isCompact_preimage (f := (V (p a)).ι) _ (B a).isOpen
      (hB a)).isRetrocompact ((V (p a)).ι ⁻¹ᵁ B a).isOpen
  classical
  obtain ⟨a, ha, hmin⟩ := (Finset.univ.filter fun a ↦ x ∈ V (p a)).exists_min_image
    id (by simpa [Finset.filter_nonempty_iff] using hp x)
  refine ⟨a, (hs a x).2 ⟨(Finset.mem_filter.1 ha).2, fun b hb hxb ↦ ?_⟩, fun a' ha' ↦ ?_⟩
  · exact absurd (hmin b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxb⟩)) (not_le.2 hb)
  · obtain ⟨hxa', ha'⟩ := (hs a' x).1 ha'
    obtain hlt | heq | hgt := lt_trichotomy a' a
    · exact absurd (hmin a' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxa'⟩)) (not_le.2 hlt)
    · exact heq
    · exact absurd (Finset.mem_filter.1 ha).2 (ha' a hgt)

/-- **The extension by zero of a constructible sheaf along a quasi-compact open immersion is
constructible.** Let `V` be an affine open neighbourhood of a point of `X`. Then `U ∩ V` is
quasi-compact, so `F` is stratified lisse there, and the restriction of `j_! F` to `U ∩ V` is
`F`. The restriction of `j_! F` to the closed complement of `U ∩ V` in `V` vanishes. -/
theorem IsAdicConstructibleSheaf.openImmersionLowerShriek {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    {F : AdicSheaf l U}
    (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((j)_!ᵃ[l].obj F) := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ : ∃ V : X.Opens, V ∈ X.affineOpens ∧ x ∈ V ∧ V ≤ ⊤ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨V, V.ι, inferInstance, by simpa using hxV, ?_⟩
  set G := (j)_!ᵃ[l].obj F
  have : IsAffine V := hV
  have : CompactSpace ↥(pullback j V.ι) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd j V.ι)
  have : QuasiSeparatedSpace ↥(pullback j V.ι) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd j V.ι)
  -- The closed complement of `U ∩ V` in `V`.
  let C : Closeds V := ⟨(Set.range (pullback.snd j V.ι).base)ᶜ,
    (pullback.snd j V.ι).isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let s := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hs : Set.range s.base = (C : Set V) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  refine IsAdicStratifiedLisseSheaf.of_isCompl (pullback.snd j V.ι) s
    (by rw [hs]; exact isCompl_compl) ?_ ?_
  · -- On `U ∩ V` the sheaf `j_! F` restricts to `F`.
    have e : F ≅ (j)^*ᵃ[l].obj G :=
      asIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app F)
    exact (hF.upperStar (pullback.fst j V.ι)).isAdicStratifiedLisseSheaf.of_iso
      ((pullback.fst j V.ι)^*ᵃ[l].mapIso e ≪≫ (adicUpperStarCompIso l pullback.condition).app G)
  · -- On the closed complement the sheaf `j_! F` vanishes.
    refine (IsAdicLisseSheaf.of_isZero ?_).isAdicStratifiedLisseSheaf
    refine (isZero_adicUpperStar_adicOpenImmersionLowerShriek j (s ≫ V.ι) ?_ F).of_iso
      ((adicUpperStarComp l _ _).app G).symm
    refine Set.eq_empty_of_forall_notMem fun y ⟨⟨u, hu⟩, ⟨c, hc⟩⟩ ↦ ?_
    obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := V.ι) u (s c)
      (by rw [hu, ← hc]; rfl)
    have hsc : s c ∈ (C : Set V) := hs ▸ ⟨c, rfl⟩
    exact hsc ⟨t, ht⟩

end AlgebraicGeometry.ProEtale
