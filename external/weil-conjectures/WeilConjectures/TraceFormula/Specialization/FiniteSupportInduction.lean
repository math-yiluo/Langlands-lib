/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.FiniteSupportDiagonal
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.Topology.Sober
public import WeilConjectures.TraceFormula.OpenClosedTriangle
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.ConstructibleGeneration

/-!

# Finite direct image is conservative

Let `f : Z ⟶ B` be a finite morphism of separated `k`-schemes of finite type. If a bounded
constructible `ℚ̄_ℓ`-complex `F` on `Z` satisfies `Rf_* F = 0`, then `F = 0`
(`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_of_isFinite`).

The proof is a noetherian induction on the open `O ⊆ B` over which `F` is known to vanish. If
`F|_{f⁻¹ O} = 0` and `S = B ∖ O` is non-empty, give `S` its reduced structure; then `F` is the
pushforward of its restriction `G` to `f⁻¹ S`, and `Rf_{S*} G = 0` since the pushforward along the
closed immersion `S ⟶ B` is fully faithful. Above a generic point `ξ` of `S` the fibre of
`f⁻¹ S ×_S f⁻¹ S` is finite and discrete, so the diagonal has open image above an open
neighbourhood `V` of `ξ` in `S` (`AlgebraicGeometry.exists_isOpen_range_diagonal_inter_preimage`),
and `G` vanishes above `V` (`isZero_upperStar_opensOverι_of_isOpen_range_diagonal`). Hence `F`
vanishes over a strictly larger open `O ∪ V'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated TopologicalSpace

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- **The diagonal of a finite morphism is generically open**: let `g : Z ⟶ S` be finite with
`Z ×_S Z` noetherian and `ξ` a point of `S` without proper generalization. Then above an open
neighbourhood of `ξ` the image of the diagonal `Z ⟶ Z ×_S Z` is open. Indeed the points of the
closure of the complement of the diagonal are specializations of points of the complement, and
the fibre above `ξ` is discrete, so no point of the diagonal above `ξ` lies in this closure. -/
theorem exists_isOpen_range_diagonal_inter_preimage {Z S : Scheme.{u}} (g : Z ⟶ S) [IsFinite g]
    [NoetherianSpace (pullback g g : Scheme.{u})] (ξ : S) (hξ : ∀ y, y ⤳ ξ → y = ξ) :
    ∃ V : S.Opens, ξ ∈ V ∧ IsOpen (Set.range (pullback.diagonal g).base ∩
      (pullback.fst g g ≫ g).base ⁻¹' V) := by
  set h := pullback.fst g g ≫ g
  set R := Set.range (pullback.diagonal g).base
  have hR : IsClosed R := (pullback.diagonal g).isClosedEmbedding.isClosed_range
  set T := h.base '' (R ∩ closure Rᶜ)
  have hT : IsClosed T := h.isClosedMap _ (hR.inter isClosed_closure)
  refine ⟨⟨Tᶜ, hT.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨w, ⟨hwR, hwN⟩, hw⟩
    obtain ⟨u, hu, huw⟩ := NoetherianSpace.exists_specializes_of_mem_closure hR.isOpen_compl hwN
    have hu' : h u = ξ := hξ _ (hw ▸ huw.map h.base.hom.continuous)
    obtain ⟨O, hO, hOw⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1
      (h.isDiscrete_preimage_singleton ξ) w hw
    have huO : u ∈ O ∩ h ⁻¹' {ξ} := ⟨huw.mem_open hO (hOw.symm.subset rfl).1, hu'⟩
    rw [hOw, Set.mem_singleton_iff] at huO
    exact hu (huO ▸ hwR)
  · have : R ∩ h.base ⁻¹' Tᶜ = (closure Rᶜ)ᶜ ∩ h.base ⁻¹' Tᶜ := by
      ext x
      refine ⟨fun ⟨hxR, hxT⟩ ↦ ⟨fun hxN ↦ hxT ⟨x, ⟨hxR, hxN⟩, rfl⟩, hxT⟩,
        fun ⟨hxN, hxT⟩ ↦ ⟨?_, hxT⟩⟩
      by_contra hxR
      exact hxN (subset_closure hxR)
    refine this ▸ isClosed_closure.isOpen_compl.inter (hT.isOpen_compl.preimage ?_)
    exact h.base.hom.continuous

namespace ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-! ### Closed subschemes and their preimages -/

section Closed

variable {B : Over (Spec (.of k))} (S : Closeds B.left)

/-- The closed subset `S` of `B` with its reduced structure, as a scheme over `s`. -/
noncomputable abbrev closedOver : Over (Spec (.of k)) :=
  Over.mk ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom)

/-- The closed immersion `S ⟶ B`. -/
noncomputable abbrev closedOverι : closedOver S ⟶ B :=
  Over.homMk (IdealSheafData.vanishingIdeal S).subschemeι

instance : IsClosedImmersion (closedOverι S).left :=
  inferInstanceAs (IsClosedImmersion (IdealSheafData.vanishingIdeal S).subschemeι)

instance [LocallyOfFiniteType B.hom] : LocallyOfFiniteType (closedOver S).hom :=
  inferInstanceAs (LocallyOfFiniteType ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom))

instance [QuasiCompact B.hom] : QuasiCompact (closedOver S).hom :=
  inferInstanceAs (QuasiCompact ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom))

instance [IsSeparated B.hom] : IsSeparated (closedOver S).hom :=
  inferInstanceAs (IsSeparated ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom))

lemma range_closedOverι : Set.range (closedOverι S).left.base = S := by
  change Set.range (IdealSheafData.vanishingIdeal S).subschemeι = _
  rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]

variable {Z : Over (Spec (.of k))} (f : Z ⟶ B)

/-- The preimage `f⁻¹ S = Z ×_B S` of the closed subscheme `S`, as a scheme over `s`. -/
noncomputable abbrev preimageOver : Over (Spec (.of k)) :=
  Over.mk (pullback.snd f.left (closedOverι S).left ≫ (closedOver S).hom)

/-- The closed immersion `f⁻¹ S ⟶ Z`. -/
noncomputable abbrev preimageOverι : preimageOver S f ⟶ Z :=
  Over.homMk (pullback.fst f.left (closedOverι S).left) (by
    simp only [Over.mk_left, Over.mk_hom, ← Over.w f, pullback.condition_assoc]
    rfl)

/-- The restriction `f⁻¹ S ⟶ S` of `f`. -/
noncomputable abbrev preimageOverMap : preimageOver S f ⟶ closedOver S :=
  Over.homMk (pullback.snd f.left (closedOverι S).left)

lemma preimageOverι_comp : preimageOverι S f ≫ f = preimageOverMap S f ≫ closedOverι S := by
  ext1
  exact pullback.condition

instance : IsClosedImmersion (preimageOverι S f).left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst f.left (closedOverι S).left))

instance [IsFinite f.left] : IsFinite (preimageOverMap S f).left :=
  inferInstanceAs (IsFinite (pullback.snd f.left (closedOverι S).left))

instance [IsFinite f.left] [LocallyOfFiniteType B.hom] :
    LocallyOfFiniteType (preimageOver S f).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left (closedOverι S).left ≫
    (closedOver S).hom))

instance [IsFinite f.left] [QuasiCompact B.hom] : QuasiCompact (preimageOver S f).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd f.left (closedOverι S).left ≫ (closedOver S).hom))

instance [IsFinite f.left] [IsSeparated B.hom] : IsSeparated (preimageOver S f).hom :=
  inferInstanceAs (IsSeparated (pullback.snd f.left (closedOverι S).left ≫ (closedOver S).hom))

lemma range_preimageOverι : Set.range (preimageOverι S f).left.base = f.left.base ⁻¹' S := by
  change Set.range (pullback.fst f.left (closedOverι S).left) = _
  rw [Scheme.Pullback.range_fst, ← range_closedOverι S]

end Closed

/-! ### Detection and the induction -/

section Induction

/-- A morphism over `s` from a scheme of finite type to a separated scheme is quasi-compact. -/
lemma quasiCompact_left {Y X : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (g : Y ⟶ X) : QuasiCompact g.left := by
  have := isNoetherian_left Y
  infer_instance

/-- The pair `(Y₁, Y₂)` as a family indexed by `Bool`. -/
noncomputable def pairOver (Y₁ Y₂ : Over (Spec (.of k))) : Bool → Over (Spec (.of k))
  | true => Y₁
  | false => Y₂

instance {Y₁ Y₂ : Over (Spec (.of k))} [LocallyOfFiniteType Y₁.hom] [LocallyOfFiniteType Y₂.hom]
    (b : Bool) : LocallyOfFiniteType (pairOver Y₁ Y₂ b).hom := by
  cases b <;> assumption

instance {Y₁ Y₂ : Over (Spec (.of k))} [QuasiCompact Y₁.hom] [QuasiCompact Y₂.hom] (b : Bool) :
    QuasiCompact (pairOver Y₁ Y₂ b).hom := by
  cases b <;> assumption

instance {Y₁ Y₂ : Over (Spec (.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] (b : Bool) :
    IsSeparated (pairOver Y₁ Y₂ b).hom := by
  cases b <;> assumption

/-- The pair of morphisms `(g₁, g₂)` as a family indexed by `Bool`. -/
noncomputable def pairHom {X Y₁ Y₂ : Over (Spec (.of k))} (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) :
    ∀ b, pairOver Y₁ Y₂ b ⟶ X
  | true => g₁
  | false => g₂

instance {X Y₁ Y₂ : Over (Spec (.of k))} [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom]
    [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (b : Bool) :
    QuasiCompact (pairHom g₁ g₂ b).left :=
  quasiCompact_left _

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable (ℓ) in
/-- **Detection along two morphisms**: a bounded constructible complex whose pullbacks along two
morphisms jointly covering `X` vanish is zero. -/
lemma isZero_of_isZero_upperStar_of_cover₂ {X Y₁ Y₂ : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
    [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
    (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X)
    (hg : ∀ x, x ∈ Set.range g₁.left.base ∨ x ∈ Set.range g₂.left.base)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h₁ : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₁).obj K))
    (h₂ : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₂).obj K)) :
    IsZero K := by
  have hiso := isIso_of_forall_isIso_boundedConstructibleUpperStar_map
    (Profinite.padicAlgClRingObj ℓ) ℓ (pairHom g₁ g₂)
    (fun x ↦ (hg x).elim (fun h ↦ ⟨true, h⟩) (fun h ↦ ⟨false, h⟩)) (0 : K ⟶ K) (fun b ↦ by
        cases b
        · exact ⟨⟨h₂.to_ _, h₂.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
        · exact ⟨⟨h₁.to_ _, h₁.eq_of_src _ _, h₁.eq_of_src _ _⟩⟩)
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← IsIso.hom_inv_id (0 : K ⟶ K), zero_comp]

/-- The closed complement of an open subset. -/
abbrev complClosed {X : Scheme.{u}} (O : X.Opens) : Closeds X :=
  ⟨(O : Set X)ᶜ, O.isOpen.isClosed_compl⟩

variable {Z B : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  (f : Z ⟶ B) [IsFinite f.left]

/-- If `F` vanishes over the open `O`, then `F` is the pushforward of its restriction `G` to the
preimage of the closed complement `S` of `O`, and `Rf_* F = 0` implies `Rf_{S*} G = 0`, the
pushforward along the closed immersion `S ⟶ B` being fully faithful. -/
theorem isZero_lowerStar_preimageOverMap (O : B.left.Opens)
    (F : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hFO : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (f.left ⁻¹ᵁ O))).obj F))
    (hF : IsZero ((boundedConstructibleLowerStar ℓ f).obj F)) :
    IsZero ((boundedConstructibleLowerStar ℓ
      (preimageOverMap (complClosed O) f)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (preimageOverι (complClosed O) f)).obj F)) := by
  have hcompl : IsCompl (Set.range (opensOverι (f.left ⁻¹ᵁ O)).left.base)
      (Set.range (preimageOverι (complClosed O) f).left.base) := by
    rw [range_opensOverι, range_preimageOverι]
    exact isCompl_compl.preimage _
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed_boundedConstructible ℓ hcompl F
  have h₁ : IsZero ((boundedConstructibleLowerShriek ℓ
      (opensOverι (f.left ⁻¹ᵁ O))).obj ((boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (f.left ⁻¹ᵁ O))).obj F)) :=
    Functor.map_isZero _ hFO
  have hunit : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (preimageOverι (complClosed O) f)).unit.app F) :=
    (Triangle.isZero₁_iff_isIso₂ _ hδ).1 h₁
  have key (q : preimageOver (complClosed O) f ⟶ B) (hq : preimageOverι (complClosed O) f ≫ f = q)
      (h : IsZero ((boundedConstructibleLowerStar ℓ
        (preimageOverι (complClosed O) f ≫ f)).obj ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ (preimageOverι (complClosed O) f)).obj F))) :
      IsZero ((boundedConstructibleLowerStar ℓ q).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (preimageOverι (complClosed O) f)).obj F)) := by
    subst hq
    exact h
  have hS := (key _ (preimageOverι_comp (complClosed O) f)
    ((hF.of_iso ((boundedConstructibleLowerStar ℓ f).mapIso
      (asIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (preimageOverι (complClosed O) f)).unit.app F))).symm).of_iso
      ((boundedConstructibleLowerStarComp ℓ _ _).app _).symm)).of_iso
      ((boundedConstructibleLowerStarComp ℓ (preimageOverMap (complClosed O) f)
        (closedOverι (complClosed O))).app _)
  exact ((boundedConstructibleUpperStar _ ℓ (closedOverι (complClosed O))).map_isZero hS).of_iso
    (asIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (closedOverι (complClosed O))).counit.app _)).symm


omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- A point lies in the range of `opensOverLift W g h` if and only if its image in `X` lies in
the range of `g`. -/
lemma mem_range_opensOverLift {X Y : Over (Spec (.of k))} (W : X.left.Opens) (g : Y ⟶ X)
    (h : Set.range g.left.base ⊆ W) (x : (opensOver W).left) :
    x ∈ Set.range (opensOverLift W g h).left.base ↔
      (opensOverι W).left.base x ∈ Set.range g.left.base := by
  have hg (y : Y.left) : (opensOverι W).left.base ((opensOverLift W g h).left.base y) =
      g.left.base y := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, opensOverLift_ι]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (hg y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (opensOverι W).left.isOpenEmbedding.injective ((hg y).trans hy)⟩

/-- **The induction step**: if `F` vanishes over the open `O ⊊ B` and `Rf_* F = 0`, then `F`
vanishes over a strictly larger open. -/
theorem exists_gt_isZero_upperStar_of_isZero_lowerStar (O : B.left.Opens)
    (hO : (O : Set B.left) ≠ Set.univ) (F : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hFO : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (f.left ⁻¹ᵁ O))).obj F))
    (hF : IsZero ((boundedConstructibleLowerStar ℓ f).obj F)) :
    ∃ O' : B.left.Opens, O < O' ∧ IsZero ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (f.left ⁻¹ᵁ O'))).obj F) := by
  have hG := isZero_lowerStar_preimageOverMap f O F hFO hF
  -- a generic point `ξ` of `S = B ∖ O`
  have hne : Nonempty (closedOver (complClosed O)).left := by
    obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem _).1 hO
    have hb' : b ∈ ((complClosed O : Closeds B.left) : Set B.left) := hb
    rw [← range_closedOverι] at hb'
    exact ⟨hb'.choose⟩
  let ξ : (closedOver (complClosed O)).left := (genericPoints.ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents hne.some⟩).1
  have hξ : ∀ y, y ⤳ ξ → y = ξ :=
    mem_genericPoints_iff_forall_specializes.1 (genericPoints.ofComponent _).2
  -- the diagonal is open above a neighbourhood `V` of `ξ`
  have : IsNoetherian (pullback (preimageOverMap (complClosed O) f).left
      (preimageOverMap (complClosed O) f).left) :=
    isNoetherian_left (fibreSquare (preimageOverMap (complClosed O) f))
  obtain ⟨V, hξV, hV⟩ := exists_isOpen_range_diagonal_inter_preimage
    (preimageOverMap (complClosed O) f).left ξ hξ
  have hGV := isZero_upperStar_opensOverι_of_isOpen_range_diagonal
    (preimageOverMap (complClosed O) f) _ hG V hV
  -- extend `V` to an open `V'` of `B`
  obtain ⟨t, ht, htV⟩ :=
    (closedOverι (complClosed O)).left.isClosedEmbedding.isInducing.isOpen_iff.1 V.isOpen
  have hξS : (closedOverι (complClosed O)).left.base ξ ∉ O := by
    have : (closedOverι (complClosed O)).left.base ξ ∈
        ((complClosed O : Closeds B.left) : Set B.left) := by
      rw [← range_closedOverι]
      exact ⟨ξ, rfl⟩
    exact this
  have hξt : (closedOverι (complClosed O)).left.base ξ ∈ t := by
    have : ξ ∈ (closedOverι (complClosed O)).left.base ⁻¹' t := htV.symm ▸ hξV
    exact this
  refine ⟨O ⊔ ⟨t, ht⟩, lt_of_le_of_ne le_sup_left fun hOt ↦ hξS ?_, ?_⟩
  · exact (le_of_eq hOt.symm : O ⊔ ⟨t, ht⟩ ≤ O) (Or.inr hξt)
  -- `F` vanishes over `O ∪ V'`
  have ha : Set.range (opensOverι (f.left ⁻¹ᵁ O)).left.base ⊆ f.left ⁻¹ᵁ (O ⊔ ⟨t, ht⟩) := by
    rw [range_opensOverι]
    exact fun z hz ↦ Or.inl hz
  have hcomm (w : (preimageOver (complClosed O) f).left) :
      f.left.base ((preimageOverι (complClosed O) f).left.base w) =
        (closedOverι (complClosed O)).left.base
          ((preimageOverMap (complClosed O) f).left.base w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
      preimageOverι_comp]
  have hb : Set.range (opensOverι ((preimageOverMap (complClosed O) f).left ⁻¹ᵁ V) ≫
      preimageOverι (complClosed O) f).left.base ⊆ f.left ⁻¹ᵁ (O ⊔ ⟨t, ht⟩) := by
    rintro _ ⟨y, rfl⟩
    refine Or.inr ?_
    change f.left.base ((preimageOverι (complClosed O) f).left.base
      ((opensOverι ((preimageOverMap (complClosed O) f).left ⁻¹ᵁ V)).left.base y)) ∈ t
    rw [hcomm]
    have hy : (opensOverι ((preimageOverMap (complClosed O) f).left ⁻¹ᵁ V)).left.base y ∈
        ((preimageOverMap (complClosed O) f).left ⁻¹ᵁ V : Set _) := by
      rw [← range_opensOverι]
      exact ⟨y, rfl⟩
    have hy' : (preimageOverMap (complClosed O) f).left.base
        ((opensOverι ((preimageOverMap (complClosed O) f).left ⁻¹ᵁ V)).left.base y) ∈
          (closedOverι (complClosed O)).left.base ⁻¹' t := htV.symm ▸ hy
    exact hy'
  refine isZero_of_isZero_upperStar_of_cover₂ ℓ (opensOverLift _ _ ha) (opensOverLift _ _ hb)
    (fun x ↦ ?_) _ (isZero_upperStar_obj_upperStar_obj _ ℓ _ _ F (by rwa [opensOverLift_ι]))
    (isZero_upperStar_obj_upperStar_obj _ ℓ _ _ F (by
      rw [opensOverLift_ι]
      exact hGV.of_iso ((boundedConstructibleUpperStarComp _ ℓ _ _).app F)))
  rw [mem_range_opensOverLift, mem_range_opensOverLift]
  set z := (opensOverι (f.left ⁻¹ᵁ (O ⊔ ⟨t, ht⟩))).left.base x
  have hz : f.left.base z ∈ O ⊔ ⟨t, ht⟩ := by
    have : z ∈ (f.left ⁻¹ᵁ (O ⊔ ⟨t, ht⟩) : Set Z.left) := by
      rw [← range_opensOverι]
      exact ⟨x, rfl⟩
    exact this
  by_cases hzO : f.left.base z ∈ O
  · left
    rw [range_opensOverι]
    exact hzO
  · right
    have hzS : z ∈ Set.range (preimageOverι (complClosed O) f).left.base := by
      rw [range_preimageOverι]
      exact hzO
    obtain ⟨w, hw⟩ := hzS
    have hwV : w ∈ Set.range
        (opensOverι ((preimageOverMap (complClosed O) f).left ⁻¹ᵁ V)).left.base := by
      rw [range_opensOverι]
      change (preimageOverMap (complClosed O) f).left.base w ∈ (V : Set _)
      rw [← htV]
      change (closedOverι (complClosed O)).left.base
        ((preimageOverMap (complClosed O) f).left.base w) ∈ t
      rw [← hcomm, hw]
      exact hz.resolve_left hzO
    obtain ⟨v, rfl⟩ := hwV
    exact ⟨v, hw⟩

/-- **Finite direct image is conservative**: for a finite morphism `f : Z ⟶ B` of separated
`k`-schemes of finite type, a bounded constructible `ℚ̄_ℓ`-complex `F` on `Z` with `Rf_* F = 0`
vanishes. This is a noetherian induction on the open of `B` over which `F` vanishes, by
`exists_gt_isZero_upperStar_of_isZero_lowerStar`. -/
theorem isZero_of_isZero_lowerStar_of_isFinite (F : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hF : IsZero ((boundedConstructibleLowerStar ℓ f).obj F)) :
    IsZero F := by
  have := isNoetherian_left B
  have hbot : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (f.left ⁻¹ᵁ ⊥))).obj F) := by
    have : IsEmpty (opensOver (f.left ⁻¹ᵁ ⊥)).left := ⟨fun x ↦ by
      have hx : (opensOverι (f.left ⁻¹ᵁ ⊥)).left.base x ∈ (f.left ⁻¹ᵁ ⊥ : Set Z.left) := by
        rw [← range_opensOverι]
        exact ⟨x, rfl⟩
      exact hx⟩
    exact isZero_boundedConstructible_of_isEmpty ℓ _
  suffices H : ∀ O : B.left.Opens, IsZero ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (f.left ⁻¹ᵁ O))).obj F) → IsZero F from
    H ⊥ hbot
  intro O
  induction O using WellFoundedGT.induction with
  | ind O ih =>
    intro hFO
    by_cases hO : (O : Set B.left) = Set.univ
    · refine isZero_of_isZero_upperStar_of_cover₂ ℓ (opensOverι (f.left ⁻¹ᵁ O))
        (opensOverι (f.left ⁻¹ᵁ O)) (fun x ↦ Or.inl ?_) F hFO hFO
      rw [range_opensOverι]
      change f.left.base x ∈ (O : Set B.left)
      rw [hO]
      trivial
    · obtain ⟨O', hlt, hO'⟩ := exists_gt_isZero_upperStar_of_isZero_lowerStar f O hO F hFO hF
      exact ih O' hlt hO'

end Induction

end ProEtale.CondensedRing

end AlgebraicGeometry
