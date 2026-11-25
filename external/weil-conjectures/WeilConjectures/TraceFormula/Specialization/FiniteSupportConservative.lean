/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.FiniteSupportInduction

/-!

# Direct image is conservative on finite support

Let `q : Y ⟶ B` be a morphism of separated `k`-schemes of finite type and `T ⊆ Y` a closed subset
finite over `B`. A bounded constructible `ℚ̄_ℓ`-complex `E` on `Y` supported on `T` with
`Rq_* E = 0` vanishes
(`ProEtale.CondensedRing.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`). This is the node
`lemma-nearby-cycles-constant-family` of the blueprint subsection
`lemma-nearby-cycles-constant-family`, stated here for `ℚ̄_ℓ`-coefficients as an input of the proof
of blueprint `theorem-verdier-s-theorem-specialization-zero`.

The subset `T`, the image of a morphism `t : T' ⟶ Y` finite over `B`, is closed; give it the
structure of the scheme-theoretic image `u : T₀ ⟶ Y` of `t`.
As `E` vanishes on the open complement (a finite union of the given neighbourhoods), the
open–closed triangle gives `E ≅ Ru_* Lu^* E`, so `R(u ≫ q)_* Lu^* E ≅ Rq_* E = 0`. The morphism
`u ≫ q` is proper with finite fibres, hence finite, and finite direct image is conservative
(`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_of_isFinite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- A complex vanishing after pullback along an open immersion `g` vanishes on every open
subscheme contained in the image of `g`. -/
lemma isZero_upperStar_opensOverι_of_le_opensRange {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (E : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {V : Scheme.{u}} (g : V ⟶ Y.left)
    [IsOpenImmersion g] (hg : IsZero ((L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj E.obj))
    (W : Y.left.Opens) (hW : (W : Set Y.left) ⊆ Set.range g.base) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W)).obj E) := by
  have hr : Set.range W.ι.base ⊆ Set.range g.base := by
    rw [Scheme.Opens.range_ι]
    exact hW
  have key (w : W.toScheme ⟶ Y.left) (hw : IsOpenImmersion.lift g W.ι hr ≫ g = w) :
      IsZero ((L((w)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj E.obj) := by
    subst hw
    exact ((L((IsOpenImmersion.lift g W.ι hr)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_isZero
      hg).of_iso ((leftDerivedUpperStarComp _ _ g).app E.obj)
  exact IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _
    (key _ (IsOpenImmersion.lift_fac _ _ _))

/-- **Direct image is conservative on finite support** (blueprint
`lemma-nearby-cycles-constant-family`, a node of the subsection
`lemma-nearby-cycles-constant-family`, for `ℚ̄_ℓ`-coefficients): let `q : Y ⟶ B` be a morphism of
separated `k`-schemes of finite type and `T ⊆ Y` a closed subset finite over `B`, given as the image
of a morphism `t : T' ⟶ Y` with `T' ⟶ B` finite. If `E` is bounded constructible on `Y` and
supported on `T` (every point outside `T` has an open neighbourhood on which `E` vanishes) and
`Rq_* E = 0`, then `E = 0`. -/
theorem isZero_of_isZero_rightDerivedLowerStar_of_isFinite {Y B : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (q : Y ⟶ B)
    {T : Scheme.{u}} (t : T ⟶ Y.left) [IsFinite (t ≫ q.left)]
    (E : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hE : ∀ y ∉ Set.range t.base, ∃ (V : Scheme.{u}) (g : V ⟶ Y.left), IsOpenImmersion g ∧
      y ∈ Set.range g.base ∧
      IsZero ((L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj E.obj))
    (hq : IsZero ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj E.obj)) :
    IsZero E.obj := by
  -- the image of `t` is closed, with the closed subscheme structure `u : T₀ ⟶ Y` of the image
  have : IsSeparated (q.left ≫ B.hom) := by
    rw [Over.w q]
    infer_instance
  have : IsSeparated q.left := IsSeparated.of_comp q.left B.hom
  have : LocallyOfFiniteType (q.left ≫ B.hom) := by
    rw [Over.w q]
    infer_instance
  have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left B.hom
  have : IsFinite t := MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) t q.left
    ‹_› ‹_›
  have hC : IsClosed (Set.range t.base) := t.isClosedMap.isClosed_range
  have hrange : Set.range t.imageι.base = Set.range t.base := by
    change Set.range t.ker.subschemeι = _
    rw [IdealSheafData.range_subschemeι, Scheme.Hom.support_ker, hC.closure_eq]
  have : Surjective t.toImage := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ : t.imageι.base x ∈ Set.range t.base := hrange ▸ ⟨x, rfl⟩
    refine ⟨y, t.imageι.isClosedEmbedding.injective ?_⟩
    rw [← hy, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]⟩
  let T₀ : Over (Spec (.of k)) := Over.mk (t.imageι ≫ Y.hom)
  let u : T₀ ⟶ Y := Over.homMk t.imageι
  have : IsClosedImmersion u.left := inferInstanceAs (IsClosedImmersion t.imageι)
  have : LocallyOfFiniteType T₀.hom := inferInstanceAs (LocallyOfFiniteType (t.imageι ≫ Y.hom))
  have : QuasiCompact T₀.hom := inferInstanceAs (QuasiCompact (t.imageι ≫ Y.hom))
  have : IsSeparated T₀.hom := inferInstanceAs (IsSeparated (t.imageι ≫ Y.hom))
  -- `u ≫ q` is finite: it is proper with finite fibres
  have hfin : IsFinite (u ≫ q).left := by
    have : UniversallyClosed (t.toImage ≫ t.imageι ≫ q.left) := by
      rw [Scheme.Hom.toImage_imageι_assoc]
      infer_instance
    have : UniversallyClosed (t.imageι ≫ q.left) :=
      UniversallyClosed.of_comp_surjective t.toImage _
    have : IsProper (t.imageι ≫ q.left) := ⟨⟩
    have : LocallyQuasiFinite (t.imageι ≫ q.left) := by
      refine .of_finite_preimage_singleton _ fun b ↦ ?_
      refine (((t ≫ q.left).finite_preimage_singleton b).image t.toImage.base).subset ?_
      intro x hx
      obtain ⟨y, rfl⟩ := t.toImage.surjective x
      refine ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, ← Scheme.Hom.toImage_imageι_assoc t q.left, Scheme.Hom.comp_apply]
      exact hx
    exact IsFinite.of_isProper_of_locallyQuasiFinite (t.imageι ≫ q.left)
  -- `E` vanishes on the complement of the image of `t`
  let U : Y.left.Opens := ⟨(Set.range t.base)ᶜ, hC.isOpen_compl⟩
  have hEU : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι U)).obj E) := by
    have := isNoetherian_left Y
    have hloc (y : Y.left) (hy : y ∈ U) : ∃ W : Y.left.Opens, y ∈ W ∧ W ≤ U ∧
        IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (opensOverι W)).obj E) := by
      obtain ⟨V, g, hg, hyg, hz⟩ := hE y hy
      exact ⟨g.opensRange ⊓ U, ⟨hyg, hy⟩, inf_le_right,
        isZero_upperStar_opensOverι_of_le_opensRange E g hz _ fun z hz ↦ hz.1⟩
    choose W hyW hWU hWz using hloc
    obtain ⟨s, hs⟩ :=
      (TopologicalSpace.NoetherianSpace.isCompact (U : Set Y.left)).elim_finite_subcover
      (fun i : U ↦ (W i.1 i.2 : Set Y.left)) (fun i ↦ (W i.1 i.2).isOpen)
      (fun y hy ↦ Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW y hy⟩)
    have hWU' (i : s) : Set.range (opensOverι (W i.1.1 i.1.2)).left.base ⊆ U := by
      rw [range_opensOverι]
      exact hWU _ _
    let g (i : s) : opensOver (W i.1.1 i.1.2) ⟶ opensOver U :=
      opensOverLift U (opensOverι (W i.1.1 i.1.2)) (hWU' i)
    have : ∀ i, QuasiCompact (g i).left := fun i ↦ quasiCompact_left _
    have hcov (x : (opensOver U).left) : ∃ i, x ∈ Set.range (g i).left.base := by
      have hx : (opensOverι U).left.base x ∈ (U : Set Y.left) := by
        rw [← range_opensOverι]
        exact ⟨x, rfl⟩
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hs hx)
      refine ⟨⟨i, hi⟩, (mem_range_opensOverLift _ _ _ x).2 ?_⟩
      rw [range_opensOverι]
      exact hxi
    have hiso := isIso_of_forall_isIso_boundedConstructibleUpperStar_map
      (Profinite.padicAlgClRingObj ℓ) ℓ (Z := fun i : s ↦ opensOver (W i.1.1 i.1.2)) g hcov
      (0 : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι U)).obj E ⟶ _) fun i ↦ by
        have h0 := isZero_upperStar_obj_upperStar_obj _ ℓ (g i) (opensOverι U) E
          (by rw [opensOverLift_ι]; exact hWz _ _)
        exact ⟨⟨h0.to_ _, h0.eq_of_src _ _, h0.eq_of_src _ _⟩⟩
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← IsIso.hom_inv_id (0 : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι U)).obj E ⟶ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι U)).obj E), zero_comp]
  -- `E` is the pushforward of its restriction to `T₀`
  have hcompl : IsCompl (Set.range (opensOverι U).left.base) (Set.range u.left.base) := by
    rw [range_opensOverι]
    change IsCompl _ (Set.range t.imageι.base)
    rw [hrange]
    exact isCompl_compl.symm
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed_boundedConstructible ℓ hcompl E
  have h₁ : IsZero ((boundedConstructibleLowerShriek ℓ
      (opensOverι U)).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι U)).obj E)) :=
    Functor.map_isZero _ hEU
  have hunit : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ u).unit.app E) :=
    (Triangle.isZero₁_iff_isIso₂ _ hδ).1 h₁
  -- conclusion by conservativity of the finite direct image along `u ≫ q`
  have hq' : IsZero ((boundedConstructibleLowerStar ℓ q).obj E) :=
    IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ hq
  have h₂ : IsZero ((boundedConstructibleLowerStar ℓ (u ≫ q)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ u).obj E)) :=
    (hq'.of_iso ((boundedConstructibleLowerStar ℓ q).mapIso (asIso
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ u).unit.app E))).symm).of_iso
      ((boundedConstructibleLowerStarComp ℓ u q).app _).symm
  have h₃ := isZero_of_isZero_lowerStar_of_isFinite (u ≫ q) _ h₂
  exact (boundedConstructible _).ι.map_isZero
    (((boundedConstructibleLowerStar ℓ u).map_isZero h₃).of_iso (asIso
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ u).unit.app E)))

end AlgebraicGeometry.ProEtale.CondensedRing
