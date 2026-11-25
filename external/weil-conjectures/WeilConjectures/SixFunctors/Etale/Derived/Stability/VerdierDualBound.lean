/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualStrata

/-!
# Verdier duality preserves `Dctf`, with the Tor bound

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and
`Λ` a finite ring whose exponent is invertible in `k`. If `K ∈ Dᵇc(X, Λ)` has Tor amplitude in
`[a, b]`, then `𝔻_X K = RHom(K, ω_X)` is bounded constructible with Tor amplitude in
`[-b - 2d, -a]`
(`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed`,
`lemma-verdier-duality-preserves-constructibility--1`).

The proof is a noetherian induction on the closed subsets `T ⊆ X`, for all closed subschemes
`Z ⊆ X` supported in `T`: a reduced `Z` is cut into a dense open `U`, smooth over `k`, on which
`K` is lisse and where the Verdier dual is computed by
`AlgebraicGeometry.Etale.exists_boundedConstructible_and_torAmplitudeIn_verdierDual`, and its
closed complement, handled by induction; the localization step is
`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_verdierDual_of_localization`.
A non-reduced `Z` is reduced to `Z_red` by the same step, with empty open complement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The topological Krull dimension of an empty space is `⊥`. -/
lemma topologicalKrullDim_le_zero_of_isEmpty {V : Type*} [TopologicalSpace V] [IsEmpty V] :
    topologicalKrullDim V ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  have : IsEmpty (TopologicalSpace.IrreducibleCloseds V) :=
    ⟨fun s ↦ IsEmpty.false s.isIrreducible.nonempty.some⟩
  rw [topologicalKrullDim, Order.krullDim_eq_bot]
  exact bot_le

/-- Blueprint `lemma-verdier-duality-preserves-constructibility--1`: Constructible preservation
before biduality, over an algebraically closed field.

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and
`Λ` a finite ring whose exponent is invertible in `k`. If `K` is bounded constructible on `X_ét`
of Tor amplitude in `[a, b]`, then `𝔻_X K = RHom(K, ω_X)` is bounded constructible of Tor
amplitude in `[-b - 2d, -a]`. -/
theorem boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed {k : Type u}
    [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {a b : ℤ}
    {K : DerivedCategoryModule Λ X} (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((verdierDual Λ aX).obj (op K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
        ((verdierDual Λ aX).obj (op K)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  suffices key : ∀ (T : TopologicalSpace.Closeds X) {Z : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
      [HasCompactification aZ] (ι : Z ⟶ X) [IsClosedImmersion ι], ι ≫ aX = aZ →
      Set.range ι.base ⊆ T → ∀ (a b : ℤ) (K : DerivedCategoryModule Λ Z),
        boundedConstructible (ModuleCat.{u + 1} Λ) Z K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b K →
        boundedConstructible (ModuleCat.{u + 1} Λ) Z
            ((verdierDual Λ aZ).obj (op K)) ∧
          torAmplitudeIn (ModuleCat.{u + 1} Λ) Z (-b - 2 * (d : ℤ)) (-a)
            ((verdierDual Λ aZ).obj (op K)) from
    key ⊤ aX (𝟙 X) (Category.id_comp _) (Set.subset_univ _) a b K hK hKt
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  -- first for reduced closed subschemes
  have hred {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι] [IsReduced Z]
      [HasCompactification (ι ≫ aX)] (hT : Set.range ι.base ⊆ T) (a b : ℤ)
      (K : DerivedCategoryModule Λ Z) (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Z K)
      (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b K) :
      boundedConstructible (ModuleCat.{u + 1} Λ) Z
          ((verdierDual Λ (ι ≫ aX)).obj (op K)) ∧
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Z (-b - 2 * (d : ℤ)) (-a)
          ((verdierDual Λ (ι ≫ aX)).obj (op K)) := by
    by_cases hab : b < a
    · exact boundedConstructible_and_torAmplitudeIn_of_isZero
        (isZero_derivedHom_obj_of_isZero _ (isZero_of_torAmplitudeIn_of_lt hKt hab) _) _ _
    by_cases hZ : IsEmpty Z
    · exact boundedConstructible_and_torAmplitudeIn_of_isZero
        (isZero_derivedCategory_of_isEmpty _ Z _) _ _
    rw [not_isEmpty_iff] at hZ
    have : TopologicalSpace.NoetherianSpace Z := ι.isClosedEmbedding.isInducing.noetherianSpace
    -- a lisse smooth open `O` and a smaller nonempty open `O'` where the dual is controlled
    obtain ⟨O, _, _, n, _, P, hP, hPl, ⟨eK⟩⟩ :=
      exists_opens_smooth_isFiniteLocallyConstantSheaf Λ (ι ≫ aX) (not_lt.1 hab) hK hKt
    have : TopologicalSpace.NoetherianSpace O := O.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact O.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    obtain ⟨O', _, hO', hloc⟩ :=
      exists_boundedConstructible_and_torAmplitudeIn_verdierDual Λ (O.ι ≫ ι ≫ aX) n P hP hPl
    have : Nonempty O' := hO'.to_subtype
    let j := O'.ι ≫ O.ι
    let i := j.closedComplement
    have hij : Set.range i.base = (Set.range j.base)ᶜ := j.range_closedComplement
    -- the dimension of `O'` is `n ≤ d`
    have : SmoothOfRelativeDimension n (O'.ι ≫ O.ι ≫ ι ≫ aX) := by
      have : SmoothOfRelativeDimension (0 + n) (O'.ι ≫ O.ι ≫ ι ≫ aX) := inferInstance
      simpa using this
    have hdimO' := topologicalKrullDim_eq_of_smoothOfRelativeDimension (O'.ι ≫ O.ι ≫ ι ≫ aX) n
    have hnd : (n : WithBot ℕ∞) ≤ d := by
      rw [← hdimO']
      exact (O'.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
        O.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans
          (ι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hd)
    have hnd' : (n : ℤ) ≤ d := by exact_mod_cast hnd
    -- the closed piece, by induction
    let T' : TopologicalSpace.Closeds X :=
      ⟨Set.range (i ≫ ι).base, (i ≫ ι).isClosedEmbedding.isClosed_range⟩
    have hlt : T' < T := by
      refine lt_of_le_of_ne (fun x hx ↦ hT ?_) fun h ↦ ?_
      · obtain ⟨y, rfl⟩ := hx
        exact ⟨i.base y, rfl⟩
      · obtain ⟨o⟩ := ‹Nonempty O'›
        have hx : ι.base (j.base o) ∈ (T : Set X) := hT ⟨_, rfl⟩
        rw [← h] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Scheme.Hom.comp_base, TopCat.comp_app] at hy
        have hy' := ι.isClosedEmbedding.injective hy
        have : i.base y ∈ Set.range i.base := ⟨y, rfl⟩
        rw [hij, hy'] at this
        exact this ⟨o, rfl⟩
    have hZ' := ih T' hlt (i ≫ ι ≫ aX) (i ≫ ι) (Category.assoc _ _ _) le_rfl a b
      ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)
      (boundedConstructible_leftDerivedUpperStar _ i hK)
      (torAmplitudeIn_leftDerivedUpperStar _ i a b hKt)
    -- the open piece
    let e : (L((j)^*[ModuleCat.{u + 1} Λ])).obj K ≅
        D((O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P) :=
      (leftDerivedUpperStarComp _ O'.ι O.ι).app K ≪≫
        (L((O'.ι)^*[ModuleCat.{u + 1} Λ])).mapIso eK ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ O'.ι).app _
    have hjc : j ≫ ι ≫ aX = O'.ι ≫ O.ι ≫ ι ≫ aX := Category.assoc _ _ _
    let e' := (verdierDual Λ (j ≫ ι ≫ aX)).mapIso e.op
    rw [← verdierDual_obj_congr hjc] at hloc
    refine boundedConstructible_and_torAmplitudeIn_verdierDual_of_localization Λ (ι ≫ aX) j i
      hij n (by rw [hdimO']) K hZ'
      ⟨(boundedConstructible _ _).prop_of_iso e' hloc.1,
        (torAmplitudeIn _ _ _ _).prop_of_iso e' (hloc.2.mono (by omega) (by omega))⟩
  -- the general case, through the reduction
  intro Z aZ _ ι _ hι hT a b K hK hKt
  subst hι
  have : TopologicalSpace.NoetherianSpace Z := ι.isClosedEmbedding.isInducing.noetherianSpace
  let r := Z.nilradical.subschemeι
  let V := openComplementOfIsClosedImmersion r
  have hV : IsEmpty V := by
    refine ⟨fun x ↦ x.2 ?_⟩
    rw [show r = Z.nilradical.subschemeι from rfl, IdealSheafData.range_subschemeι,
      ← IdealSheafData.vanishingIdeal_top, IdealSheafData.coe_support_vanishingIdeal]
    trivial
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hrV : Set.range r.base = (Set.range V.ι.base)ᶜ := by
    simp [V, openComplementOfIsClosedImmersion]
  have hZr := hred (r ≫ ι) (hT.trans' (by
    rintro - ⟨y, rfl⟩
    exact ⟨r.base y, rfl⟩)) a b ((L((r)^*[ModuleCat.{u + 1} Λ])).obj K)
    (boundedConstructible_leftDerivedUpperStar _ r hK)
    (torAmplitudeIn_leftDerivedUpperStar _ r a b hKt)
  rw [verdierDual_obj_congr (Category.assoc r ι aX)] at hZr
  exact boundedConstructible_and_torAmplitudeIn_verdierDual_of_localization Λ (ι ≫ aX) V.ι r
    hrV 0 topologicalKrullDim_le_zero_of_isEmpty K hZr
    (boundedConstructible_and_torAmplitudeIn_of_isZero
      (isZero_derivedCategory_of_isEmpty _ V _) _ _)

end Etale

end AlgebraicGeometry
