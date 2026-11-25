/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialAffineNoether
public import WeilConjectures.TraceFormula.Specialization.DefectBoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.DefectGenericDivisor
public import WeilConjectures.TraceFormula.Specialization.FiniteSupportConservative

/-!

# Vanishing of the defect for a coordinate hyperplane

For `X = 𝔸^{N+1}_k = Spec k[X₀, …, X_N]` and the coordinate hyperplane `Z = V(X_N)`, the defect
`C_{X,Z}(L)` of `ProEtale.CondensedRing.specializationDefect` vanishes for every bounded
constructible `ℚ̄_ℓ`-complex `L` (`ProEtale.CondensedRing.isZero_specializationDefect_polyAffine`,
blueprint `theorem-verdier-s-theorem-specialization-zero`). Consequently the defect vanishes along
the principal divisor of a global function on an affine `k`-scheme of finite type
(`ProEtale.CondensedRing.isZero_specializationDefect_ofIdealTop_span_singleton`).

The proof follows the blueprint, by induction on `N`.
* Replacing `L` by `j_! j^* L` does not change the defect, so we may assume `Li^* L = 0`
  (`ProEtale.CondensedRing.isZero_specializationDefect_of_forall_isZero_upperStar`).
* The defect then vanishes over a dense open `U ⊆ Z`
  (`ProEtale.CondensedRing.exists_dense_isZero_specializationDefect`, blueprint
  `lemma-vanishing-generic-points-principal-divisor--1`). For `N = 0` the hyperplane is a point, so
  `U = Z`.
* For `N + 1`, after an automorphism of `X` preserving `Z` the projection `q : X ⟶ X'` forgetting
  `X₀` is finite on `Y = Z ∖ U` (`AlgebraicGeometry.exists_isFinite_polyAffineProj`). Compactify
  `q` by `v : X ⟶ X̄ = ℙ¹_{X'}`, `q̄ : X̄ ⟶ X'`. The proper exchange along `q̄` and the induction
  hypothesis give `Rq̄_{Z*} C_{X̄, Z̄}(v_! L) = 0`; the smooth exchange along `v` identifies the
  restriction of `C_{X̄, Z̄}(v_! L)` to `Z` with `C_{X,Z}(L)`. So `C_{X̄, Z̄}(v_! L)` is supported
  on `Y ∪ (Z̄ ∖ Z)`, which is finite over `Z'`, and it vanishes because direct image is
  conservative on finite support
  (`ProEtale.CondensedRing.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`, blueprint
  `lemma-nearby-cycles-constant-family`).

-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme ProjectiveLine

/-- The image of `f` is contained in the image of `[f, g] : A ⨿ B ⟶ C`. -/
lemma range_subset_range_coprod_desc_left {A B C : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) :
    Set.range f.base ⊆ Set.range (coprod.desc f g).base := by
  rintro _ ⟨s, rfl⟩
  exact ⟨(coprod.inl : A ⟶ A ⨿ B).base s, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩

/-- The image of `g` is contained in the image of `[f, g] : A ⨿ B ⟶ C`. -/
lemma range_subset_range_coprod_desc_right {A B C : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) :
    Set.range g.base ⊆ Set.range (coprod.desc f g).base := by
  rintro _ ⟨s, rfl⟩
  exact ⟨(coprod.inr : B ⟶ A ⨿ B).base s, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

/-- Membership in the image on constant special fibres can be checked on the ambient scheme. -/
private lemma mem_range_centreSpecialFibreMap_iff {k : Type u} [Field k]
    (k' : Type u) [Field k'] [Algebra k k'] {X X' : Over (Spec (.of k))}
    (f : X' ⟶ X) (I : X.left.IdealSheafData)
    (y : (deformationSpecialFibre (centre X I) ⊥ k').left) :
    y ∈ Set.range (centreSpecialFibreMap f I k').left.base ↔
      I.subschemeι (constantSpecialFibreProj k' (centre X I) y) ∈ Set.range f.left.base := by
  rw [range_centreSpecialFibreMap_eq_preimage, range_centreMap]
  rfl

/-- Projection to the ambient scheme commutes with the map on constant special fibres. -/
private lemma centreSpecialFibreMap_toBase_apply {k : Type u} [Field k]
    (k' : Type u) [Field k'] [Algebra k k'] {X X' : Over (Spec (.of k))}
    (f : X' ⟶ X) (I : X.left.IdealSheafData)
    (x : (deformationSpecialFibre (centre X' (I.comap f.left)) ⊥ k').left) :
    I.subschemeι (constantSpecialFibreProj k' (centre X I)
      ((centreSpecialFibreMap f I k').left x)) =
      f.left ((centreι X' (I.comap f.left)).left
        (constantSpecialFibreProj k' (centre X' (I.comap f.left)) x)) := by
  have h := congrArg (fun g ↦ g.base x)
    (centreSpecialFibreMap_constantSpecialFibreProj k' f I)
  change constantSpecialFibreProj k' (centre X I) ((centreSpecialFibreMap f I k').left x) =
    (centreMap f I).left (constantSpecialFibreProj k' (centre X' (I.comap f.left)) x) at h
  rw [h]
  exact congrArg (fun g ↦ g.left (constantSpecialFibreProj k'
    (centre X' (I.comap f.left)) x)) (centreMap_centreι f I)

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [hk' : Fact (ringChar k').Prime] [hk'ℓ : Fact (ringChar k' ≠ ℓ)]

include hk' hk'ℓ


/-- The base case `N = 0` of `ProEtale.CondensedRing.isZero_specializationDefect_polyAffine`: the
coordinate hyperplane of the affine line is a point, so the generic vanishing of the defect
(`ProEtale.CondensedRing.exists_dense_isZero_specializationDefect`) is vanishing. -/
theorem isZero_specializationDefect_polyAffine_zero
    (L : Dᵇc((polyAffine k 1).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineHyperplane k 0) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  refine isZero_specializationDefect_of_forall_isZero_upperStar (k' := k') _ _
    (fun L₀ hL₀ ↦ ?_) L
  obtain ⟨U, hUd, hU⟩ := exists_dense_isZero_specializationDefect k'
    (I := polyAffineHyperplane k 0)
    (isNormalScheme_polyAffine k 1) (polyAffineCoord_ne_zero k _) rfl L₀ hL₀
  have : Subsingleton (centre (polyAffine k 1) (polyAffineHyperplane k 0)).left :=
    subsingleton_polyAffineHyperplane_subscheme k
  have hU' : U = ⊤ := by
    refine SetLike.coe_injective (Set.eq_univ_of_forall fun x ↦ ?_)
    have : Nonempty (centre (polyAffine k 1) (polyAffineHyperplane k 0)).left := ⟨x⟩
    obtain ⟨y, hy⟩ := hUd.nonempty
    exact Subsingleton.elim y x ▸ hy
  subst hU'
  let F := deformationSpecialFibre (centre (polyAffine k 1) (polyAffineHyperplane k 0)) ⊥ k'
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  have : CompactSpace F.left := QuasiCompact.compactSpace_of_compactSpace F.hom
  have : IsNoetherian F.left := ⟨⟩
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (Profinite.padicAlgClRingObj ℓ) (fun _ : Unit ↦ (constantSpecialFibreProj k'
      (centre (polyAffine k 1) (polyAffineHyperplane k 0)) ⁻¹ᵁ ⊤).ι) (fun x ↦ ⟨(), by simp⟩)
  have (_ : Unit) : IsIso ((L((((constantSpecialFibreProj k' (centre (polyAffine k 1)
      (polyAffineHyperplane k 0))) ⁻¹ᵁ ⊤).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
      (0 : specializationDefect (polyAffine k 1) (polyAffineHyperplane k 0) k'
        (Profinite.padicAlgClRingObj ℓ) L₀.obj ⟶ 0)) :=
    hU.isIso (Functor.map_isZero _ (isZero_zero _)) _
  exact ((isIsoZero_iff_source_target_isZero _ _).1 (@JointlyReflectIsomorphisms.isIso _ _ _ _ _ _
    hP _ _ (0 : specializationDefect (polyAffine k 1) (polyAffineHyperplane k 0) k'
      (Profinite.padicAlgClRingObj ℓ) L₀.obj ⟶ 0) this)).1

/-- The inductive step of `ProEtale.CondensedRing.isZero_specializationDefect_polyAffine`, after
the generic vanishing and the Noether normalisation: let `ψ` be an automorphism of `𝔸^{N+2}_k`,
`v : 𝔸^{N+2}_k ⟶ ℙ¹_{𝔸^{N+1}_k}` the composite of `ψ` and the compactification of `X₀`, and
`Z = v⁻¹ Z̄` for the inverse image `Z̄` of the coordinate hyperplane of `𝔸^{N+1}_k`. If the defect
`C_{𝔸^{N+1}, V(X_N)}` vanishes, `C_{𝔸^{N+2}, Z}(L)` vanishes over an open `U ⊆ Z`, and `Z ∖ U` lies
in the image of some `a : V ⟶ 𝔸^{N+2}_k` with `V ⟶ 𝔸^{N+1}_k` finite, then
`C_{𝔸^{N+2}, Z}(L) = 0`. -/
theorem isZero_specializationDefect_of_isFinite (N : ℕ)
    (ih : ∀ L : Dᵇc((polyAffine k (N + 1)).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero (specializationDefect (polyAffine k (N + 1)) (polyAffineHyperplane k N) k'
        (Profinite.padicAlgClRingObj ℓ) L.obj))
    (ψ : polyAffine k (N + 2) ≅ polyAffine k (N + 2)) {V : Scheme.{u}}
    (a : V ⟶ (polyAffine k (N + 2)).left)
    (hfin : IsFinite (a ≫ ψ.hom.left ≫ (polyAffineProj k (N + 1)).left))
    {I : (polyAffine k (N + 2)).left.IdealSheafData}
    (hI : ((polyAffineHyperplane k N).comap
      (overProjectiveLineProj (polyAffine k (N + 1))).left).comap
        (ψ.hom ≫ polyAffineChart k (N + 1)).left = I)
    (L₀ : Dᵇc((polyAffine k (N + 2)).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (U : (centre (polyAffine k (N + 2)) I).left.Opens)
    (hU : IsZero ((L((((constantSpecialFibreProj k' (centre (polyAffine k (N + 2)) I)) ⁻¹ᵁ
      U).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (specializationDefect (polyAffine k (N + 2)) I k' (Profinite.padicAlgClRingObj ℓ)
          L₀.obj)))
    (hY : (centreι (polyAffine k (N + 2)) I).left.base '' (U : Set _)ᶜ ⊆ Set.range a.base) :
    IsZero (specializationDefect (polyAffine k (N + 2)) I k' (Profinite.padicAlgClRingObj ℓ)
      L₀.obj) := by
  subst hI
  let Λ := Profinite.padicAlgClRingObj ℓ
  let p := overProjectiveLineProj (polyAffine k (N + 1))
  let H' := polyAffineHyperplane k N
  let H := H'.comap p.left
  let v := ψ.hom ≫ polyAffineChart k (N + 1)
  have : IsIso ψ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have : IsOpenImmersion v.left :=
    inferInstanceAs (IsOpenImmersion (ψ.hom.left ≫ (polyAffineChart k (N + 1)).left))
  let L := (boundedConstructibleOpenImmersionLowerShriek Λ ℓ v).obj L₀
  let C := specializationDefect (overProjectiveLine (polyAffine k (N + 1))) H k' Λ L.obj
  -- the proper exchange along `p` and the induction hypothesis: `Rp_{Z*} C = 0`
  have hq : IsZero ((R(((centreSpecialFibreMap p H' k').left)_*⟦Λ⟧)).obj C) := by
    obtain ⟨e⟩ := nonempty_specializationDefect_lowerStar_iso p H' k' L
    obtain ⟨e'⟩ := nonempty_specializationDefect_iso (polyAffine k (N + 1)) H' k' Λ
      ((boundedConstructibleLowerStarCompatibility ℓ p).app L)
    exact ((ih ((boundedConstructibleLowerStar ℓ p).obj L)).of_iso e'.symm).of_iso e.symm
  -- the smooth exchange along `v`: `C_{X, Z}(L₀) ≅ Lv_Z^* C`
  obtain ⟨e₁⟩ : Nonempty (specializationDefect (polyAffine k (N + 2)) (H.comap v.left) k' Λ L₀.obj ≅
      (L(((centreSpecialFibreMap v H k').left)^*⟦Λ⟧)).obj C) := by
    have : Smooth v.left := inferInstance
    have h₁ := nonempty_specializationDefect_upperStar_iso (ℓ := ℓ) (k' := k') v H L
    have h₂ := nonempty_specializationDefect_iso (polyAffine k (N + 2)) (H.comap v.left) k' Λ
      ((boundedConstructible _).ι.mapIso (asIso
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ v).unit.app L₀)) ≪≫
        (boundedConstructibleUpperStarCompatibility Λ ℓ v).app L)
    exact ⟨h₂.some ≪≫ h₁.some⟩
  suffices hC : IsZero C from (Functor.map_isZero _ hC).of_iso e₁
  -- the closed subset `(Z ∖ U) ∪ (Z̄ ∖ Z)` of `N_⊥ Z̄`, finite over `N_⊥ Z'`
  let aO : Over.mk (a ≫ (polyAffine k (N + 2)).hom) ⟶ overProjectiveLine (polyAffine k (N + 1)) :=
    Over.homMk (a ≫ v.left) (by rw [Category.assoc, Over.w v]; rfl)
  have : IsFinite (overProjectiveLineInfinity (polyAffine k (N + 1)) ≫ p).left := by
    rw [overProjectiveLineInfinity_proj]
    exact inferInstanceAs (IsFinite (𝟙 _))
  have : IsFinite (aO ≫ p).left := by
    have h : (aO ≫ p).left = a ≫ ψ.hom.left ≫ (polyAffineProj k (N + 1)).left := by
      rw [← polyAffineChart_proj]
      rfl
    rw [h]
    exact hfin
  let t₁ := (centreSpecialFibreMap (overProjectiveLineInfinity (polyAffine k (N + 1))) H k').left
  let t₂ := (centreSpecialFibreMap aO H k').left
  have : IsFinite (t₁ ≫ (centreSpecialFibreMap p H' k').left) :=
    isFinite_centreSpecialFibreMap_comp k' p H' _
  have : IsFinite (t₂ ≫ (centreSpecialFibreMap p H' k').left) :=
    isFinite_centreSpecialFibreMap_comp k' p H' _
  have : IsFinite (coprod.desc t₁ t₂ ≫ (centreSpecialFibreMap p H' k').left) := by
    rw [coprod.desc_comp]
    infer_instance
  refine isZero_of_isZero_rightDerivedLowerStar_of_isFinite (centreSpecialFibreMap p H' k')
    (coprod.desc t₁ t₂) ⟨C, boundedConstructible_specializationDefect k' _ H L⟩ ?_ hq
  -- the support condition
  intro y hy
  have hy₁ : y ∉ Set.range t₁.base := fun h ↦ hy (range_subset_range_coprod_desc_left _ _ h)
  have hy₂ : y ∉ Set.range t₂.base := fun h ↦ hy (range_subset_range_coprod_desc_right _ _ h)
  -- `y` lies over the affine chart
  have hyv : y ∈ Set.range (centreSpecialFibreMap v H k').left.base := by
    have h₁ : H.subschemeι (constantSpecialFibreProj k' (centre _ H) y) ∉
        Set.range (overProjectiveLineInfinity (polyAffine k (N + 1))).left.base := by
      intro h
      exact hy₁ ((mem_range_centreSpecialFibreMap_iff k' _ H y).2 h)
    have h₂ : Set.range v.left.base = Set.range (polyAffineChart k (N + 1)).left.base := by
      change Set.range (ψ.hom.left ≫ (polyAffineChart k (N + 1)).left).base = _
      rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
        Scheme.Hom.coe_opensRange]
    rw [mem_range_centreSpecialFibreMap_iff k' v H, h₂, range_polyAffineChart]
    exact h₁
  rcases hyv with ⟨x, hxy⟩
  by_cases hx : constantSpecialFibreProj k' (centre _ _) x ∈ U
  · -- over `U` the defect vanishes
    refine ⟨_, ((constantSpecialFibreProj k'
      (centre (polyAffine k (N + 2)) (H.comap v.left))) ⁻¹ᵁ U).ι ≫
      (centreSpecialFibreMap v H k').left, inferInstance, ⟨⟨x, hx⟩, hxy⟩, ?_⟩
    exact (hU.of_iso ((L((((constantSpecialFibreProj k'
      (centre (polyAffine k (N + 2)) (H.comap v.left))) ⁻¹ᵁ U).ι)^*⟦Λ⟧)).mapIso
      e₁.symm)).of_iso ((leftDerivedUpperStarComp Λ _ _).app C)
  · -- outside `U`, the point lies over `a`
    refine absurd ?_ hy₂
    apply (mem_range_centreSpecialFibreMap_iff k' aO H y).2
    rw [← hxy, centreSpecialFibreMap_toBase_apply]
    change v.left.base _ ∈ Set.range (a ≫ v.left).base
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.mem_image_of_mem v.left.base (hY ⟨_, hx, rfl⟩)

/-- The inductive step of `ProEtale.CondensedRing.isZero_specializationDefect_polyAffine`. -/
theorem isZero_specializationDefect_polyAffine_succ (N : ℕ)
    (ih : ∀ L : Dᵇc((polyAffine k (N + 1)).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero (specializationDefect (polyAffine k (N + 1)) (polyAffineHyperplane k N) k'
        (Profinite.padicAlgClRingObj ℓ) L.obj))
    (L : Dᵇc((polyAffine k (N + 2)).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect (polyAffine k (N + 2)) (polyAffineHyperplane k (N + 1)) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  refine isZero_specializationDefect_of_forall_isZero_upperStar (k' := k') _ _
    (fun L₀ hL₀ ↦ ?_) L
  obtain ⟨U, hUd, hU⟩ := exists_dense_isZero_specializationDefect k'
    (I := polyAffineHyperplane k (N + 1))
    (isNormalScheme_polyAffine k (N + 2)) (polyAffineCoord_ne_zero k _) rfl L₀ hL₀
  let H := polyAffineHyperplane k (N + 1)
  have hι := (centreι (polyAffine k (N + 2)) H).left.isClosedEmbedding
  let Y := (centreι (polyAffine k (N + 2)) H).left.base '' (U : Set _)ᶜ
  have hYc : IsClosed Y := hι.isClosedMap _ U.isOpen.isClosed_compl
  have hYH : Y ⊆ (H.support : Set (polyAffine k (N + 2)).left) := by
    rintro _ ⟨z, -, rfl⟩
    rw [← IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hne : ¬ (H.support : Set (polyAffine k (N + 2)).left) ⊆ Y := by
    intro hsub
    have : Nonempty (centre (polyAffine k (N + 2)) H).left :=
      nonempty_polyAffineHyperplane_subscheme k (N + 1)
    obtain ⟨z, hz⟩ := hUd.nonempty
    obtain ⟨z', hz', he⟩ := hsub (by rw [← IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
    exact hz' (hι.injective he ▸ hz)
  obtain ⟨ψ, V, a, hYa, hfin, hψ⟩ := exists_isFinite_polyAffineProj N hYc hYH hne
  refine isZero_specializationDefect_of_isFinite k' N ih ψ a hfin ?_ L₀ U hU hYa
  have h : (ψ.hom ≫ polyAffineChart k (N + 1)).left ≫
      (overProjectiveLineProj (polyAffine k (N + 1))).left =
        ψ.hom.left ≫ (polyAffineProj k (N + 1)).left := by
    rw [← Over.comp_left, Category.assoc, polyAffineChart_proj, Over.comp_left]
  rw [← IdealSheafData.comap_comp, h, IdealSheafData.comap_comp,
    comap_polyAffineProj_polyAffineHyperplane, hψ]

/-- **Vanishing of the defect for a coordinate hyperplane** (blueprint
`theorem-verdier-s-theorem-specialization-zero`): for `X = 𝔸^{N+1}_k` and the coordinate hyperplane
`Z = V(X_N)`, the defect `C_{X,Z}(L)` vanishes for every bounded constructible `L`. -/
theorem isZero_specializationDefect_polyAffine (N : ℕ)
    (L : Dᵇc((polyAffine k (N + 1)).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect (polyAffine k (N + 1)) (polyAffineHyperplane k N) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  induction N with
  | zero => exact isZero_specializationDefect_polyAffine_zero k' L
  | succ N ih => exact isZero_specializationDefect_polyAffine_succ k' N ih L


/-- The defect vanishes for the inverse image of the coordinate hyperplane under a closed immersion
`a : V ⟶ 𝔸^{n+1}_k`: the proper exchange gives
`C_{𝔸, V(X_n)}(Ra_* L) ≅ Ra_{Z*} C_{V, a⁻¹ V(X_n)}(L)`, the left side vanishes by
`ProEtale.CondensedRing.isZero_specializationDefect_polyAffine`, and `Ra_{Z*}` is fully faithful
since `a_Z` is a closed immersion. -/
theorem isZero_specializationDefect_comap_polyAffineHyperplane {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] {n : ℕ}
    (a : V ⟶ polyAffine k (n + 1)) [IsClosedImmersion a.left]
    (L : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect V ((polyAffineHyperplane k n).comap a.left) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  set aZ := (centreSpecialFibreMap a (polyAffineHyperplane k n) k').left
  let Λ := Profinite.padicAlgClRingObj ℓ
  have e := (nonempty_specializationDefect_lowerStar_iso (ℓ := ℓ) a (polyAffineHyperplane k n)
    k' L).some
  have e' := (nonempty_specializationDefect_iso (polyAffine k (n + 1)) (polyAffineHyperplane k n)
    k' Λ ((boundedConstructibleLowerStarCompatibility ℓ a).app L)).some
  have h₀ : IsZero (R((aZ)_*⟦Λ⟧).obj
      (specializationDefect V ((polyAffineHyperplane k n).comap a.left) k' Λ L.obj)) :=
    ((isZero_specializationDefect_polyAffine (ℓ := ℓ) k' n
      ((boundedConstructibleLowerStar ℓ a).obj L)).of_iso e'.symm).of_iso e.symm
  have : IsClosedImmersion aZ :=
    isClosedImmersion_centreSpecialFibreMap (k' := k') a (polyAffineHyperplane k n)
  have h₁ := L((aZ)^*⟦Λ⟧).map_isZero h₀
  have : IsIso (derivedUpperStarLowerStarAdjunction Λ aZ).counit :=
    isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ aZ
  have e₁ := asIso (Adjunction.counit (derivedUpperStarLowerStarAdjunction Λ aZ) |>.app
    (specializationDefect V ((polyAffineHyperplane k n).comap a.left) k' Λ L.obj))
  exact h₁.of_iso e₁.symm

/-- The defect vanishes for a principal divisor `V(h)` of an affine `k`-scheme of finite type
(proof of blueprint `theorem-verdier-s-theorem-specialization-zero--1`): embed `V(h) ⊆ V` into a
coordinate hyperplane of an affine space by a closed immersion
(`AlgebraicGeometry.exists_isClosedImmersion_comap_polyAffineHyperplane`). -/
theorem isZero_specializationDefect_ofIdealTop_span_singleton {V : Over (Spec (.of k))}
    [IsAffine V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (h : Γ(V.left, ⊤)) (L : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect V (IdealSheafData.ofIdealTop (Ideal.span {h})) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  obtain ⟨n, a, ha, hI⟩ := exists_isClosedImmersion_comap_polyAffineHyperplane h
  exact hI ▸ isZero_specializationDefect_comap_polyAffineHyperplane k' a L

end AlgebraicGeometry.ProEtale.CondensedRing
