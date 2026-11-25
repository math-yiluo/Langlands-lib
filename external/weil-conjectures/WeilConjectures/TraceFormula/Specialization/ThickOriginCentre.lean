/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineHyperplane
public import WeilConjectures.TraceFormula.Specialization.Defect

/-!

# The thick origin of the affine line

For `m ≥ 1`, the *thick origin* of the affine line `𝔸¹_k = Spec k[x]` is the closed subscheme
`Z = V(x^m) = Spec k[x]/(x^m)` (`AlgebraicGeometry.polyAffineThickOrigin`). Its structure morphism
`Z ⟶ Spec k` is a universal homeomorphism
(`ProEtale.CondensedRing.isUniversalHomeomorphism_centre_polyAffineThickOrigin`): it has the
origin as a section, which is a surjective closed immersion since `Z` is a single point.

The general criterion used is `AlgebraicGeometry.IsUniversalHomeomorphism.of_comp_eq_id`: an
affine morphism admitting a section which is a universal homeomorphism is a universal
homeomorphism, since every base change of it is inverse to the base change of the section on
underlying spaces.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

namespace IsUniversalHomeomorphism

variable {Z S : Scheme.{u}} {f : Z ⟶ S} {s : S ⟶ Z}

/-- If `s` is a section of `f` and a universal homeomorphism, every base change `f'` of `f` is a
homeomorphism on underlying spaces: it is inverse to the base change of `s`. -/
lemma isHomeomorph_of_isPullback_of_comp_eq_id (hs : s ≫ f = 𝟙 S) [IsUniversalHomeomorphism s]
    {Z' S' : Scheme.{u}} {f' : Z' ⟶ S'} {i₁ : Z' ⟶ Z} {i₂ : S' ⟶ S}
    (h : IsPullback f' i₁ i₂ f) : IsHomeomorph f'.base := by
  let s' : S' ⟶ Z' := h.lift (𝟙 S') (i₂ ≫ s) (by rw [Category.id_comp, Category.assoc, hs,
    Category.comp_id])
  have hs' : s' ≫ f' = 𝟙 S' := h.lift_fst _ _ _
  have hsq : IsPullback s' i₂ i₁ s := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hs', hs]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have : IsUniversalHomeomorphism s' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let e := s'.isHomeomorph.homeomorph
  have he : (f'.base : Z' → S') = e.symm := by
    funext z
    obtain ⟨a, rfl⟩ := e.surjective z
    rw [Homeomorph.symm_apply_apply]
    exact congr($hs' a)
  rw [he]
  exact e.symm.isHomeomorph

/-- **An affine morphism with a universally homeomorphic section is a universal
homeomorphism**: every base change of it is a homeomorphism
(`AlgebraicGeometry.IsUniversalHomeomorphism.isHomeomorph_of_isPullback_of_comp_eq_id`), so it is
universally closed, hence integral, universally injective, and surjective. -/
theorem of_comp_eq_id [IsAffineHom f] (hs : s ≫ f = 𝟙 S) [IsUniversalHomeomorphism s] :
    IsUniversalHomeomorphism f := by
  have : UniversallyClosed f := by
    rw [universallyClosed_eq]
    exact fun _ _ _ _ _ h ↦ (isHomeomorph_of_isPullback_of_comp_eq_id hs h).isClosedMap
  have : IsIntegralHom f := IsIntegralHom.iff_universallyClosed_and_isAffineHom.2 ⟨this, ‹_›⟩
  have : UniversallyInjective f := by
    rw [universallyInjective_eq]
    exact fun _ _ _ _ _ h ↦ (isHomeomorph_of_isPullback_of_comp_eq_id hs h).injective
  have : Surjective f := by
    have : Surjective (s ≫ f) := by
      rw [hs]
      infer_instance
    exact Surjective.of_comp s f
  exact { }

end IsUniversalHomeomorphism

variable (k : Type u) [Field k]

/-- The *thick origin* `V(x^m) ⊆ 𝔸¹_k = Spec k[x]`. -/
noncomputable def polyAffineThickOrigin (m : ℕ) : (polyAffine k 1).left.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {polyAffineCoord k (Fin.last 0) ^ m})

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k : Type u) [Field k]

/-- The origin `Spec k ⟶ 𝔸¹_k`, evaluation at `x = 0`. -/
noncomputable def polyAffineOrigin : Spec (.of k) ⟶ (polyAffine k 1).left :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (σ := Fin 1) (R := k)))

@[reassoc (attr := simp)]
lemma polyAffineOrigin_hom : polyAffineOrigin k ≫ (polyAffine k 1).hom = 𝟙 _ := by
  dsimp [polyAffineOrigin, polyAffine]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  simp

/-- The coordinate `x^m` vanishes at the origin. -/
lemma polyAffineOrigin_appTop_coord_pow {m : ℕ} (hm : 0 < m) :
    (polyAffineOrigin k).appTop (polyAffineCoord k (Fin.last 0) ^ m) = 0 := by
  have h : (polyAffineOrigin k).appTop (polyAffineCoord k (Fin.last 0)) = 0 := by
    have h' : (Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (σ := Fin 1)
        (R := k)))).appTop (polyAffineCoord k (Fin.last 0)) = 0 := by
      rw [polyAffineCoord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      simp
    exact h'
  rw [map_pow, h, zero_pow hm.ne']

/-- The thick origin `V(x^m)` contains the origin. -/
lemma polyAffineThickOrigin_le_ker {m : ℕ} (hm : 0 < m) :
    polyAffineThickOrigin k m ≤ (polyAffineOrigin k).ker :=
  IdealSheafData.ofIdealTop_span_le_ker _ fun t ht ↦ by
    rw [Set.mem_singleton_iff.1 ht]
    exact polyAffineOrigin_appTop_coord_pow k hm

/-- The origin, as a point of the thick origin `V(x^m)`. -/
noncomputable def thickOriginPoint {m : ℕ} (hm : 0 < m) :
    Spec (.of k) ⟶ (centre (polyAffine k 1) (polyAffineThickOrigin k m)).left :=
  (polyAffineOrigin k).toImage ≫ IdealSheafData.inclusion (polyAffineThickOrigin_le_ker k hm)

@[reassoc (attr := simp)]
lemma thickOriginPoint_hom {m : ℕ} (hm : 0 < m) :
    thickOriginPoint k hm ≫ (centre (polyAffine k 1) (polyAffineThickOrigin k m)).hom = 𝟙 _ := by
  simp [thickOriginPoint, centre]

/-- The thick origin `V(x^m)` is a single point. -/
lemma subsingleton_polyAffineThickOrigin_subscheme {m : ℕ} (hm : 0 < m) :
    Subsingleton (polyAffineThickOrigin k m).subscheme := by
  have := subsingleton_polyAffineHyperplane_subscheme k
  have h : Set.range (polyAffineThickOrigin k m).subschemeι.base =
      Set.range (polyAffineHyperplane k 0).subschemeι.base := by
    rw [polyAffineThickOrigin, polyAffineHyperplane,
      IdealSheafData.range_subschemeι_ofIdealTop_span,
      IdealSheafData.range_subschemeι_ofIdealTop_span, Scheme.zeroLocus_singleton,
      Scheme.zeroLocus_singleton, Scheme.basicOpen_pow _ _ hm]
  refine ⟨fun a b ↦ (polyAffineThickOrigin k m).subschemeι.isClosedEmbedding.injective ?_⟩
  obtain ⟨a', ha'⟩ : (polyAffineThickOrigin k m).subschemeι a ∈
      Set.range (polyAffineHyperplane k 0).subschemeι.base := by
    rw [← h]
    exact ⟨a, rfl⟩
  obtain ⟨b', hb'⟩ : (polyAffineThickOrigin k m).subschemeι b ∈
      Set.range (polyAffineHyperplane k 0).subschemeι.base := by
    rw [← h]
    exact ⟨b, rfl⟩
  rw [← ha', ← hb', Subsingleton.elim a' b']

/-- **The thick origin is a universally homeomorphic point**: for `m ≥ 1`, the structure morphism
of `V(x^m) = Spec k[x]/(x^m)` is a universal homeomorphism. The origin is a section of it, and a
surjective closed immersion since `V(x^m)` is a single point. -/
theorem isUniversalHomeomorphism_centre_polyAffineThickOrigin {m : ℕ} (hm : 0 < m) :
    IsUniversalHomeomorphism (centre (polyAffine k 1) (polyAffineThickOrigin k m)).hom := by
  have : Subsingleton (centre (polyAffine k 1) (polyAffineThickOrigin k m)).left :=
    subsingleton_polyAffineThickOrigin_subscheme k hm
  have : IsAffineHom (polyAffine k 1).hom := by
    dsimp [polyAffine]
    infer_instance
  have : IsAffineHom (centre (polyAffine k 1) (polyAffineThickOrigin k m)).hom :=
    inferInstanceAs (IsAffineHom (_ ≫ _))
  have : IsClosedImmersion (thickOriginPoint k hm) :=
    isClosedImmersion_of_comp_eq_id _ _ (thickOriginPoint_hom k hm)
  have : Surjective (thickOriginPoint k hm) := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
    exact ⟨p, Subsingleton.elim _ _⟩
  exact IsUniversalHomeomorphism.of_comp_eq_id (thickOriginPoint_hom k hm)

end AlgebraicGeometry.ProEtale.CondensedRing
