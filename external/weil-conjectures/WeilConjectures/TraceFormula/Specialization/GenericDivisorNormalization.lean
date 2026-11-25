/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding
public import WeilConjectures.AlgebraicGeometry.NormalizationCover
public import WeilConjectures.AlgebraicGeometry.NormalSchemeOpen

/-!

# Normalization of a normal scheme in a finite étale cover of an open subscheme

Let `X` be a normal scheme of finite type over a field `k`, `I` an ideal sheaf on `X` with
support `Z`, and `v : W ⟶ X ∖ Z` a connected finite étale cover. The normalization `X'` of `X`
in `W` is normal, finite over `X`, and the complement of `V(f^* I)` in `X'` is identified with
`W` over `v`. This is the normalisation step of the generic-divisor argument
(blueprint `lemma-vanishing-generic-points-principal-divisor--1`).

## Main results

- `AlgebraicGeometry.Scheme.exists_isIso_isPullback_preimage_of_isOpenImmersion`: an open
  immersion `t : W ⟶ Y` over `v : W ⟶ U` with range `g⁻¹(U)` identifies `W` with `g⁻¹(U)`,
  compatibly with the pullback square.
- `AlgebraicGeometry.exists_normalization_of_finite_etale`: the normalization of `X` in a
  connected finite étale cover of `X ∖ Z`, packaged as an object of `Over (Spec k)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Let `g : Y ⟶ X`, `U ⊆ X` open, `v : W ⟶ U` and `t : W ⟶ Y` an open immersion with
`t ≫ g = v ≫ U.ι` and range `g⁻¹(U)`. Then `t` factors through an isomorphism
`w : W ≅ g⁻¹(U)`, and `W` is the pullback of `g` along `U.ι`. -/
theorem Scheme.exists_isIso_isPullback_preimage_of_isOpenImmersion {W X Y : Scheme.{u}}
    {U : X.Opens} (v : W ⟶ U) (g : Y ⟶ X) (t : W ⟶ Y) [IsOpenImmersion t]
    (ht : t ≫ g = v ≫ U.ι) (hrange : Set.range t.base = g.base ⁻¹' U) :
    ∃ w : W ⟶ (g ⁻¹ᵁ U).toScheme, IsIso w ∧ w ≫ (g ⁻¹ᵁ U).ι = t ∧
      IsPullback (w ≫ (g ⁻¹ᵁ U).ι) v g U.ι := by
  have hr : Set.range t.base = Set.range (g ⁻¹ᵁ U).ι.base := by
    rw [hrange, Scheme.Opens.range_ι]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq t (g ⁻¹ᵁ U).ι hr
  have he : e.hom ≫ (g ⁻¹ᵁ U).ι = t := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  have hv : e.hom ≫ (g ∣_ U) = v := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he, ht]
  refine ⟨e.hom, inferInstance, he, (isPullback_morphismRestrict g U).flip.of_iso e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)⟩
  rw [← hv]
  simp

/-- **Normalization in a finite étale cover of the complement of a divisor** (the normalisation
step of blueprint `lemma-vanishing-generic-points-principal-divisor--1`, via
`lem-fin-normalization-extends-cover`): let `X` be a normal scheme of finite type over a field `k`,
`I` an ideal sheaf on `X` with support `Z`, and `v : W ⟶ X ∖ Z` a finite étale cover with `W`
connected. Then there are a normal scheme `X'` of finite type over `k` (the normalization of `X` in
`W`) and a finite morphism `f : X' ⟶ X` such that `X' ∖ V(f^* I)` is identified with `W` by an
isomorphism `w`, and the square `W ⟶ X' ∖ V(f^* I) ⟶ X'` over `v` and `f` is a pullback square. -/
theorem exists_normalization_of_finite_etale {k : Type u} [Field k] {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (hX : IsNormalScheme X.left) (I : X.left.IdealSheafData) {W : Scheme.{u}} [ConnectedSpace W]
    (v : W ⟶ (overRestrict X I.support.compl).left) [IsFinite v] [Etale v] :
    ∃ (X' : Over (Spec (.of k))) (_ : LocallyOfFiniteType X'.hom) (_ : QuasiCompact X'.hom)
      (_ : IsSeparated X'.hom) (f : X' ⟶ X) (_ : IsFinite f.left)
      (w : W ⟶ (overRestrict X' (I.comap f.left).support.compl).left)
      (_ : IsIso w),
      IsNormalScheme X'.left ∧
      IsPullback (w ≫ (overRestrictι X' (I.comap f.left).support.compl).left) v f.left
        (overRestrictι X I.support.compl).left := by
  have := hX.1
  have : Nonempty (overRestrict X I.support.compl).left :=
    ⟨v (Classical.arbitrary W)⟩
  have hV : IsNormalScheme (overRestrict X I.support.compl).left :=
    hX.of_isOpenImmersion (overRestrictι X I.support.compl).left
  obtain ⟨-, -, hto, hfin, hint, hst, hrange⟩ := Scheme.normalization_comp_of_finite_etale X.hom
    (overRestrictι X I.support.compl).left (fun x ↦ (hV.2 x).2) v
  set φ := v ≫ (overRestrictι X I.support.compl).left
  let f : Over.mk (φ.fromNormalization ≫ X.hom) ⟶ X := Over.homMk φ.fromNormalization rfl
  have hsupp : (I.comap f.left).support.compl = φ.fromNormalization ⁻¹ᵁ I.support.compl := by
    ext1
    simp [Scheme.IdealSheafData.support_comap, f]
  obtain ⟨w, hw, -, hpb⟩ := Scheme.exists_isIso_isPullback_preimage_of_isOpenImmersion v
    φ.fromNormalization φ.toNormalization φ.toNormalization_fromNormalization (by
      rw [hrange, range_overRestrictι])
  refine ⟨Over.mk (φ.fromNormalization ≫ X.hom),
    inferInstanceAs (LocallyOfFiniteType (φ.fromNormalization ≫ X.hom)),
    inferInstanceAs (QuasiCompact (φ.fromNormalization ≫ X.hom)),
    inferInstanceAs (IsSeparated (φ.fromNormalization ≫ X.hom)), f, hfin, ?_⟩
  rw [hsupp]
  exact ⟨w, hw, ⟨hint, fun y ↦
    ⟨inferInstanceAs (IsDomain (φ.normalization.presheaf.stalk y)), hst y⟩⟩, hpb⟩

end AlgebraicGeometry
