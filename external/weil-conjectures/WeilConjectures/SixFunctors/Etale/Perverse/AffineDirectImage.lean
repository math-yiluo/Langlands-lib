/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.ArtinVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Perverse.AffinePushforward

/-!
# The support estimate for an affine direct image

Let `f : X ⟶ Y` be an affine morphism of finite type to a separated scheme of finite type over a
field. For a constructible sheaf `G` on `X` whose support has dimension at most `N`, the stalks
of `Rᵠf_* G` vanish at every point `y` with `q + dim {y}⁻ > N` (Stacks `0F0X`). Combined with the
dévissage of
`AlgebraicGeometry.Etale.DerivedCategory.supportCondition_shift_rightDerivedLowerStar_of_stalk`
this is the support estimate for `Rf_*` entering the cosupport side of Artin–Gabber
(blueprint `lem-per-artin-gabber-affine-curve`, Step 3).

## Main statements

- `AlgebraicGeometry.Etale.supportEstimate_upperStar_homology_rightDerivedLowerStar`: the
  pointwise estimate, in the form taken by the dévissage.
- `AlgebraicGeometry.Etale.DerivedCategory.supportCondition_shift_rightDerivedLowerStar`: for a
  bounded constructible `K` with `K[n]` satisfying the support condition, so does
  `(Rf_* K)[n + d]` for every `d ≥ 0`.

## Implementation notes

The relative affine vanishing theorem is
`AlgebraicGeometry.Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom`, for a source of
dimension at most `N`. To apply it to `G`, write `G[0] ≅ Ri_* (i^* G)[0]` for the closed
immersion `i` of the support of `G` (the open-closed triangle), so that
`Rf_* G[0] ≅ R(i ≫ f)_* (i^* G)[0]`. Since `Rᵠf_* G` is constructible, a vanishing stalk at
the geometric point `Y.algClosurePoint y` forces the vanishing at every geometric point over `y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- **Pointwise support estimate for an affine direct image** (Stacks `0F0X`). Let
`f : X ⟶ Y` be an affine morphism of finite type to a separated scheme of finite type over a
field, `G` a constructible sheaf on `X` and `s : Spec Ω ⟶ Y` a geometric point over `y ∈ Y`. If
`s^* Rᵠf_* G ≠ 0`, then the support of `G` is nonempty and, whenever it has dimension at most
`N`, `q ≤ N` and `dim {y}⁻ ≤ N - q`. (blueprint: `lem-per-artin-gabber-affine-curve`) -/
theorem supportEstimate_upperStar_homology_rightDerivedLowerStar {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) (q : ℤ)
    (hs : ¬ IsZero (((s)^*[ModuleCat.{u + 1} Λ]).obj
      ((homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj G))))) :
    (sheafSupport G).Nonempty ∧ ∀ N : ℕ, topologicalKrullDim (sheafSupport G) ≤ (N : ℕ∞) →
      q ≤ N ∧ topologicalKrullDim (closure {s.base (IsLocalRing.closedPoint Ω)} : Set Y) ≤
        ((N - q).toNat : ℕ∞) := by
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
  set y := s.base (IsLocalRing.closedPoint Ω)
  let K := (singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj G
  let H := (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)
  have : IsConstructibleSheaf H :=
    (boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ f (f ≫ aY) aY rfl K
      (DerivedCategory.boundedConstructible_singleFunctor_obj G 0)).2 q
  -- the stalk of `H` at `y` is nonzero, `H` being constructible
  have hy : ¬ IsZero ((Y.uliftPointSmallEtale y).sheafFiber.obj H) := by
    intro h
    have h' : IsZero ((pointSmallEtale (Y.algClosurePoint y)).sheafFiber.obj H) :=
      h.of_iso (((pointSmallEtale (Y.algClosurePoint y)).uliftSheafFiberIso _).app H).symm
    have hm := mem_stalkZeroLocus_of_isZero_sheafFiber H _ h'
    rw [Y.algClosurePoint_base] at hm
    refine hs ((isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun x ↦ ?_))
    refine mem_stalkZeroLocus_upperStar s H ?_
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint Ω)]
  -- the support of `G` is nonempty
  have hne : (sheafSupport G).Nonempty := by
    by_contra hG
    rw [Set.not_nonempty_iff_eq_empty] at hG
    have hG0 : IsZero G := by
      refine (isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun x ↦ ?_)
      by_contra hx
      simpa [hG] using compl_stalkZeroLocus_subset_sheafSupport G hx
    exact hy ((Y.uliftPointSmallEtale y).sheafFiber.map_isZero ((homologyFunctor _ q).map_isZero
      ((R((f)_*[ModuleCat.{u + 1} Λ])).map_isZero ((singleFunctor _ 0).map_isZero hG0))))
  refine ⟨hne, fun N hN ↦ ?_⟩
  -- `q ≥ 0`
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := by
    refine ⟨q.toNat, ?_⟩
    by_contra hq
    have := ((f)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor G
    exact hy ((Y.uliftPointSmallEtale y).sheafFiber.map_isZero
      (_root_.DerivedCategory.isZero_of_isGE _ 0 q (by lia)))
  -- the closed immersion of the support of `G`
  let V : X.Opens := ⟨(sheafSupport G)ᶜ, (isClosed_sheafSupport G).isOpen_compl⟩
  let i := V.closedComplement
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by simp [i]
  have hi : Set.range i.base = sheafSupport G := by
    rw [hij, Scheme.Opens.range_ι]
    simp [V]
  have hK : IsZero (D((V.ι)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    ((singleFunctor _ 0).map_isZero (isZero_upperStar_of_disjoint_sheafSupport G V
      disjoint_compl_left)).of_iso
      ((((V.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G)
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) V.ι i hij K
  have : IsIso ((mapDerivedUpperStarLowerStarAdjunction _ i).unit.app K) :=
    (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hw).1
      (D((V.ι)_!open[ModuleCat.{u + 1} Λ]).map_isZero hK)
  let G' := ((i)^*[ModuleCat.{u + 1} Λ]).obj G
  let eK : K ≅ (R((i)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj G') :=
    asIso ((mapDerivedUpperStarLowerStarAdjunction _ i).unit.app K) ≪≫
      (R((i)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G)
  let eH : H ≅ higherDirectImage Λ (i ≫ f) n G' :=
    (homologyFunctor _ n).mapIso ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso eK ≪≫
      (rightDerivedLowerStarComp _ i f).app _) ≪≫
      homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ (i ≫ f) G' n
  -- the dimension of the support scheme
  have hZ : topologicalKrullDim (IdealSheafData.vanishingIdeal
      ⟨((V : Set X))ᶜ, V.isOpen.isClosed_compl⟩).subscheme ≤ (N : WithBot ℕ∞) := by
    refine le_trans ?_ hN
    let ρ : _ → (sheafSupport G : Set X) := fun z ↦ ⟨i.base z, hi ▸ Set.mem_range_self _⟩
    exact Topology.IsInducing.topologicalKrullDim_le (f := ρ)
      (.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val
        i.isClosedEmbedding.isInducing)
  -- the dimension of the closure of `y`
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_locallyOfFiniteType aY
  have : Nonempty (closure {y} : Set Y) := ⟨⟨y, subset_closure rfl⟩⟩
  obtain ⟨r, -, hr⟩ := exists_topologicalKrullDim_eq_natCast (X := (closure {y} : Set Y))
    ((Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le).trans hd)
  have hle : (n : ℤ) + r ≤ N := by
    by_contra hlt
    exact hy ((isZero_sheafFiber_higherDirectImage_of_isAffineHom Λ (i ≫ f) aY G' N hZ y r hr n
      (by lia)).of_iso ((Y.uliftPointSmallEtale y).sheafFiber.mapIso eH))
  refine ⟨by lia, ?_⟩
  rw [hr]
  exact_mod_cast (by lia : r ≤ ((N : ℤ) - n).toNat)

/-- **Support estimate for an affine direct image.** Let `f : X ⟶ Y` be an affine morphism of
finite type to a separated scheme of finite type over a field. For a bounded constructible `K`
with `K[n]` satisfying the support condition, `(Rf_* K)[n + d]` satisfies the support condition
for every `d ≥ 0`. This is the input of the cosupport side of Artin–Gabber.
(blueprint: `lem-per-artin-gabber-affine-curve`, Step 3) -/
theorem DerivedCategory.supportCondition_shift_rightDerivedLowerStar {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f] (d : ℕ) {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.SupportCondition (K⟦n⟧))
    (hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.SupportCondition (((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)⟦n + d⟧) :=
  DerivedCategory.supportCondition_shift_rightDerivedLowerStar_of_stalk aY f
    (fun G _ _ _ _ s q hs ↦ supportEstimate_upperStar_homology_rightDerivedLowerStar aY f G s q hs)
    d hK hK'

end AlgebraicGeometry.Etale
