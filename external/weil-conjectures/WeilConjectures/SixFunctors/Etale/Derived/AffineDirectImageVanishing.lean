/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing

/-!
# Vanishing of the higher direct images along an affine morphism above the dimension

Let `K` be a separably closed field, `h : T ⟶ Y` an affine morphism whose source is a
`K`-scheme of finite type of dimension at most `e`, and `Λ` a finite ring. Then `R^q h_* M = 0`
for every `q > e` and every étale sheaf `M` of `Λ`-modules on `T`
(`AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_of_isAffineHom`).

The proof is that of `AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`, with
the affine bound `lemma-uniform-bounds-pro-etale-affines` in place of the finite-type bound: for an
affine `W` étale over `Y`, the scheme `W ×_Y T` is affine, of finite type over `K` and étale over
`T`, hence of dimension at most `e`, so its cohomology vanishes above `e`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Higher direct images along an affine morphism from a scheme over a separably closed
field.** Let `K` be separably closed, `h : T ⟶ Y` affine with `T` of finite type over `K` and
`dim T ≤ e`, and `Λ` a finite ring. Then `R^q h_* M = 0` for every `q > e` and every étale sheaf
`M` of `Λ`-modules on `T`: `UDV(h, Λ; e)` holds. For an affine `W` étale over `Y`, the scheme
`W ×_Y T` is affine, of finite type over `K` and étale over `T`, so its cohomology vanishes
above `e` by the affine bound `lemma-uniform-bounds-pro-etale-affines`
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`, with `c = 0`); and
`R^q h_* M` is the sheafification of these groups. -/
theorem Etale.hasUniformDirectImageVanishingLE_of_isAffineHom [Finite Λ] {K : Type u} [Field K]
    [IsSepClosed K] {T Y : Scheme.{u}} (h : T ⟶ Y) [IsAffineHom h] (aT : T ⟶ Spec (.of K))
    [LocallyOfFiniteType aT] (e : ℕ) (hT : topologicalKrullDim T ≤ (e : WithBot ℕ∞)) :
    Etale.HasUniformDirectImageVanishingLE Λ h e := by
  intro M q hq
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
  refine Etale.isZero_higherDirectImage_of_forall_isAffine h _ M fun W hW ↦ ?_
  let V := (MorphismProperty.Over.pullback @Etale ⊤ h).obj W
  have hV : AlgebraicGeometry.Etale V.hom := V.prop
  -- the cohomology of the restriction of `M` to `V = W ×_Y T` vanishes above `e`
  have hcd : Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M)) (n + 1)) := by
    have : IsAffine ((𝟭 Scheme.{u}).obj W.left) := hW
    have : IsAffineHom (pullback.fst W.hom h) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback W.hom h).flip inferInstance
    have : IsAffine ((𝟭 Scheme.{u}).obj V.left) := by
      change IsAffine (pullback W.hom h)
      exact isAffine_of_isAffineHom (pullback.fst W.hom h)
    refine Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine
      (Scheme.hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K) (V.hom ≫ aT)
      ((V.hom.topologicalKrullDim_le_of_etale).trans hT) _ ?_ (n + 1) (by omega)
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
    have := Fintype.ofFinite Λ
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Fintype.card Λ, Fintype.card_pos, ?_⟩
    let y : ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M).obj.obj U := x
    change Fintype.card Λ • y = 0
    rw [← one_smul Λ y, ← smul_assoc, card_nsmul_eq_zero, zero_smul]
  have : Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ T).obj V) M (n + 1)) :=
    Etale.subsingleton_ext_freeSheaf_of_subsingleton_H V M n hcd
  exact ((DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1}
    ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ Y).obj W)) M (n + 1)).trans
    (Abelian.Ext.precompAddEquiv (Etale.upperStarFreeSheafIso Λ h W) M (n + 1)).symm.toEquiv
    ).subsingleton

end AlgebraicGeometry
