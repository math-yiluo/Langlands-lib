/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Gabber
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Vanishing of the higher direct images above twice the dimension

Let `k` be a separably closed field, `f : X ⟶ Y` a morphism of finite type between `k`-schemes
locally of finite type, with `dim X ≤ d`, and `Λ` a finite ring. Then `R^q f_* M = 0` for every
`q > 2d` and every étale sheaf `M` of `Λ`-modules on `X`
(`AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`, blueprint
`theorem-results-from-etale-theory--4`).

The proof follows the blueprint. The sheaf `R^q f_* M` is the sheafification of the presheaf
`W ↦ H^q(W ×_Y X, M|)` on `Y_ét`
(`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`),
so it suffices that these groups vanish for affine `W`. Then `W ×_Y X` is a `k`-scheme of finite
type, étale over `X`, hence of dimension at most `d`, and its torsion cohomological dimension is
at most `2d` (`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`, blueprint
`sk-prop-sf-finiteness`, the case `c = 0` of the bound `cd_tor(X) ≤ 2d + c` of
`lemma-uniform-bounds-pro-etale-affines`). That bound is stated for abelian sheaves; it is
transported to sheaves of `Λ`-modules by dimension shifting
(`AlgebraicGeometry.Etale.subsingleton_ext_freeSheaf_of_subsingleton_H`), using that the
underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`).

## Main definitions

- `AlgebraicGeometry.Etale.HasUniformDirectImageVanishingLE`: the bound `UDV(f, Λ; N)` of
  blueprint `definition-cohomological-dimension--2`.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_ext_freeSheaf_of_subsingleton_H`: the cohomology of a
  sheaf of `Λ`-modules over an étale `X`-scheme `V` vanishes in a degree where the abelian
  cohomology of its underlying abelian sheaf restricted to `V` does.
- `AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`: blueprint
  `theorem-results-from-etale-theory--4`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `definition-cohomological-dimension--2`: Uniform vanishing of the higher direct
images.

`UDV(f, Λ; N)` holds if the higher direct images of `f` on the small étale sites vanish above
`N` for every sheaf of `Λ`-modules: `R^q f_* M = 0` for every `q > N` and every étale sheaf `M`
of `Λ`-modules on `X`. -/
def Etale.HasUniformDirectImageVanishingLE {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), (N : ℤ) < q →
    IsZero (Etale.higherDirectImage Λ f q M)

variable {Λ} in
/-- **Cohomology of sheaves of `Λ`-modules versus abelian sheaf cohomology.** Let `Λ` be a finite
ring, `V` an étale `X`-scheme and `F` an étale sheaf of `Λ`-modules on `X`. If the underlying
abelian sheaf of the restriction of `F` to `V` has no cohomology in degree `n + 1`, then
`Ext^{n + 1}(Λ[V], F) = 0`, that is `H^{n + 1}(V, F|) = 0` computed with sheaves of `Λ`-modules.

This is dimension shifting (`CategoryTheory.Abelian.Ext.subsingleton_of_subsingleton_map`): the
underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`), and in degree one both groups
measure the failure of sections over `V` to lift. -/
theorem Etale.subsingleton_ext_freeSheaf_of_subsingleton_H [Finite Λ] {X : Scheme.{u}}
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (hF : Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj F)) (n + 1))) :
    Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ X).obj V) F (n + 1)) :=
  Etale.subsingleton_ext_freeSheaf_of_subsingleton_H_of_acyclic V F n
    (fun I _ m ↦ Sheaf.subsingleton_H_forget₂_of_injective.{u + 1, u + 1, u, u + 1} Λ I m) hF

/-- Blueprint `theorem-results-from-etale-theory--4`: Vanishing of the higher direct images above
the dimension.

Let `k` be a separably closed field, `f : X ⟶ Y` a morphism of finite type between `k`-schemes
locally of finite type with `dim X ≤ d`, and `Λ` a finite ring. Then `R^q f_* M = 0` for every
`q > 2d` and every étale sheaf `M` of `Λ`-modules on `X`: `UDV(f, Λ; 2d)` holds. Separatedness of
`f` is not needed.

The blueprint assumes `k` algebraically closed and `Λ` annihilated by an integer invertible in
`k`; neither is needed for the argument, whose input is the torsion cohomological dimension
bound `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`. For an affine
étale `W ⟶ Y`, the scheme `W ×_Y X` is of finite type over `k` and étale over `X`, hence of
dimension at most `d`, so its cohomology vanishes above `2d`; and `R^q f_* M` is the
sheafification of these groups. -/
theorem Etale.hasUniformDirectImageVanishingLE_two_mul [Finite Λ] {k : Type u} [Field k]
    [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    (hf : f ≫ aY = aX) (d : ℕ) (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    Etale.HasUniformDirectImageVanishingLE Λ f (2 * d) := by
  intro M q hq
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
  refine Etale.isZero_higherDirectImage_of_forall_isAffine f _ M fun W hW ↦ ?_
  let V := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  have hV : AlgebraicGeometry.Etale V.hom := V.prop
  -- the cohomology of the restriction of `M` to `V = W ×_Y X` vanishes above `2d`
  have hcd : Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M)) (n + 1)) := by
    have : CompactSpace ((𝟭 Scheme.{u}).obj W.left) := by
      change CompactSpace W.left
      infer_instance
    have : CompactSpace ((𝟭 Scheme.{u}).obj V.left) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst W.hom f)
    have : QuasiCompact (V.hom ≫ aX) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance
    have : LocallyOfFiniteType aX := hf ▸ inferInstance
    refine Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d (V.hom ≫ aX)
      ((V.hom.topologicalKrullDim_le_of_etale).trans hX) _ ?_ (n + 1) (by omega)
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
    have := Fintype.ofFinite Λ
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Fintype.card Λ, Fintype.card_pos, ?_⟩
    let y : ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M).obj.obj U := x
    change Fintype.card Λ • y = 0
    rw [← one_smul Λ y, ← smul_assoc, card_nsmul_eq_zero, zero_smul]
  have : Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ X).obj V) M (n + 1)) :=
    Etale.subsingleton_ext_freeSheaf_of_subsingleton_H V M n hcd
  exact ((DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1}
    ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ Y).obj W)) M (n + 1)).trans
    (Abelian.Ext.precompAddEquiv (Etale.upperStarFreeSheafIso Λ f W) M (n + 1)).symm.toEquiv
    ).subsingleton

open ZeroObject in
/-- **Higher direct images of base changes of a proper morphism.** Let `k` be separably closed,
`p : X' ⟶ Y` a proper morphism of `k`-schemes locally of finite type with `dim X' ≤ d`, and `Λ` a
finite ring. For the base change `p' : X'' ⟶ Y''` of `p` along an arbitrary `g : Y'' ⟶ Y` and
every étale sheaf `F` of `Λ`-modules on `X''`, `R^r p'_* F = 0` for `r > 2d`.

This is the étale part of blueprint `sk-prop-sf-fullcd-etale-origin`. Vanishing is tested after
pullback to the geometric points `t : Spec Ω ⟶ Y''`
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`); by proper base
change (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`)
`t^* R^r p'_* F ≅ R^r h_* (F|)` for the fibre `h : X'' ×_{Y''} Spec Ω ⟶ Spec Ω`, which is a
`Ω`-scheme of finite type of dimension at most `d`
(`AlgebraicGeometry.topologicalKrullDim_pullback_le`), so that
`AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul` applies. -/
theorem Etale.isZero_higherDirectImage_of_isPullback_of_isProper [Finite Λ] {k : Type u}
    [Field k] [IsSepClosed k] {X' Y X'' Y'' : Scheme.{u}} (p : X' ⟶ Y) [IsProper p]
    (aX' : X' ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX']
    (hp : p ≫ aY = aX') (d : ℕ) (hd : topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    {g' : X'' ⟶ X'} {p' : X'' ⟶ Y''} {g : Y'' ⟶ Y} (sq : IsPullback g' p' p g)
    (F : Sheaf X''.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : ℤ) (hr : (2 * d : ℤ) < r) :
    IsZero (Etale.higherDirectImage Λ p' r F) := by
  have : IsProper p' := MorphismProperty.of_isPullback sq inferInstance
  have : LocallyOfFiniteType p := by
    subst hp
    exact locallyOfFiniteType_of_comp p aY
  let G := Etale.higherDirectImage Λ p' r F
  suffices H : ∀ y : Y'', IsZero ((Y''.algClosurePoint y)^*[ModuleCat.{u + 1} Λ].obj G) by
    have hz : IsZero (0 : Sheaf Y''.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := isZero_zero _
    have : IsIso (hz.from_ G) := by
      refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (fun y ↦ Y''.algClosurePoint y)
        (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
        fun y ↦ ?_
      have hz' : IsZero ((Y''.algClosurePoint y)^*[ModuleCat.{u + 1} Λ].obj 0) :=
        Functor.map_isZero _ hz
      exact ⟨⟨hz'.to_ _, (H y).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
    exact IsZero.of_iso hz (asIso (hz.from_ G))
  intro y
  let t := Y''.algClosurePoint y
  let sq' := IsPullback.of_hasPullback p' t
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq'
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  -- the geometric fibre has dimension at most `d`
  have hdim : topologicalKrullDim (pullback p' t : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
    let e := (sq'.paste_horiz sq).isoPullback
    rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_pullback_le p (t ≫ g)).trans hd
  have hvan := Etale.hasUniformDirectImageVanishingLE_two_mul Λ (pullback.snd p' t)
    (pullback.snd p' t) (𝟙 _) (Category.comp_id _) d hdim
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p' t)).obj F) r hr
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  refine IsZero.of_iso hvan
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) t).mapDerivedCategoryPlusHomologyFunctorIso r).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p').rightDerivedFunctorPlus.obj K) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ r).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq'.toCommSq).app K)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ r).mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd p' t)).rightDerivedFunctorPlus.mapIso
          (((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst p' t)).mapDerivedCategoryPlusSingleFunctor 0).app F)))

end AlgebraicGeometry
