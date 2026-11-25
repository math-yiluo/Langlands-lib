/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.NonClosedPoints
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.ClosedPoints

/-!
# Base change for open immersions of schemes of finite type over a field

Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K` and `Y` a
scheme of finite type over `K`. For the cartesian square

```
  Y ×_K U --h--> Y ×_K X
     |              |
     p              q
     v              v
     U ------j----> X
```

the exchange morphism `q⁻¹ R^i j_* F ⟶ R^i h_* p⁻¹ F` is an isomorphism for every sheaf `F` of
`Λ`-modules on `U_ét`, where `Λ` is killed by an integer `n` invertible in `K` (blueprint
`corollary-open-direct-image-over-field--2`,
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field`).

## References

- Stacks Project, Lemma 0F1H, <https://stacks.math.columbia.edu/tag/0F1H>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `corollary-open-direct-image-over-field--2`: base change for open immersions.

Let `K` be a field, `n` an integer invertible in `K` which kills `Λ`, `j : U ⟶ X` an open
immersion of schemes of finite type over `K` and `Y` a scheme of finite type over `K`. Let
`W = X ×_K Y` with projection `q₁ : W ⟶ X`, and let `V = U ×_X W` with projections
`e : V ⟶ U` and `h : V ⟶ W`. Then the exchange morphism
`q₁⁻¹ R^i j_* F ⟶ R^i h_* e⁻¹ F` is an isomorphism for every sheaf `F` of `Λ`-modules on
`U_ét` and every degree `i`. -/
@[stacks 0F1H]
theorem Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  have key : ∀ N : WithBot ℕ∞, Etale.OpenImmersionBaseChangeBelow Λ N := by
    intro N
    induction N using WellFoundedLT.induction with
    | _ N IH =>
      intro K _ X U Y W V aX aY _ _ _ _ j _ q₁ q₂ hW e h sq n hn hΛ hdim
      exact Etale.openImmersionBaseChangeAtMost_of_atNonClosed
        (Etale.openImmersionBaseChangeAtNonClosed_of_below (IH _ hdim))
        aX aY j q₁ q₂ hW e h sq n hn hΛ le_rfl
  exact Etale.openImmersionBaseChangeAtMost_of_atNonClosed
    (Etale.openImmersionBaseChangeAtNonClosed_of_below (key _))
    aX aY j q₁ q₂ hW e h sq n hn hΛ le_rfl i F

/-- Whether the degree-`q` base-change map of a cartesian square is an isomorphism does not depend
on how the pushed-forward side `g` and its base change `h` are written. -/
lemma Etale.isIso_baseChangeHomologyMap_congr_of_eq {X S T Y : Scheme.{u}} {p : X ⟶ S}
    {e : Y ⟶ T} {h₁ h₂ : Y ⟶ X} {g₁ g₂ : T ⟶ S} (hg : g₁ = g₂) (hh : h₁ = h₂)
    (sq₁ : IsPullback e h₁ g₁ p) (sq₂ : IsPullback e h₂ g₂ p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₁ q F) ↔
      IsIso (Etale.baseChangeHomologyMap Λ sq₂ q F) := by
  subst hg hh
  rfl

/-- Base change for an arbitrary separated morphism of finite type between schemes of finite
type over a field, deduced from blueprint `corollary-open-direct-image-over-field--2`.

Let `K` be a field, `n` an integer invertible in `K` which kills `Λ`, `j : U ⟶ X` a separated
quasi-compact morphism locally of finite type, `X` and `Y` of finite type over `K`, `W = X ×_K Y`
and `V = U ×_X W`. Then the exchange morphism `q₁⁻¹ R^i j_* F ⟶ R^i h_* e⁻¹ F` is an isomorphism
for every sheaf `F` of `Λ`-modules on `U_ét` and every degree `i`.

Write `j = i ≫ g` with `i` an open immersion and `g` proper (Nagata compactification,
`AlgebraicGeometry.NagataCompactification`). The derived exchange morphism of the square on `j`
is the vertical pasting of the one for `g`, an isomorphism by proper base change
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`), and the one for
`i`, an isomorphism at `F` by blueprint `corollary-open-direct-image-over-field--2`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_field {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let c := NagataCompactification j
  have hj : j = c.i ≫ c.g := c.comm
  have sq₂ : IsPullback (pullback.fst c.g q₁) (pullback.snd c.g q₁) c.g q₁ :=
    IsPullback.of_hasPullback c.g q₁
  have hw : (e ≫ c.i) ≫ c.g = h ≫ q₁ := by rw [Category.assoc, ← hj, sq.w]
  let l : V ⟶ pullback c.g q₁ := pullback.lift (e ≫ c.i) h hw
  have hl₁ : l ≫ pullback.fst c.g q₁ = e ≫ c.i := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd c.g q₁ = h := pullback.lift_snd _ _ _
  have sq' : IsPullback e (l ≫ pullback.snd c.g q₁) (c.i ≫ c.g) q₁ := by
    rw [hl₂, ← hj]
    exact sq
  have sq₁ : IsPullback e l c.i (pullback.fst c.g q₁) := IsPullback.of_bot sq' hl₁.symm sq₂
  rw [Etale.isIso_baseChangeHomologyMap_congr_of_eq Λ hj hl₂.symm sq sq']
  revert i
  rw [← Etale.isIso_baseChange_app_singleFunctor_obj_iff]
  -- the open immersion part, by blueprint `corollary-open-direct-image-over-field--2`
  have hW' : IsPullback (pullback.fst c.g q₁) (pullback.snd c.g q₁ ≫ q₂) (c.g ≫ aX) aY :=
    sq₂.paste_vert hW
  have h₁ : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
    rw [Etale.isIso_baseChange_app_singleFunctor_obj_iff]
    exact fun i ↦ Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field Λ (c.g ≫ aX) aY
      c.i _ _ hW' e l sq₁ n hn hΛ i F
  -- the proper part, by proper base change
  have hΛt : IsAddTorsion Λ := fun x ↦ by
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨n, Nat.pos_of_ne_zero hn0, by rw [nsmul_eq_mul, hΛ, zero_mul]⟩
  have h₂ := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛt sq₂
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at h₁ h₂ ⊢
  rw [NatTrans.congr_app (Etale.derivedBaseChangeMapPlus_paste_vert _ sq₁.toCommSq
    sq₂.toCommSq sq'.toCommSq) _]
  dsimp
  infer_instance

end AlgebraicGeometry
