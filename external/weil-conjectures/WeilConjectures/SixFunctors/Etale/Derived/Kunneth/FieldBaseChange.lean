/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.BaseChangeUniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldBaseChangeNormal

/-!
# Base change towards spectra of fields

Let `K` be a field and `X` a scheme of finite type over `K`. We show that the structure morphism
`a : X ⟶ Spec K` satisfies the base-change property `BC(a, Λ, q)` universally, in every degree
`q`, for a coefficient ring `Λ` killed by an integer `n` invertible in `K`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`, blueprint
`lemma-kunneth-field-coefficients--1`): for every base change `X' = X ×_K S' ⟶ S'`, every
quasi-compact quasi-separated `g : T ⟶ S'` and every sheaf `F` of `Λ`-modules on `T_ét`, the
exchange morphism `p'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism.

The proof is an induction on `q`, as for the smooth base change theorem
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one`):

* in degree zero, after replacing `K` by its perfect closure and `X` by its reduction (étale
  cohomology is invariant under universal homeomorphisms) the morphism is flat, of finite
  presentation, with geometrically reduced fibres, and the degree-zero base change theorem
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero` applies;
* in degree `q ≥ 1`, a first failure is witnessed, by
  `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage` (Stacks 0F08), by a
  nonzero higher direct image `R^q h_* (Λ/dΛ)` along the geometric generic fibre `h` of a base
  change of `a` to an affine integral scheme with algebraically closed function field; this
  higher direct image vanishes by blueprint `lemma-kunneth-finite-direct-image--1`
  (`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed`).

## Main statements

- `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`: degree zero.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed`
  (`lemma-kunneth-finite-direct-image--1`).
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`
(`lemma-kunneth-field-coefficients--1`).

## References

- Stacks Project, Lemma 0F1I, <https://stacks.math.columbia.edu/tag/0F1I>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Degree zero of blueprint `lemma-kunneth-field-coefficients--1`: for a scheme `X` locally of
finite type over a field `K`, the structure morphism `a : X ⟶ Spec K` satisfies the degree-zero
base-change property universally, for every coefficient ring.

After the base change to the perfect closure of `K` and the passage to the reduction, both
universal homeomorphisms which do not change the étale sites, the morphism is flat, locally of
finite presentation and has geometrically reduced fibres (blueprint
`lemma-kunneth-finite-direct-image--1`), so that the degree-zero base change theorem (blueprint
`lemma-kunneth-finite-direct-image--1`, `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`)
applies. -/
theorem Etale.universalBaseChangeProperty_zero_of_field {K : Type u} [Field K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] :
    Etale.UniversalBaseChangeProperty Λ a 0 := by
  let Kp := perfectClosure K (AlgebraicClosure K)
  let π : Spec (.of Kp) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kp))
  have : IsUniversalHomeomorphism π :=
    Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism
  have hpb : IsPullback (pullback.fst a π) (pullback.snd a π) a π := IsPullback.of_hasPullback a π
  refine Etale.UniversalBaseChangeProperty.of_isPullback_of_isUniversalHomeomorphism hpb ?_
  obtain ⟨_, _, _, -⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism (pullback a π)
  refine Etale.UniversalBaseChangeProperty.of_comp_isUniversalHomeomorphism
    (pullback a π).nilradical.subschemeι ?_
  have : GeometricallyReduced ((pullback a π).nilradical.subschemeι ≫ pullback.snd a π) :=
    GeometricallyReduced.of_perfectField _
  exact Etale.universalBaseChangeProperty_zero Λ _

/-- Blueprint `lemma-kunneth-field-coefficients--1`: base change towards spectra of fields.

Let `K` be a field, `X` a scheme of finite type over `K` with structure morphism
`a : X ⟶ Spec K`, and `n` an integer invertible in `K` which kills the coefficient ring `Λ`.
Then `BC(a, Λ, q)` holds universally in every degree `q`: for every base change
`p' : X' = X ×_K S' ⟶ S'`, every quasi-compact quasi-separated `g : T ⟶ S'` and every sheaf `F`
of `Λ`-modules on `T_ét`, the exchange morphism `p'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` for the
cartesian square `Y = X' ×_{S'} T` is an isomorphism.

The proof is an induction on `q`: degree zero is
`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`, and a first failure in
degree `q ≥ 1` would produce, by
`AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage` (blueprint
`lemma-kunneth-finite-direct-image--1`), a nonzero higher direct image which vanishes by
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed`. -/
@[stacks 0F1I]
theorem Etale.universalBaseChangeProperty_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (n : ℕ)
    (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0) (q : ℤ) :
    Etale.UniversalBaseChangeProperty Λ a q := by
  have hn' : IsUnit (n : Γ(Spec (.of K), ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (.of K)).inv.hom
  have key : ∀ m : ℕ, ∀ q' < (m : ℤ), Etale.UniversalBaseChangeProperty Λ a q' := by
    intro m
    induction m with
    | zero => exact fun q' hq' ↦ Etale.universalBaseChangeProperty_of_neg Λ a hq'
    | succ m ih =>
      intro q' hq'
      rcases lt_or_eq_of_le (show q' ≤ m by omega) with h | rfl
      · exact ih q' h
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact Etale.universalBaseChangeProperty_zero_of_field Λ a
        · by_contra hfail
          obtain ⟨S', X', s, b, p', hpb, _, _, hnorm, _, L, _, _, i, Y, e, h, sq, d, hd, hne⟩ :=
            Etale.exists_isPullback_not_isZero_higherDirectImage Λ a n hn' hΛ m (by omega) ih
              hfail
          exact hne (Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed Λ a n hn hΛ
            s b p' hpb hnorm i e h sq d hd m (by omega))
  exact key (q.toNat + 1) q (by omega)

end AlgebraicGeometry
