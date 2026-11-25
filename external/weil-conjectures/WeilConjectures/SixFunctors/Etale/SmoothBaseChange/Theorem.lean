/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction

/-!
# The smooth base change theorem

Fix a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` **smooth** and `g` quasi-compact quasi-separated. For every sheaf `F` of
`Λ`-modules on `T_ét` all of whose geometric stalks are torsion of orders invertible on `S`
— that is, `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder` — the base-change map

`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`

of `AlgebraicGeometry.Etale.baseChangeHomologyMap` is an isomorphism in every degree `q`.

The proof is the second, shorter proof of the Stacks Project.

- In negative degrees both sides vanish
  (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_neg`).
- *Filtered torsion*: `F` is a filtered colimit of sheaves killed by integers `n` invertible
  on `S`, and both sides of the base-change map commute with filtered colimits
  (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_forall_nsmul_eq_zero`); a sheaf
  killed by `n` is a sheaf of `Λ/nΛ`-modules
  (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero`), so it suffices to
  prove the base-change property `BC(p, Λ, q)` for a coefficient ring `Λ` in which `n = 0`.
- *Reduction to relative dimension one*: the property is étale local on `X` and `S`
  (`AlgebraicGeometry.Etale.BaseChangeProperty.of_etale_cover`); by the étale-local normal
  form `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`, `X ⟶ S` is locally an étale
  morphism to `𝔸^d_S` followed by the projection, which is the composite of the `d` relative
  lines `𝔸^{k+1}_S ⟶ 𝔸^k_S`; by `AlgebraicGeometry.Etale.BaseChangeProperty.comp` it suffices
  to treat affine smooth morphisms of relative dimension one with affine source
  (`AlgebraicGeometry.Etale.baseChangeProperty_of_smooth_of_relativeDimension_one`).
- *Induction on `q`*: for those,
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one` gives
  the base-change property after every base change, by strong induction on `q` on
  `AlgebraicGeometry.Etale.UniversalBaseChangeProperty` with step
  `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt`, starting from
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_neg` and
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_smooth`. The induction has to
  run on the universal property, since its step consumes the hypothesis after a preliminary
  base change; the proof ends by specialising along `𝟙 S` with
  `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.baseChangeProperty`.

Compare `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`,
the proper base change
theorem, in which the roles of the two legs of the square are exchanged.

The seams of the argument (blueprint `sk-rem-seams`, `rem-seams`): a first failure in degree `q`
produces a universal curve-test datum with `R^q h_* (ℤ/dℤ) ≠ 0`
(`AlgebraicGeometry.Etale.exists_curveTestDatum`), while the curve-test lane makes this sheaf
vanish (`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`), using
the field-extension invariance, the torsor translation and the spreading of Galois covers in
degree one only. These are Stacks 0F06, 0F07, 0F08 and the theorem is Stacks 0EYU.

## Main statements

- `AlgebraicGeometry.Etale.baseChangeProperty_of_smooth_of_relativeDimension_one`: the
  reduction of the base-change property for smooth morphisms to relative dimension one.
- `AlgebraicGeometry.Etale.baseChangeProperty_of_smooth`: the base-change property
  `BC(p, Λ, q)` for `p` smooth, when an integer invertible on the base vanishes in `Λ`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`: the smooth base change
  theorem.

## References

- Stacks Project, Étale Cohomology, Theorem 59.89.2,
  <https://stacks.math.columbia.edu/tag/0EYU>
- [SGA 4, Exp. XVI]
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S T Y : Scheme.{u}}

/-- The base-change property `BC(ε ≫ π, Λ, q)` for an étale morphism `ε : V ⟶ 𝔸^d_U` followed
by the projection `π : 𝔸^d_U ⟶ U`, with `U` and `V` affine and `n` invertible on `U`, provided
the property holds for all affine smooth morphisms of relative dimension one with affine source
and with `n` invertible on the target. By induction on `d`: for `d = 0` the morphism is étale
and étale locality reduces it to the identity; for `d + 1` write `π` as the relative line
`𝔸^{d+1}_U ⟶ 𝔸^d_U` followed by `𝔸^d_U ⟶ U`, and use stability under composition. -/
theorem Etale.baseChangeProperty_comp_affineSpace (n : ℕ) (q : ℤ)
    (H : ∀ ⦃X' S' : Scheme.{u}⦄ (p' : X' ⟶ S') [IsAffine X'] [IsAffineHom p']
      [SmoothOfRelativeDimension 1 p'], IsUnit (n : Γ(S', ⊤)) →
        Etale.BaseChangeProperty Λ p' q)
    (d : ℕ) {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (hn : IsUnit (n : Γ(U, ⊤)))
    (ε : V ⟶ 𝔸(ULift.{u} (Fin d); U)) [Etale ε] :
    Etale.BaseChangeProperty Λ (ε ≫ 𝔸(ULift.{u} (Fin d); U) ↘ U) q := by
  induction d generalizing V with
  | zero =>
    intro T Y g e h _ _ sq F
    exact Etale.BaseChangeProperty.of_etale_cover Λ (ι := PUnit) (U := fun _ ↦ V)
      (V := fun _ ↦ V) (fun _ ↦ 𝟙 V) (fun x ↦ ⟨⟨⟩, x, rfl⟩) (fun _ ↦ 𝟙 V)
      (fun _ ↦ ε ≫ 𝔸(ULift.{u} (Fin 0); U) ↘ U) (fun _ ↦ by simp)
      (fun _ ↦ Etale.baseChangeProperty_of_isIso Λ (𝟙 V) q) g e h sq F
  | succ d ih =>
    let r := AffineSpace.reindex
      (fun i : ULift.{u} (Fin d) ↦ (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) U
    have : SmoothOfRelativeDimension (0 + 1) (ε ≫ r) := inferInstance
    have : SmoothOfRelativeDimension 1 (ε ≫ r) := by simpa using this
    have hr : ε ≫ 𝔸(ULift.{u} (Fin (d + 1)); U) ↘ U =
        (ε ≫ r) ≫ 𝔸(ULift.{u} (Fin d); U) ↘ U := by
      simp [r]
    have h₂ : Etale.BaseChangeProperty Λ (𝔸(ULift.{u} (Fin d); U) ↘ U) q := by
      have := @ih 𝔸(ULift.{u} (Fin d); U) _ (𝟙 _) _
      rwa [Category.id_comp] at this
    rw [hr]
    intro T Y g e h _ _ sq F
    exact Etale.BaseChangeProperty.comp Λ
      (H (ε ≫ r) (by simpa using hn.map (𝔸(ULift.{u} (Fin d); U) ↘ U).appTop.hom)) h₂ g e h sq F

/-- Reduction of the smooth base change theorem to relative dimension one.

Let `n` be invertible on `S`. If the base-change property `BC(p', Λ, q)` holds for every affine
smooth morphism `p' : X' ⟶ S'` of relative dimension one with `X'` affine and `n` invertible
on `S'`, then it holds for every smooth `p : X ⟶ S`. The property is étale local on `X` and
`S`, and locally on `X` and `S` a smooth morphism is an étale morphism to an affine space
followed by the projection. -/
theorem Etale.baseChangeProperty_of_smooth_of_relativeDimension_one (n : ℕ) (q : ℤ)
    (H : ∀ ⦃X' S' : Scheme.{u}⦄ (p' : X' ⟶ S') [IsAffine X'] [IsAffineHom p']
      [SmoothOfRelativeDimension 1 p'], IsUnit (n : Γ(S', ⊤)) →
        Etale.BaseChangeProperty Λ p' q)
    (p : X ⟶ S) [Smooth p] (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale.BaseChangeProperty Λ p q := by
  have key : ∀ x : X, ∃ (U₁ : S.Opens) (V₁ : X.Opens) (U₂ : U₁.toScheme.Opens)
      (V₂ : V₁.toScheme.Opens) (f : V₂.toScheme ⟶ U₂.toScheme),
      (∃ y : V₂.toScheme, (V₂.ι ≫ V₁.ι).base y = x) ∧
      f ≫ U₂.ι ≫ U₁.ι = V₂.ι ≫ V₁.ι ≫ p ∧ Etale.BaseChangeProperty Λ f q := by
    intro x
    obtain ⟨U₁, V₁, hU₁, hV₁, hx, e₁, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE p x
    obtain ⟨U₂, V₂, hU₂, hV₂, -, hx₂, e₂, ε, hε, hεg⟩ :=
      Smooth.exists_etale_to_affineSpace (p.resLE U₁ V₁ e₁) d ⟨x, hx⟩
    refine ⟨U₁, V₁, U₂, V₂, (p.resLE U₁ V₁ e₁).resLE U₂ V₂ e₂, ⟨⟨⟨x, hx⟩, hx₂⟩, rfl⟩, ?_, ?_⟩
    · simp [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι]
    · have : IsAffine U₂ := hU₂
      have : IsAffine V₂ := hV₂
      rw [← hεg]
      intro T Y g e h _ _ sq F
      exact Etale.baseChangeProperty_comp_affineSpace Λ n q H d
        (by simpa using hn.map (U₂.ι ≫ U₁.ι).appTop.hom) ε g e h sq F
  choose U₁ V₁ U₂ V₂ f hx w hf using key
  intro T Y g e h _ _ sq F
  exact Etale.BaseChangeProperty.of_etale_cover Λ (fun x ↦ (V₂ x).ι ≫ (V₁ x).ι)
    (fun x ↦ ⟨x, hx x⟩) f (fun x ↦ (U₂ x).ι ≫ (U₁ x).ι) w hf g e h sq F

/-- The base-change property for smooth morphisms: if `n` vanishes in `Λ` and is invertible on
`S`, then `BC(p, Λ, q)` holds for every smooth `p : X ⟶ S` and every `q ≥ 0`. After the
reduction `AlgebraicGeometry.Etale.baseChangeProperty_of_smooth_of_relativeDimension_one` this
is `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one`,
specialised along `𝟙 S`. -/
theorem Etale.baseChangeProperty_of_smooth (n : ℕ) (hΛ : (n : Λ) = 0)
    (p : X ⟶ S) [Smooth p] (hn : IsUnit (n : Γ(S, ⊤))) (q : ℕ) :
    Etale.BaseChangeProperty Λ p q :=
  Etale.baseChangeProperty_of_smooth_of_relativeDimension_one Λ n q
    (fun _ _ p' _ _ _ hn' ↦
      (Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one (p := p') n hn' hΛ
        q).baseChangeProperty)
    p hn

/-- Blueprint `theorem-smooth-base-change-classical-torsion--1`: Smooth base change.

**The smooth base change theorem** in étale cohomology: for a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact quasi-separated, and for every sheaf `F` of
`Λ`-modules on `T_ét` all of whose geometric stalks are torsion of orders invertible on `S`,
the base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism in every degree. -/
@[stacks 0EYU]
theorem Etale.isIso_baseChangeHomologyMap_of_smooth (p : X ⟶ S) [Smooth p] (g : T ⟶ S)
    (e : Y ⟶ T) (h : Y ⟶ X) [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  obtain hq | hq := lt_or_ge q 0
  · exact Etale.isIso_baseChangeHomologyMap_of_neg Λ sq hq F
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  refine Etale.isIso_baseChangeHomologyMap_of_forall_nsmul_eq_zero Λ sq _
    (fun n _ hn G hG ↦ ?_) F
  refine Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero Λ sq _ n ?_ G hG
  intro T' Y' g' e' h' _ _ sq' F'
  exact Etale.baseChangeProperty_of_smooth _ n
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) p hn q g' e' h' sq' F'

end AlgebraicGeometry
