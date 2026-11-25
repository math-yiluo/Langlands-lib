/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Field
public import Mathlib.RingTheory.PicardGroup
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection

/-!
# The universal curve-test datum attached to a failure of base change

A *curve-test datum* (`AlgebraicGeometry.Etale.CurveTestDatum`) is an affine, integral,
normal base `S₀` with algebraically closed function field, an affine smooth relative curve
`f₀ : X₀ ⟶ S₀` over it, the fibre of `f₀` over a geometric generic point
`Spec K ⟶ S₀` of `S₀`, and an integer `d` invertible on `S₀`.

A failure of the base-change property in degree `q`, below which it holds universally, can be
normalised to such a datum: after passing to a field, enlarging it to an algebraically closed
field and normalising the base, the failure is witnessed by a curve-test datum which is a base
change of `p` and whose higher direct image `R^q h_* (Λ/dΛ)` does not vanish, with `d` dividing
`n`. This is
`AlgebraicGeometry.Etale.exists_curveTestDatum`; the vanishing theorem
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing`, which forbids exactly that,
is what contradicts it.

## Main definitions

- `AlgebraicGeometry.Etale.CurveTestDatum`: a smooth affine relative curve over a normal
  base with algebraically closed function field, together with its geometric generic fibre
  and a torsion order invertible on the base.

## Main statements

- `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage`: a failure of
  `BC(p, Λ, q)` in the first degree where it can fail is witnessed by the geometric generic
  fibre of a base change of `p` over a normal affine base with algebraically closed function
  field, on which a higher direct image of a constant sheaf does not vanish.
- `AlgebraicGeometry.Etale.exists_curveTestDatum`: a failure of `BC(p, Λ, q)`, when
  `BC(p, Λ, q')` holds universally for `q' < q`, produces a curve-test datum which is a base
  change of `p` and on which a higher direct image of a constant sheaf fails to vanish.

## Implementation notes

The blueprint reduces the coefficient sheaf on the geometric point `Spec K` to a constant sheaf
`ℤ/dℤ` by decomposing a `ℤ/nℤ`-module as a sum of cyclic modules. Over a general coefficient
ring `Λ` with `n = 0` in `Λ` a `Λ`-module is not a sum of the `Λ/dΛ`, so this step is recorded
as `AlgebraicGeometry.Etale.exists_not_isZero_higherDirectImage_constantModSheaf`, which
compares the higher direct images through their underlying abelian sheaves. It is applied
after the normalisation step, where the base-change map is already known to be injective, so
that only the nonvanishing of its target has to be transported.

## References

- Stacks Project, Lemma 59.88.7, <https://stacks.math.columbia.edu/tag/0F08>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

/-- A *curve-test datum*: an affine smooth relative curve `f₀ : X₀ ⟶ S₀` over an affine,
integral, normal base with algebraically closed function field, together with its fibre over
a geometric generic point `Spec K ⟶ S₀` and an integer `d` invertible on `S₀`:

```
Y₀ ---e---> Spec K
|              |
h              |
v              v
X₀ ---f₀----> S₀
```

the right-hand column being `Spec` of an extension `i` of the function field of `S₀`
followed by the inclusion of the generic point. Normality of `S₀` is spelled out as integral
closedness of all its stalks, there being no `IsNormal` predicate on schemes. -/
structure Etale.CurveTestDatum where
  /-- the base of the test curve -/
  S₀ : Scheme.{u}
  [isAffine_base : IsAffine S₀]
  [isIntegral_base : IsIntegral S₀]
  /-- the base is normal: all its stalks are integrally closed -/
  isIntegrallyClosed_stalk (x : S₀) : IsIntegrallyClosed (S₀.presheaf.stalk x)
  [isAlgClosed_functionField : IsAlgClosed S₀.functionField]
  /-- the total space of the test curve -/
  X₀ : Scheme.{u}
  /-- the test curve -/
  f₀ : X₀ ⟶ S₀
  [isAffineHom : IsAffineHom f₀]
  [smoothOfRelativeDimension_one : SmoothOfRelativeDimension 1 f₀]
  /-- the algebraically closed field of the geometric generic point -/
  K : Type u
  [field : Field K]
  [isAlgClosed : IsAlgClosed K]
  /-- `K` is an extension of the function field of the base -/
  i : S₀.functionField ⟶ CommRingCat.of K
  /-- the geometric generic fibre of the test curve -/
  Y₀ : Scheme.{u}
  /-- the projection of the fibre to the geometric generic point -/
  e : Y₀ ⟶ Spec (CommRingCat.of K)
  /-- the projection of the fibre to the total space -/
  h : Y₀ ⟶ X₀
  /-- the fibre square is Cartesian -/
  isPullback : IsPullback e h (Spec.map i ≫ S₀.fromSpecStalk (genericPoint S₀)) f₀
  /-- the torsion order -/
  d : ℕ
  /-- the torsion order is invertible on the base -/
  isUnit_d : IsUnit (d : Γ(S₀, ⊤))

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- The normalisation of an affine scheme `S'` in the spectrum of an algebraically closed field
`K` over it: the spectrum `S''` of the integral closure of `Γ(S', ⊤)` in `K`. It is affine,
integral and normal, its function field is algebraically closed
(`IsFractionRing.isAlgClosed_integralClosure`), the morphism `S'' ⟶ S'` is integral, and the
given point `Spec K ⟶ S'` lifts to a geometric generic point of `S''`. 
(blueprint: lem-sbc-normalization-algclosed-field)
-/
theorem Etale.exists_normalization_of_isAlgClosed {S' : Scheme.{u}} [IsAffine S'] {K : Type u}
    [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S') :
    ∃ (S'' : Scheme.{u}) (_ : IsAffine S'') (_ : IsIntegral S'')
      (_ : ∀ x : S'', IsIntegrallyClosed (S''.presheaf.stalk x))
      (_ : IsAlgClosed S''.functionField) (π : S'' ⟶ S') (_ : IsIntegralHom π)
      (i : S''.functionField ⟶ CommRingCat.of K),
      (Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')) ≫ π = g := by
  let φ : Γ(S', ⊤) ⟶ CommRingCat.of K := Spec.preimage (g ≫ S'.isoSpec.hom)
  let : Algebra Γ(S', ⊤) K := φ.hom.toAlgebra
  let B := integralClosure Γ(S', ⊤) K
  have hinj : Function.Injective (algebraMap B K) := Subtype.val_injective
  have : IsIntegrallyClosed B := .of_isIntegrallyClosed_of_isIntegrallyClosedIn B K
  have hB : IsIntegrallyClosed Γ(Spec (.of B), ⊤) :=
    .of_equiv (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
  have : IsDomain (CommRingCat.of B) := inferInstanceAs (IsDomain B)
  let : Algebra B (Spec (.of B)).functionField :=
    instAlgebraCarrierFunctionFieldSpec (.of B)
  have : IsFractionRing B (Spec (.of B)).functionField :=
    functionField_isFractionRing_of_affine (.of B)
  let i : (Spec (.of B)).functionField ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (IsFractionRing.lift (K := (Spec (.of B)).functionField) hinj)
  refine ⟨Spec (.of B), inferInstance, inferInstance, fun x ↦ ?_,
    IsFractionRing.isAlgClosed_integralClosure (R := Γ(S', ⊤)) (K := K),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S', ⊤) B)) ≫ S'.isoSpec.inv, ?_,
    i, ?_⟩
  · let := TopCat.Presheaf.algebra_section_stalk (Spec (.of B)).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec (.of B)).Opens))
    have := (isAffineOpen_top (Spec (.of B))).isLocalization_stalk ⟨x, trivial⟩
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  · have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap Γ(S', ⊤) B))) :=
      IsIntegralHom.SpecMap_iff.2 fun x ↦ Algebra.IsIntegral.isIntegral (R := Γ(S', ⊤)) x
    infer_instance
  · have key : (CommRingCat.ofHom (algebraMap Γ(S', ⊤) B) ≫ (Scheme.ΓSpecIso (.of B)).inv ≫
        (Spec (.of B)).presheaf.germ ⊤ (genericPoint (Spec (.of B))) trivial) ≫
        i = φ := by
      ext a
      exact IsFractionRing.lift_algebraMap hinj (algebraMap Γ(S', ⊤) B a)
    have hg : g = Spec.map φ ≫ S'.isoSpec.inv := by
      rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hg, ← key, Spec.fromSpecStalk_eq]
    simp only [Spec.map_comp, Category.assoc]

/-- Whether the base-change map is an isomorphism does not depend on how the base `g` of the
square is written. -/
lemma Etale.isIso_baseChangeHomologyMap_congr {T Y : Scheme.{u}} {e : Y ⟶ T} {h : Y ⟶ X}
    {g₁ g₂ : T ⟶ S} (hg : g₁ = g₂) (sq₁ : IsPullback e h g₁ p) (sq₂ : IsPullback e h g₂ p)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₁ q F) ↔
      IsIso (Etale.baseChangeHomologyMap Λ sq₂ q F) := by
  subst hg
  rfl

/-- The reduction of the coefficients to a constant sheaf `Λ/dΛ` in the proof of blueprint
`lemma-reduction-curve-over-normal-base--1`.

Let `K` be algebraically closed, `e : Y ⟶ Spec K` and `h : Y ⟶ X` with `h` quasi-compact and
quasi-separated, and let `n ≠ 0` annihilate `Λ`. If `R^q h_* e⁻¹ F` is nonzero for a sheaf `F`
of `Λ`-modules on `(Spec K)_ét`, then `R^q h_* (Λ/dΛ)` is nonzero for some `d ∣ n`.

The sheaf `F` is constant with value its global sections `M`, so `e⁻¹ F` is the constant sheaf
`M` on `Y`. The higher direct images of a sheaf of `Λ`-modules are those of its underlying
abelian sheaf, and `R^q h_*` commutes with direct sums as `h` is quasi-compact and
quasi-separated. As an abelian group `M` is a direct sum of cyclic groups `ℤ/ℓ^k`, with `ℓ`
dividing the characteristic `m` of `Λ`, so by dévissage `R^q h_* (ℤ/ℓ) ≠ 0` for a prime
`ℓ ∣ m`; and `Λ/ℓΛ` is a nonzero `𝔽_ℓ`-vector space, whence `R^q h_* (Λ/ℓΛ) ≠ 0`. -/
theorem Etale.exists_not_isZero_higherDirectImage_constantModSheaf {K : Type u} [Field K]
    [IsAlgClosed K] {Y : Scheme.{u}} (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X) [QuasiCompact h]
    [QuasiSeparated h] (n : ℕ) (hn : n ≠ 0) (hΛ : (n : Λ) = 0) (q : ℤ)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ¬ IsZero ((Etale.baseChangeTargetFunctor Λ e h q).obj F)) :
    ∃ d, d ∣ n ∧ ¬ IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  obtain ⟨r, hr, hrn, hunit, hnonzero⟩ :=
    Etale.exists_prime_cyclic_higherDirectImage Λ e h n hn hΛ q F hF
  refine ⟨r, hrn, ?_⟩
  intro hzero
  exact hnonzero
    (Etale.isZero_prime_cyclic_higherDirectImage_of_quotient Λ h q r hr hunit hzero)

/-- Blueprint `lemma-reduction-curve-over-normal-base--1`: Universal curve-test datum for a failure.

Let `n` be invertible on `S` with `n = 0` in `Λ`, and let `q ≥ 1`. If `BC(p, Λ, q')` holds
universally for all `q' < q` but `BC(p, Λ, q)` does not hold universally, there is a base
change `p' : X' ⟶ S'` of `p` with `S'` affine, integral and normal with algebraically closed
function field, an algebraically closed extension `K` of that function field, and `d ∣ n` such
that `R^q h_* (Λ/dΛ) ≠ 0` for the fibre `h : Y ⟶ X'` of `p'` over `Spec K`.

A counterexample over a field `K₀` exists by
`AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`. It survives
the integral surjective base change to an algebraic closure `K` of `K₀`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`) and the
replacement of `S'` by the normalisation of `S'` in `Spec K`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom`). The base-change
map of the resulting square is injective (`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`)
and not an isomorphism, so its target is nonzero, and
`AlgebraicGeometry.Etale.exists_not_isZero_higherDirectImage_constantModSheaf` reduces the
coefficients to a constant sheaf `Λ/dΛ`. -/
@[stacks 0F08]
theorem Etale.exists_isPullback_not_isZero_higherDirectImage (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) (hΛ : (n : Λ) = 0) (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.UniversalBaseChangeProperty Λ p q) :
    ∃ (S' X' : Scheme.{u}) (a : S' ⟶ S) (b : X' ⟶ X) (p' : X' ⟶ S') (_ : IsPullback b p' p a)
      (_ : IsAffine S') (_ : IsIntegral S')
      (_ : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
      (_ : IsAlgClosed S'.functionField) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (i : S'.functionField ⟶ CommRingCat.of K) (Y : Scheme.{u}) (e : Y ⟶ Spec (.of K))
      (h : Y ⟶ X') (_ : IsPullback e h (Spec.map i ≫ S'.fromSpecStalk (genericPoint S')) p')
      (d : ℕ), d ∣ n ∧ ¬ IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  obtain ⟨F⟩ := Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty Λ p q hq hprev
    hfail
  have := F.isAffine
  let := F.field
  -- the algebraic closure of the field of the counterexample
  let K := AlgebraicClosure F.K
  let πK : Spec (.of K) ⟶ Spec (.of F.K) := Spec.map (CommRingCat.ofHom (algebraMap F.K K))
  have : IsIntegralHom πK :=
    IsIntegralHom.SpecMap_iff.2 fun x ↦ Algebra.IsIntegral.isIntegral (R := F.K) x
  have hπK : Function.Surjective πK.base := fun x ↦
    ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩
  -- the normalisation of `S'` in `Spec K`
  obtain ⟨S'', _, _, hnorm, _, π, _, i, hi⟩ :=
    Etale.exists_normalization_of_isAlgClosed (πK ≫ F.g)
  set g'' := Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')
  have hπ : IsPullback (pullback.fst F.p' π) (pullback.snd F.p' π) F.p' π :=
    IsPullback.of_hasPullback _ _
  have sq'' : IsPullback (pullback.fst g'' (pullback.snd F.p' π))
      (pullback.snd g'' (pullback.snd F.p' π)) g'' (pullback.snd F.p' π) :=
    IsPullback.of_hasPullback _ _
  have sq := (sq''.flip.paste_horiz hπ).flip
  have hpb := hπ.paste_horiz F.isPullback
  have hprev' : Etale.BaseChangeProperty Λ F.p' (q - 1) :=
    (hprev (q - 1) (by omega)) F.a F.b F.p' F.isPullback
  -- the failure survives the passage to `K` and to the normalisation
  have h₁ : ¬ IsIso (Etale.baseChangeHomologyMap Λ sq q
      ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) := by
    rw [Etale.isIso_baseChangeHomologyMap_congr Λ F.p' hi sq (hi ▸ sq)]
    exact fun hiso ↦ F.not_isIso
      (Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective Λ q hq hprev'
        F.isPullback_fibre πK hπK (hi ▸ sq) F.F hiso)
  have h₂ : ¬ IsIso (Etale.baseChangeHomologyMap Λ sq'' q
      ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) :=
    fun hiso ↦ h₁ ((Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom Λ π hπ sq'' sq q
      _).2 hiso)
  -- its target is nonzero, the base-change map being injective
  have hprev'' : Etale.BaseChangeProperty Λ (pullback.snd F.p' π) (q - 1) :=
    (hprev (q - 1) (by omega)) _ _ _ hpb
  have := Etale.mono_baseChangeHomologyMap Λ q hq hprev'' sq'' ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)
  have h₃ : ¬ IsZero ((Etale.baseChangeTargetFunctor Λ (pullback.fst g'' (pullback.snd F.p' π))
      (pullback.snd g'' (pullback.snd F.p' π)) q).obj ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) :=
    fun hz ↦ h₂ ((IsZero.of_mono (Etale.baseChangeHomologyMap Λ sq'' q
      ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) hz).isIso hz _)
  have : IsAffineHom (pullback.snd g'' (pullback.snd F.p' π)) :=
    MorphismProperty.of_isPullback sq'' inferInstance
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nonempty (⊤ : (Spec (.of K)).Opens) :=
      ⟨⟨Nonempty.some (inferInstance : Nonempty (Spec (.of K))), trivial⟩⟩
    have : Nontrivial Γ(Spec (.of K), ⊤) := Scheme.component_nontrivial _ _
    simpa using hn.map (πK ≫ F.g ≫ F.a).appTop.hom
  obtain ⟨d, hd, hne⟩ := Etale.exists_not_isZero_higherDirectImage_constantModSheaf Λ _ _ n hn0
    hΛ q _ h₃
  exact ⟨S'', _, π ≫ F.a, _, _, hpb, inferInstance, inferInstance, hnorm, inferInstance, K,
    inferInstance, inferInstance, i, _, _, _, sq'', d, hd, hne⟩

/-- Blueprint `lemma-reduction-curve-over-normal-base`: Universal curve-test datum for a failure.

Let `p : X ⟶ S` be an affine smooth relative curve with `X` affine, and let `n` be invertible
on `S` and annihilate `Λ`. If `BC(p, Λ, q')` holds universally for all `q' < q` but
`BC(p, Λ, q)` fails for some `q ≥ 1`, there is a curve-test datum `D` which is a base change of
`p`, whose torsion order `D.d` divides `n`, and on whose geometric generic fibre the higher
direct image `R^q h_* (Λ/D.d Λ)` of the constant sheaf does not vanish.

This is `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage`: affine
smooth morphisms of relative dimension one are stable under base change, and `d` is invertible
on the new base since it divides `n`. -/
@[stacks 0F08]
theorem Etale.exists_curveTestDatum [IsAffine X] [IsAffineHom p]
    [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (hΛ : (n : Λ) = 0)
    (q : ℤ) (hq : 1 ≤ q) (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    ∃ (D : Etale.CurveTestDatum.{u}) (a : D.S₀ ⟶ S) (b : D.X₀ ⟶ X),
      IsPullback b D.f₀ p a ∧ D.d ∣ n ∧
      ¬ IsZero (Etale.higherDirectImage Λ D.h q (Etale.constantModSheaf Λ D.Y₀ D.d)) := by
  obtain ⟨S', X', a, b, p', hpb, _, _, hnorm, _, K, _, _, i, Y, e, h, sq, d, hd, hne⟩ :=
    Etale.exists_isPullback_not_isZero_higherDirectImage Λ p n hn hΛ q hq hprev
      fun H ↦ hfail H.baseChangeProperty
  have : IsAffineHom p' := MorphismProperty.of_isPullback hpb inferInstance
  have : SmoothOfRelativeDimension 1 p' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hpb inferInstance
  have hd' : IsUnit (d : Γ(S', ⊤)) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (by simpa using hn.map a.appTop.hom)
  exact ⟨⟨S', hnorm, X', p', K, i, Y, e, h, sq, d, hd'⟩, a, b, hpb, hd, hne⟩

end AlgebraicGeometry
