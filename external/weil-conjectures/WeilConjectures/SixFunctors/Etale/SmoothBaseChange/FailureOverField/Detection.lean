/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.FieldFailure
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap

/-!
# A failure of base change is detected over a field

If `BC(p, Λ, q')` holds universally for all `q' < q` but `BC(p, Λ, q)` fails, then the
failure is already visible after base change to an affine open `S' ⊆ S` and over a field. The
proof applies the minimal-counterexample lemma
`AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty` to the survival property
`AlgebraicGeometry.Etale.SurvivesBaseChange` of a cokernel element.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_fieldFailure`: if `BC(p, Λ, q')` holds universally for
  `q' < q` and `BC(p, Λ, q)` fails, a counterexample over a field exists.
- `AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`: the same
  conclusion when `BC(p, Λ, q)` only fails after some base change, as in the blueprint.

## References

- Stacks Project, Lemma 59.88.6, <https://stacks.math.columbia.edu/tag/0F07>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X S : Scheme.{u}} {p : X ⟶ S}

variable {Λ} in
/-- A failure of `BC(p, Λ, q)` is already a failure over an affine open of `S`: the
base-change map and the higher direct images are compatible with restriction to an open of
`S`, which is the pullback along an étale morphism, and being an isomorphism of sheaves is
local (`AlgebraicGeometry.Etale.BaseChangeProperty.of_etale_cover`, applied to the cover of
`S` by its affine opens). -/
theorem Etale.exists_isAffineOpen_not_baseChangeProperty {q : ℤ}
    (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    ∃ U : S.Opens, IsAffineOpen U ∧ ¬ Etale.BaseChangeProperty Λ (pullback.snd p U.ι) q := by
  by_contra! H
  refine hfail (Etale.BaseChangeProperty.of_etale_cover Λ (ι := S.affineOpens)
    (fun U ↦ pullback.fst p U.1.ι) (fun x ↦ ?_) (fun U ↦ pullback.snd p U.1.ι)
    (fun U ↦ U.1.ι) (fun _ ↦ pullback.condition.symm) fun U ↦ H U.1 U.2)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p x)) isOpen_univ
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
    (g := Scheme.Opens.ι (X := S) U) x ⟨p x, hx⟩ rfl
  exact ⟨⟨U, hU⟩, y, hy⟩

variable (p) in
/-- Blueprint `lemma-reduction-field--1`: A failure is detected on the generic fibre.

If the base-change property `BC(p, Λ, q')` holds universally for all `q' < q` while
`BC(p, Λ, q)` fails for some `q ≥ 1`, there is a counterexample over a field, that is, an
`AlgebraicGeometry.Etale.FieldFailure`. Blueprint `lemma-reduction-field--1` only assumes that
`BC(p, Λ, q)` does not hold universally; that form is
`AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty`.

After restricting to an affine open of `S` the base of the failing square is quasi-compact
and quasi-separated. The base-change map is injective there
(`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`), so some geometric stalk of its target
contains an element `ξ` outside its image, and the minimal-counterexample lemma applied to the
survival of `ξ` produces the field. -/
@[stacks 0F07]
theorem Etale.nonempty_fieldFailure (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    Nonempty (Etale.FieldFailure Λ p q) := by
  obtain ⟨U, hU, hUfail⟩ := Etale.exists_isAffineOpen_not_baseChangeProperty hfail
  have : IsAffine U := hU
  have hpb : IsPullback (pullback.fst p U.ι) (pullback.snd p U.ι) p U.ι :=
    IsPullback.of_hasPullback _ _
  have hprev' : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ (pullback.snd p U.ι) q' :=
    fun q' hq' ↦ (hprev q' hq').of_isPullback hpb
  obtain ⟨T, Y, g, e, h, _, _, sq, F, hF⟩ : ∃ (T Y : Scheme.{u}) (g : T ⟶ U) (e : Y ⟶ T)
      (h : Y ⟶ pullback p U.ι) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (sq : IsPullback e h g (pullback.snd p U.ι))
      (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      ¬ IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
    by_contra! H
    exact hUfail fun g e h _ _ sq F ↦ H _ _ g e h ‹_› ‹_› sq F
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated g
  have hmono := Etale.mono_baseChangeHomologyMap Λ q hq
    (hprev' (q - 1) (by omega)).baseChangeProperty sq F
  obtain ⟨x, hx⟩ : ∃ x : ↥(pullback p U.ι),
      ¬ IsIso ((Scheme.uliftPointSmallEtale _ x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq q F)) := by
    by_contra! H
    exact hF (Scheme.isIso_of_isIso_sheafFiber_map _ H)
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ ∉ Set.range ((Scheme.uliftPointSmallEtale _ x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq q F)).hom := by
    by_contra! H
    refine hx ((ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, H⟩)
    -- instance search does not find `LocallySmall.{u + 1}` for the small étale site
    have : LocallySmall.{u + 1} (pullback p U.ι).Etale := locallySmall_max.{u + 1, u}
    have : PreservesFiniteLimits
        ((Scheme.uliftPointSmallEtale _ x).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
      inferInstance
    exact (ModuleCat.mono_iff_injective _).1 (Functor.map_mono _ _)
  obtain ⟨K, _, φ, hφ⟩ := exists_spec_field_of_isQcqsLocalProperty T _
    (Etale.isQcqsLocalProperty_survivesBaseChange q hq hprev' sq F x ξ)
    (Etale.survivesBaseChange_id q sq F x ξ hξ)
  refine ⟨Etale.FieldFailure.mk (S' := U) (a := U.ι) (X' := pullback p U.ι)
    (p' := pullback.snd p U.ι) (b := pullback.fst p U.ι) (isPullback := hpb) (K := K)
    (g := φ ≫ g) (Y' := pullback (φ ≫ g) (pullback.snd p U.ι)) (e := pullback.fst _ _)
    (h := pullback.snd _ _) (isPullback_fibre := IsPullback.of_hasPullback _ _)
    (F := ((φ)^*[ModuleCat.{u + 1} Λ]).obj F) (not_isIso := fun hiso ↦ hφ ?_)⟩
  exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2 _

variable (p) in
/-- Blueprint `lemma-reduction-field--1`: A failure of base change is detected over a field.

If the base-change property `BC(p, Λ, q')` holds universally for all `q' < q` while
`BC(p, Λ, q)` fails after some base change for some `q ≥ 1`, there is a counterexample over
a field. Apply `AlgebraicGeometry.Etale.nonempty_fieldFailure` to a failing base change of
`p` and paste the squares. -/
@[stacks 0F07]
theorem Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.UniversalBaseChangeProperty Λ p q) :
    Nonempty (Etale.FieldFailure Λ p q) := by
  simp only [Etale.UniversalBaseChangeProperty, not_forall] at hfail
  obtain ⟨S'', X'', a, b, p'', hpb, hfail⟩ := hfail
  obtain ⟨F⟩ := Etale.nonempty_fieldFailure Λ p'' q hq
    (fun q' hq' ↦ (hprev q' hq').of_isPullback hpb) hfail
  have := F.isAffine
  have := F.field
  exact ⟨{ F with a := F.a ≫ a, b := F.b ≫ b, isPullback := F.isPullback.paste_horiz hpb }⟩

end AlgebraicGeometry
