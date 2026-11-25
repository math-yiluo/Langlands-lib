/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.ProjectiveDomination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Cancellation
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# The reduction of proper base change to the projective line

Assume that the projection `ℙ¹_S ⟶ S` satisfies the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`. Then every proper morphism
satisfies it (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`).

The proof follows the Stacks Project:

- *change of coefficients*: it suffices to treat the coefficient rings `Λ ⧸ pΛ`, `p` prime,
  which are torsion as additive groups
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_forall_prime`), and the hypothesis passes
  to them (`AlgebraicGeometry.Etale.HasTorsionBaseChange.quotient`); for a torsion ring the base
  change property composes and cancels along proper surjections;
- *from `ℙ¹` to `ℙⁿ`*: `(ℙ¹_S)ⁿ ⟶ S` is a composite of projective lines, and the symmetric
  product `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` is finite and surjective
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveSpace`);
- *target locality and Chow's lemma*: over an affine open `U` of the target, `f` is dominated by
  a closed subscheme `X̃` of `ℙⁿ_U` through a proper surjection `π : X̃ ⟶ X`; closed immersions are
  finite, so `X̃ ⟶ U` has the base change property, and so does `π`, which factors as the closed
  immersion `X̃ ⟶ ℙⁿ_X` followed by the projection; cancellation along `π` concludes.

## References

- Stacks Project, Lemma 59.91.10, <https://stacks.math.columbia.edu/tag/0A4F>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A finite morphism satisfies the base change property for every coefficient ring: the derived
base change map is an isomorphism on all of `D⁺`
(`AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite`).
(blueprint: `lemma-finite-morphisms--2`) -/
theorem Etale.hasTorsionBaseChange_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_isBaseChangeIso Λ f

/-- The tower `(ℙ¹_S)ⁿ ⟶ S` satisfies the base change property if all projective lines do, the
coefficient ring being torsion: it is a composite of projective lines over successive bases. -/
theorem Etale.hasTorsionBaseChange_projectiveLinePowProj (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S)) (n : ℕ)
    (S : Scheme.{u}) : Etale.HasTorsionBaseChange Λ (projectiveLinePowProj n S) := by
  induction n with
  | zero => exact Etale.hasTorsionBaseChange_of_isFinite Λ (𝟙 S)
  | succ n ih => exact Etale.HasTorsionBaseChange.comp Λ hΛ (h _) ih

/-- **Reduction of projective space to products of lines.** For a torsion coefficient ring `Λ`,
if `ℙ¹_S ⟶ S` satisfies the base change property for every scheme `S`, then so does `ℙⁿ_S ⟶ S`
for every finite index type `n`: the composite `(ℙ¹_S)ᵏ ⟶ ℙⁿ_S ⟶ S` of the finite surjective
symmetric product morphism with the projection is a composite of projective lines, and the base
change property cancels along the finite surjective symmetric product morphism.
(blueprint: `lemma-pbc-projective-space--1`) -/
theorem Etale.hasTorsionBaseChange_projectiveSpace (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S)) (n : Type u)
    [Finite n] (S : Scheme.{u}) : Etale.HasTorsionBaseChange Λ (ℙ(n; S) ↘ S) := by
  cases isEmpty_or_nonempty n with
  | inl _ => exact Etale.hasTorsionBaseChange_of_isFinite Λ _
  | inr _ =>
    obtain ⟨k, σ, _, _, hσ⟩ := exists_isFinite_surjective_projectiveLinePow n S
    refine Etale.HasTorsionBaseChange.of_comp Λ hΛ (f := σ)
      (Etale.hasTorsionBaseChange_of_isFinite Λ σ) ?_
    rw [hσ]
    exact Etale.hasTorsionBaseChange_projectiveLinePowProj Λ hΛ h k S

/-- **Reduction of proper base change to the projective line, torsion coefficients.** For a
coefficient ring `Λ` which is torsion as an additive group, if `ℙ¹_S ⟶ S` satisfies the base
change property for every scheme `S`, then so does every proper morphism `f : X ⟶ Y`.

By target locality we may assume `Y` affine. Chow's lemma gives a proper surjection
`π : X̃ ⟶ X` and a closed immersion `i : X̃ ⟶ ℙⁿ_Y` over `Y`. The composite `π ≫ f = i ≫ pₙ`
has the base change property, as `i` is finite and `pₙ : ℙⁿ_Y ⟶ Y` has it by
`AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveSpace`; so does `π`, the composite of
the closed immersion `(π, i) : X̃ ⟶ ℙⁿ_X` with the projection `ℙⁿ_X ⟶ X`. Cancellation along the
proper surjection `π` gives the base change property for `f`.
(blueprint: `proposition-proper-base-change-etale-site--1`) -/
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAddTorsion
    (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Etale.HasTorsionBaseChange Λ f := by
  refine Etale.hasTorsionBaseChange_of_affineOpens Λ f fun U ↦ ?_
  have : IsAffine (U : Y.Opens) := U.2
  obtain ⟨D⟩ := ProjectiveDomination.nonempty_of_isAffine (f := f ∣_ (U : Y.Opens))
  have hp := Etale.hasTorsionBaseChange_projectiveSpace Λ hΛ h D.n
  have hπ : Etale.HasTorsionBaseChange Λ D.π := by
    have hw : D.π ≫ f ∣_ (U : Y.Opens) = D.i ≫ ℙ(D.n; _) ↘ _ := D.w.symm
    rw [← ProjectiveSpace.liftBaseChange_over D.π D.i hw]
    exact Etale.HasTorsionBaseChange.comp Λ hΛ (Etale.hasTorsionBaseChange_of_isFinite Λ _)
      (hp _)
  refine Etale.HasTorsionBaseChange.of_comp Λ hΛ hπ ?_
  rw [← D.w]
  exact Etale.HasTorsionBaseChange.comp Λ hΛ (Etale.hasTorsionBaseChange_of_isFinite Λ _) (hp _)

/-- **Reduction of proper base change to the projective line**: if the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`,
then so does every proper morphism of schemes.

The proof is Chow's lemma: a proper `f : X ⟶ Y` is dominated by a projective one,

```
       X̃ ------------> ℙⁿ_Y
       |                |
     π |                | pₙ
       v                v
       X ------ f ----> Y
```

with `π` proper surjective and the horizontal arrow a closed immersion over `Y`; the base
change property for `pₙ` comes from that of `ℙ¹` by the symmetric-product morphism, and
transfers to `f` because it composes and cancels along proper surjections. These manipulations
need a torsion coefficient ring, which is reached by the change of coefficients
`Λ ↝ Λ ⧸ pΛ`.
(blueprint: `proposition-proper-base-change-etale-site--1`) -/
@[stacks 0A4F]
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_forall_prime Λ f fun p hp ↦
    Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAddTorsion _
      (isAddTorsion_quotient_span_natCast Λ hp.pos) (fun S ↦ (h S).quotient Λ p) f

end AlgebraicGeometry
