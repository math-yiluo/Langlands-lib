/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.FilteredColimitLocalization

/-!
# Normality along filtered colimits: the domain part and the common-stage argument

Let `R = colim_i R_i` be a filtered colimit of commutative rings and `p` a prime of `R` with
contractions `p_i`. We record the two halves of Stacks, Tag 037D separately:

- `CommRingCat.isDomain_localization_of_isColimit`: if all `(R_i)_{p_i}` are domains, then
  `R_p` is a domain;
- `CommRingCat.isIntegrallyClosed_of_isColimit_localizationAtPrimeDiagram`: any colimit of the
  diagram `i ↦ (R_i)_{p_i}` of integrally closed domains is integrally closed.

## References

- Stacks Project, Lemma 10.37.5, <https://stacks.math.columbia.edu/tag/037D>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CommRingCat

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}} (c : Cocone F)
  (p : Ideal c.pt) [p.IsPrime]

/-- **Domain part of Stacks 037D.** If `R = colim_i R_i` is a filtered colimit of commutative
rings and `p` is a prime of `R` such that the localizations `(R_i)_{p_i}` at all contracted
primes `p_i = ι_i⁻¹(p)` are domains, then `R_p` is a domain.

(blueprint: `proposition-proper-direct-image-constructible-complexes`) -/
theorem isDomain_localization_of_isColimit (hc : IsColimit c)
    (h : ∀ j, IsDomain (Localization.AtPrime (p.comap (c.ι.app j).hom))) :
    IsDomain (Localization.AtPrime p) :=
  @isDomain_of_isColimit _ _ _ _ _ (isColimitLocalizationAtPrimeCocone c p hc) h

/-- **Integral closedness from a localization cocone.** Let `R = colim_i R_i` be a filtered
colimit of commutative rings and `p` a prime of `R`. If `d` is a colimit cocone over the diagram
`i ↦ (R_i)_{p_i}` of localizations at the contracted primes (for instance the cocone with point
`R_p`), and every `(R_i)_{p_i}` is an integrally closed domain, then the cocone point `d.pt` is
integrally closed: a monic relation and a fraction are lifted to a common stage, where integral
closedness applies.

(blueprint: `lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed-common-stage`) -/
theorem isIntegrallyClosed_of_isColimit_localizationAtPrimeDiagram
    {d : Cocone (localizationAtPrimeDiagram c p)} (hd : IsColimit d)
    (h : ∀ j, IsDomain (Localization.AtPrime (p.comap (c.ι.app j).hom)) ∧
      IsIntegrallyClosed (Localization.AtPrime (p.comap (c.ι.app j).hom))) :
    IsIntegrallyClosed d.pt :=
  (@isDomain_and_isIntegrallyClosed_of_isColimit _ _ _ _ _ hd (fun j ↦ (h j).1)
    (fun j ↦ (h j).2)).2

end CommRingCat
