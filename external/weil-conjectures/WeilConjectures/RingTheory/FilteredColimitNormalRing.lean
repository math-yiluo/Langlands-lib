/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import WeilConjectures.RingTheory.FilteredColimitNormalRingDomain
import WeilConjectures.RingTheory.FilteredColimitNormalRingIntegrallyClosed

/-!
# A filtered colimit of normal rings is normal

Source: Stacks Project, Algebra, Lemma Tag 037D (lemma-colimit-normal-ring)
(blueprint: lem-weil-pbc-filtered-colimit-normal-ring).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A filtered colimit of normal rings is normal, with no condition on transition maps.
Source: Stacks Project, Algebra, Lemma Tag 037D (lemma-colimit-normal-ring),
stated there for a directed system; the filtered formulation is the one used in the
blueprint (blueprint: lem-weil-pbc-filtered-colimit-normal-ring).

Proof: reduce normality to the localizations at prime ideals.  The localization at a
prime of the colimit is the filtered colimit of the corresponding localizations at the
contracted primes.  Finitely many elements and relations lift to one common index, so
the colimit is a domain; clearing denominators in a monic equation and lifting it to one
stage, normality of that stage puts the root back in the colimit.  This proves each
localization is a normal domain.
-/
theorem isNormal_of_filtered_colimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p) := by
  set_option linter.style.haveILetI false in
  intro p hp
  letI := hp
  exact ⟨filtered_colimit_localization_isDomain F (fun i q hq => (hF i q).1) p,
    filtered_colimit_localization_isIntegrallyClosed F hF p⟩

end CommRingCat
