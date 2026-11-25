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
import WeilConjectures.RingTheory.FilteredColimitIsDomain

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- The localization of a filtered colimit at a prime is a domain when every
stage localization at a contracted prime is a domain.
(blueprint: proposition-proper-direct-image-constructible-complexes)

This is the domain part of the proof of Stacks Project, Algebra, Tag 037D.
Representatives of two factors are lifted to a common stage using filteredness;
the zero relation is then detected at a later stage, where the stage
localization is a domain.
-/
theorem filtered_colimit_localization_isDomain
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p))
    (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) := by
  rcases AlgebraicGeometry.filteredColimitLocalizationAtPrime F p with
    ⟨hpᵢ, _, D, hD, _, c, hc, _, hcol⟩
  have hDc : ∀ i : I, IsDomain (D.obj i) := by
    intro i
    rw [hD i]
    exact hF i _
  obtain ⟨hcol⟩ := hcol
  exact isDomain_of_filtered_colimit_cocone D c hcol hDc hc


end CommRingCat
