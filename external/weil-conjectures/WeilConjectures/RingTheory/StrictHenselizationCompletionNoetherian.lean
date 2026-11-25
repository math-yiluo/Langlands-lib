/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.StrictHenselizationCompletionFlat
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Noetherianity and faithful flatness of the completed strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, parts (a) and (c), and
Algebra, Lemma Tag 00HR (blueprint: lem-sc-strict-henselization-completion-noetherian).
-/

@[expose] public section

universe u

namespace Algebra

/-- The completion of the strict henselization of a Noetherian local ring at the extended
maximal ideal is Noetherian, and the canonical completion map is local and faithfully flat.
Source: Stacks Project, Tag 06LJ, parts (a) and (c), and Tag 00HR
(blueprint: lem-sc-strict-henselization-completion-noetherian).

Proof:
1. Put `I = m C`. The strict henselization triples theorem
`lem-weil-pbc-strict-henselization-triples` identifies `C` as local with maximal ideal `I`
and residue field `K`. Noetherianity of `A` makes `m`, hence `I`, finitely generated.
The quotient `C/I` is a field and is Noetherian. The completion criterion
`lem-weil-pbc-completion-noetherian-quotient-noetherian` now makes the completion Noetherian.
2. The completion map is flat by `lem-sc-strict-henselization-completion-flat`.
3. Projection of the completion to `C/I` has kernel precisely the nonunits: a compatible
sequence with nonzero first coordinate is a unit in every `C/I^n`, and the inverses are
compatible by uniqueness. Thus the completion is local. The composite of the completion
map and this projection is the quotient map, so the completion map reflects units and
is local.
4. Flatness and locality imply faithful flatness by
`lem-pc-local-flat-faithful-flat-reflects-surjective` (Tag 00HR). -/
theorem strictHenselization_completion_noetherian_faithfullyFlat
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    IsNoetherianRing
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C) ∧
      IsLocalHom (algebraMap C
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)) ∧
      Module.FaithfullyFlat C
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C) := by
  obtain ⟨hlocal, hmax⟩ := strictHenselization_local_maximalIdeal A K C hC
  let I := (IsLocalRing.maximalIdeal A).map (algebraMap A C)
  have hI : I.FG := (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing.map _
  have hm : (IsLocalRing.maximalIdeal C).FG := by
    rw [hmax]
    exact hI
  have hquotient : IsNoetherianRing (C ⧸ I) := by
    change IsNoetherianRing (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C))
    rw [← hmax]
    change IsNoetherianRing (IsLocalRing.ResidueField C)
    infer_instance
  have hn := (AdicCompletion.isNoetherianRing_and_isAdicComplete_of_quotient I hI).1
  have hl : IsLocalRing (AdicCompletion I C) := by
    change IsLocalRing
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)
    rw [← hmax]
    exact AdicCompletion.isLocalRing_of_fg hm
  have hh : IsLocalHom (algebraMap C (AdicCompletion I C)) := by
    change IsLocalHom (algebraMap C
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C))
    rw [← hmax]
    exact AdicCompletion.algebraMap_isLocalHom_of_fg hm
  have hf : Module.Flat C (AdicCompletion I C) :=
    RingHom.flat_algebraMap_iff.mp (strictHenselization_completion_flat A K C hC)
  exact ⟨hn, hh, Module.FaithfullyFlat.of_flat_of_isLocalHom⟩

end Algebra
