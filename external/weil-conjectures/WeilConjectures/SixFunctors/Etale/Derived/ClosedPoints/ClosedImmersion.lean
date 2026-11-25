/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.AdicImageTower
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Support
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.AdicImageTower

/-!
# Pushforward along a closed immersion

For a closed immersion `i : Z ⟶ X`, the pushforward `i_*` of étale sheaves of `Λ`-modules is
fully faithful with left inverse `i^*`, and its essential image consists of the sheaves whose
geometric stalks vanish at the points outside `Z` (blueprint
`proposition-extension-zero-restriction-closed-subscheme--5`).

## Main statements

- `AlgebraicGeometry.Etale.mem_essImage_lowerStar_iff_isZero_sheafFiber`
(`proposition-extension-zero-restriction-closed-subscheme--5`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--5`: **pushforward along a
closed immersion.** Let `i : Z ⟶ X` be a closed immersion. The pushforward `i_*` is fully faithful
(`AlgebraicGeometry.Etale.fullyFaithfulLowerStar`), `i^*` is a left inverse
(`AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit`), and a sheaf `K` on `X`
is in the essential image of `i_*` if and only if its support is contained in `Z`, that is, its
stalks at the geometric points over the points outside `Z` vanish. Indeed, both conditions say
that the restriction of `K` to the open complement `U` of `Z` vanishes
(`AlgebraicGeometry.Etale.mem_essImage_lowerStar_of_isZero_upperStar`), and the stalks of that
restriction are those of `K` at the points of `U`. -/
theorem mem_essImage_lowerStar_iff_isZero_sheafFiber {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (K : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (i)_*[ModuleCat.{u + 1} Λ].essImage K ↔
      ∀ x ∉ Set.range i.base,
        IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj K) := by
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι.base = (Set.range i.base)ᶜ := Scheme.Opens.range_ι U
  -- the stalk of `K` at a point of `U` is a stalk of `U^* K`
  have hfib (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X) (hx : x ∈ U)
      (hL : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj L)) :
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj L) := by
    let y : U := ⟨x, hx⟩
    refine ((isZero_sheafFiber_iff_of_apply_eq L ((U : Scheme.{u}).algClosurePoint y ≫ U.ι)
      (X.algClosurePoint x) (by simp [y])).1 ?_)
    exact ((pointSmallEtale _).sheafFiber.map_isZero hL).of_iso
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.ι _).app L).symm
  constructor
  · rintro ⟨G, ⟨e⟩⟩ x hx
    refine (hfib _ x hx ?_).of_iso ((pointSmallEtale _).sheafFiber.mapIso e).symm
    exact isZero_upperStar_lowerStar_of_disjoint_range _ U.ι i
      (hU ▸ disjoint_compl_left) G
  · intro h
    refine mem_essImage_lowerStar_of_isZero_upperStar (j := U.ι) i (by rw [hU, compl_compl]) ?_
    refine isZero_of_forall_isZero_sheafFiber_algClosurePoint fun y ↦ ?_
    refine (isZero_sheafFiber_iff_of_apply_eq K ((U : Scheme.{u}).algClosurePoint y ≫ U.ι)
      (X.algClosurePoint (U.ι.base y)) (by simp)).2 (h _ ?_) |>.of_iso
        ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.ι _).app K)
    rw [← Set.mem_compl_iff, ← hU]
    exact ⟨y, rfl⟩

end Etale

end AlgebraicGeometry
