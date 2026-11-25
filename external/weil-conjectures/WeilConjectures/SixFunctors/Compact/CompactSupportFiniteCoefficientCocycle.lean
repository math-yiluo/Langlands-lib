/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportCoefficientPresentation

/-! # The compact-support coefficient square with a prescribed composite

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-finite-coefficient-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
-- Keep distinct quotient levels from unfolding their valuation-theoretic ideal data.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The compact-support restriction square with a prescribed composite ring map.
Source: blueprint finite-level coefficient comparison, Stacks Tag 03DA
(blueprint: lem-coef-compact-support-finite-coefficient-cocycle).
Proof: substitute the composite map equality in the published composition square.
The inserted identity isomorphisms then simplify to identities. -/
theorem compactSupportRestriction_comp_cast (l : ℕ) [Fact l.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (c : Compactification f) (φ : A →+* B) (ψ : B →+* C)
    (χ : A →+* C) (hχ : ψ.comp φ = χ) (K : proEtaleDerivedCategory X C) :
    (sfAmbientCompactSupportCandidate A c).map
        ((compactSupportCoefficientResComp X φ ψ χ hχ).hom.app K) ≫
          (compactSupportCoefficientComparison c χ).hom.app K =
      (compactSupportCoefficientComparison c φ).hom.app
          ((compactSupportCoefficientRestriction X ψ).obj K) ≫
        (compactSupportCoefficientRestriction Y φ).map
          ((compactSupportCoefficientComparison c ψ).hom.app K) ≫
        (compactSupportCoefficientResComp Y φ ψ χ hχ).hom.app
          ((sfAmbientCompactSupportCandidate C c).obj K) := by
  subst χ
  simpa only [compactSupportCoefficientResComp, compactSupportCoefficientComparison,
    compactSupportCoefficientRestriction, eqToIso_refl, Iso.trans_refl,
    sfAmbientCompactSupportCandidate] using
    sfCompactSupportRestriction_comp l f hl c φ ψ K

end WeilConjectures
