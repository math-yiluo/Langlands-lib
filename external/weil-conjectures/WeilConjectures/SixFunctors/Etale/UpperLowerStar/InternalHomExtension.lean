/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Internal Hom and étale restriction

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, coefficient dual argument.
-/

@[expose] public section

universe u




open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- Étale pullback commutes with internal Hom of module sheaves.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` local trivialization argument.

Proof: Identify the small étale site of Y, for an étale Y → X, with the localization
of the small étale site of X at Y. On a site, the internal Hom sheaf evaluated at U
is the module of morphisms between the two sheaves restricted to the localization at U.
This description follows from the tensor-Hom adjunction: maps from the free module sheaf
on the representable U to the internal Hom are maps from its tensor product with F to G,
which are precisely maps F|U → G|U. Localization first at Y and then at an object U → Y
is equivalent to localization at U in the original site. Thus restriction of internal Hom
and internal Hom of restrictions have naturally isomorphic sections at every U.
The section identifications commute with restriction along U' → U (both restrict the
same sheaf morphism), giving the required sheaf isomorphism. Transport it across the
localized-site equivalence to the functor Etale.upperStar.
No finite generation or noetherian hypothesis is needed. -/
theorem nonempty_etale_upperStar_ihom_iso (f : Y ⟶ X) [Etale f]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj ((ihom F).obj G) ≅
      (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G)) := by
  have := Etale.isIso_ihomComparison_upperStar
    (ModuleCat.{u + 1} Λ) f F
  exact ⟨asIso ((Functor.LaxMonoidal.ihomComparison
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f) F).app G)⟩

end AlgebraicGeometry.Scheme
