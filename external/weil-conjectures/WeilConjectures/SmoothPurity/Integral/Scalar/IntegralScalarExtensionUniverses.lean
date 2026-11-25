/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension

/-! # Integral scalar extension with independent coefficient and site universes

Source: blueprint integral scalar extension, order 1460; Bhatt--Scholze,
Definition 3.4.10 (blueprint: def-weil-integral-scalar-extension).
The published resolving-class construction already permits independent universes.
This interface exposes that same construction without identifying those universes.
The original equal-universe interface is publicly retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The existing strict Roos construction localized on its flat-term K-flat class.
Its universal normalized comparison determines the functor up to the unique
comparison-preserving isomorphism. No site or coefficient universe is restricted.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
def integralScalarExtensionOfUniverses :
    DerivedCategory (integralTowerModules.{t, u} l E Y) ⥤
      DerivedCategory (integralTowerModules.{t, u} l L Y) :=
  (integralScalarExtensionWellDefined.{t, u} l E L ι Y).2.choose

/-- The retained comparison with the actual strict-tower functor on resolving complexes.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
def integralScalarExtensionComparisonOfUniverses :
    integralOperationsGoodLocalization.{t, u} l E Y ⋙ integralScalarExtensionOfUniverses l E L ι Y ≅
      integralScalarOnGood.{t, u} l E L ι Y :=
  (integralScalarExtensionWellDefined.{t, u} l E L ι Y).2.choose_spec.choose

/-- Additivity from the same universal localization witness.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
instance integralScalarExtensionOfUniverses_additive :
    (integralScalarExtensionOfUniverses l E L ι Y).Additive :=
  (integralScalarExtensionWellDefined.{t, u} l E L ι Y).2.choose_spec.choose_spec.1

end WeilConjectures
