/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleSheafSmall
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # LocallyFiniteAdicConstructibleSmall

Source: Bhatt--Scholze, Section 6.8; native realization proof
(blueprint: lem-sf-locally-finite-adic-constructible-small).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- Essential smallness of the native target, independently of a realization functor.

Source: the essential-smallness addendum in step 8 of the native realization node,
using BBD 1.3.3--1.3.6 and constructible-module presentation counting
(blueprint: lem-sf-locally-finite-adic-constructible-small).

Proof in words: the native internal-module convention is equivalent to the abelian
sheaf-module convention by restriction of the constant scalar action and its inverse
balanced action. On each Noetherian stratum finite-free modules are finitely presented.
A finite open subcover makes the locally given finite stratifications into one finite
stratification, by disjointifying the opens and restricting their strata. Apply
constructibleModuleObjects_essentiallySmall to obtain a small family of representatives
of the native constructible modules, transported through that equivalence. Their degree
zero complexes and all integer shifts form a small family in the ordinary derived
category. For an interval [a,b], exists_bounded_postnikov_tower builds every object with
constructible cohomology in that interval from b-a+1 of these factors. At each extension
step essentiallySmall_extensionProduct bounds the possible middle objects: connecting
morphisms between representatives lie in small Hom sets. Induction therefore gives a
small family for each interval. Take the union over the small set of pairs of integers
a,b. It contains a representative of every bounded constructible object. The full
subcategory inherits small Hom sets from the ambient derived category in the same
site/coefficient universe, proving EssentiallySmall at u+1. Zero objects are included;
for an empty interval the Postnikov tower has no factors and ends at zero. No field
of definition, Hom descent, or functor J is needed.
-/
theorem nativeConstructible_essentiallySmall
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X] :
    EssentiallySmall.{u + 1}
      (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory := by
  have : ObjectProperty.EssentiallySmall.{u + 1} (ProEtale.adicConstructibleSheaf l X) :=
    nativeConstructibleSheaf_essentiallySmall l X
  have : ObjectProperty.EssentiallySmall.{u + 1}
      (ProEtale.DerivedCategory.boundedAdicConstructible l X) :=
    DerivedCategory.essentiallySmall_bounded_inf (ProEtale.adicConstructibleSheaf l X)
  infer_instance

end WeilConjectures.LocallyFiniteAdicRealization
