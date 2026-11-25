/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicConstructibilityEncoding
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall

/-! # LocallyFiniteAdicConstructibleSheafSmall

Source: Bhatt--Scholze, Section 6.8; native realization proof
(blueprint: lem-sf-locally-finite-adic-constructible-sheaf-small).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- A small family of native constructible sheaves, before passage to complexes.

Source: native realization proof step 8, constructible-module presentation counting;
Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.8
(blueprint: lem-sf-locally-finite-adic-constructible-sheaf-small).

Proof in words: forget the constant coefficient action from a native internal module
to obtain a module in abelian sheaves over abRing. Conversely, restrict its action
along the constants into the coefficient ring to recover that constant scalar action;
the unit and balancing identities show these constructions are inverse equivalences,
on morphisms as well as objects. They preserve restrictions and take the native unit
to the regular module. Thus a native finite-free local model gives a finite-free, hence
finitely presented, abelian-sheaf-module model. For a constructible sheaf take a finite
subcover of its open stratified-lisse neighborhoods. Replace each open by its difference
with the preceding opens and intersect its strata with this piece. This produces one
finite locally closed stratification of X and a finite-presentation cover on each
stratum. The construction uses only quasi-compactness and Noetherianity, not dimension
or invertibility. In Lean this equivalence is the normalized native encoding
NativeEncoding.encoding, and encoding_constructible_iff is the constructibility comparison
on Noetherian X.
Apply constructibleModuleObjects_essentiallySmall to the resulting
constructible modules over abRing. A fully faithful functor into that essentially small
full subcategory makes the native full subcategory essentially small. Equivalently,
its property has a small family of representatives. The equivalence and finite-cover
argument include empty schemes, empty strata and rank-zero modules.
-/
theorem nativeConstructibleSheaf_essentiallySmall
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.EssentiallySmall.{u + 1} (ProEtale.adicConstructibleSheaf l X) := by
  let P := ProEtale.adicConstructibleSheaf l X
  let Q : ObjectProperty _ := ProEtale.IsConstructibleModuleObject
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X)
  have : ObjectProperty.EssentiallySmall.{u + 1} Q :=
    ProEtale.constructibleModuleObjects_essentiallySmall X _
  let F := Q.lift (P.ι ⋙ ProEtale.NativeEncoding.encoding l X)
    (fun M ↦ (ProEtale.encoding_constructible_iff M.obj).mp M.property)
  have : F.Full := by dsimp only [F]; infer_instance
  have : F.Faithful := by dsimp only [F]; infer_instance
  have : EssentiallySmall.{u + 1} P.FullSubcategory :=
    essentiallySmall_of_fully_faithful F
  have h : ObjectProperty.EssentiallySmall.{u + 1} P.ι.essImage := inferInstance
  exact ObjectProperty.EssentiallySmall.of_le
    (Q := P.ι.essImage) (fun M hM ↦ ⟨⟨M, hM⟩, ⟨Iso.refl M⟩⟩)

end WeilConjectures.LocallyFiniteAdicRealization
