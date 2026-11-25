/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.CategoryTheory.DerivedCategory.ZetaWeil.RingDerivedDualizablePerfect
public import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.LocalSite

set_option linter.privateModule false

/-! # Perfect complexes and dualizable objects under contractible evaluation

Source: Hemo--Richarz--Scholbach, Section 3, (3.1)--(3.2), Remark 3.2,
Lemma 4.1 and Proposition 4.3(3)
(blueprint: lem-zl-contractible-lisse-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Duality

variable {V W : Type*} [Category* V] [Category* W]
  [MonoidalCategory V] [MonoidalCategory W]

omit [MonoidalCategory V] [MonoidalCategory W] in
omit [MonoidalCategory V] [MonoidalCategory W] in
omit [MonoidalCategory V] [MonoidalCategory W] in
private theorem restriction_equivalence {L : V ⥤ W} {H : W ⥤ V}
    (adj : L ⊣ H) [IsIso adj.unit] (P : ObjectProperty V) (Q : ObjectProperty W)
    (hL : ∀ X, P X → Q (L.obj X)) (hH : ∀ X, Q X → P (H.obj X))
    (hmap : ∀ X Y, Q X → Q Y → Function.Bijective (H.map : (X ⟶ Y) → _)) :
    ∃ e : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (e.functor ⋙ Q.ι ≅ P.ι ⋙ L) ∧
      Nonempty (e.inverse ⋙ P.ι ≅ Q.ι ⋙ H) := by
  let L' := Q.lift (P.ι ⋙ L) (fun X ↦ hL X.obj X.property)
  let H' := P.lift (Q.ι ⋙ H) (fun X ↦ hH X.obj X.property)
  let adj' : L' ⊣ H' := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  let := adj.fullyFaithfulLOfIsIsoUnit.full
  let := adj.fullyFaithfulLOfIsIsoUnit.faithful
  let : H'.Full := ⟨fun {X Y} f ↦ by
    obtain ⟨g, hg⟩ := (hmap X.obj Y.obj X.property Y.property).2 f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩⟩
  let : H'.Faithful := ⟨fun {X Y} {f g} h ↦ by
    apply ObjectProperty.hom_ext
    apply (hmap X.obj Y.obj X.property Y.property).1
    exact congrArg (fun k ↦ k.hom) h⟩
  exact ⟨adj'.toEquivalence, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

end Duality

end AlgebraicGeometry.ProEtale.CondensedRing
