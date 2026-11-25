/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.Etale
public import WeilConjectures.RingTheory.ProEtale.Contraction.Covers
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Successive adjoining of étale sections

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node theorem-existence-contractible-covers--1, order 1226
(blueprint: theorem-existence-contractible-covers--1).

We work dually in commutative rings: finite wide pullbacks are finite tensor
coproducts, and the two limits below are the two ring colimits in the source.
Taking the skeleton of the small model ensures exactly one representative per
algebra isomorphism class, rather than one factor for every object of the model.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CommRingCat.EtaleContraction

/-- Representatives of faithfully flat étale algebras, in the fixed universe `u`.
Étale ring maps are of finite presentation. Source: blueprint order 1226
(blueprint: theorem-existence-contractible-covers--1). -/
abbrev Representatives (R : CommRingCat.{u}ᵒᵖ) : Type u :=
  Skeleton (SmallModel.{u} ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R))

/-- The finite tensor coproducts and their canonical inclusion maps, written dually.
`FiniteFamilies` includes the empty subset, whose wide pullback is the base ring.
Source: blueprint order 1226 (blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def finiteDiagram (R : CommRingCat.{u}ᵒᵖ) :
    (FiniteFamilies (Representatives R))ᵒᵖ ⥤ Over R :=
  (FiniteFamilies.map (fromSkeleton (SmallModel.{u}
    ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R)))).op ⋙
      FiniteFamilies.diag (CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op) R

/-- Adjoin all the representatives by the filtered colimit of finite tensor coproducts.
Its structural map is the arrow of this `Over` object. Source: blueprint order 1226
(blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def step (R : CommRingCat.{u}ᵒᵖ) : Over R :=
  limit (finiteDiagram R)

/-- The successive rings, with `stage R 0 = R`. Source: blueprint order 1226
(blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def stage (R : CommRingCat.{u}ᵒᵖ) : ℕ → CommRingCat.{u}ᵒᵖ
  | 0 => R
  | n + 1 => (step (stage R n)).left

/-- The sequential diagram with the structural maps from the finite-tensor colimits.
Source: blueprint order 1226 (blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def sequence (R : CommRingCat.{u}ᵒᵖ) : ℕᵒᵖ ⥤ CommRingCat.{u}ᵒᵖ :=
  Functor.ofOpSequence (X := stage R) (fun n ↦ (step (stage R n)).hom)

end CommRingCat.EtaleContraction

/-- The ring `Rᵉ`, the sequential colimit of the successive tensor coproducts of one
representative of each faithfully flat étale algebra of finite presentation.
Both colimits carry their canonical maps and universal properties from `limit` in
the opposite category. Source: blueprint order 1226
(blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def CommRingCat.etaleContraction (R : CommRingCat.{u}) : CommRingCat.{u} :=
  (limit (EtaleContraction.sequence (op R))).unop

/-- The canonical map of the `n`-th ring to `Rᵉ`. Source: blueprint order 1226
(blueprint: theorem-existence-contractible-covers--1). -/
noncomputable def CommRingCat.EtaleContraction.ι (R : CommRingCat.{u}) (n : ℕ) :
    (stage (op R) n).unop ⟶ R.etaleContraction :=
  (limit.π (sequence (op R)) (op n)).unop
