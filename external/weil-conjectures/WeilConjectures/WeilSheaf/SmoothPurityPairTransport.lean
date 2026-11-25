/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTensorPowerInduction

/-! # Transporting a pair isomorphism between Frobenius conventions -/

@[expose] public section

open CategoryTheory Endofunctor

namespace CategoryTheory

/-- Transport an equivariant isomorphism along an isomorphism of endofunctors,
retaining the named structure isomorphisms in the conclusion. -/
noncomputable def purity_pairIso_transport
    {C : Type*} [Category C] {P L : C ⥤ C} (u : P ≅ L)
    {A B : C} (φ : P.obj A ≅ A) (ψ : P.obj B ≅ B)
    (a : L.obj A ≅ A) (b : L.obj B ≅ B)
    (ha : a = (u.app A).symm ≪≫ φ) (hb : b = (u.app B).symm ≪≫ ψ)
    (e : A ≅ B) (he : P.map e.hom ≫ ψ.hom = φ.hom ≫ e.hom) :
    IsoAlgebra.mk A a ≅ IsoAlgebra.mk B b := by
  subst a
  subst b
  refine IsoAlgebra.isoMk e ?_
  change L.map e.hom ≫ (u.inv.app B ≫ ψ.hom) =
    (u.inv.app A ≫ φ.hom) ≫ e.hom
  rw [← Category.assoc, u.inv.naturality, Category.assoc, he, Category.assoc]

end CategoryTheory
