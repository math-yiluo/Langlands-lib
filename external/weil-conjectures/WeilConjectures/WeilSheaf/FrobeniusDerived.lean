/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# The derived Frobenius isomorphism of a Weil complex

Blueprint `definition-weil-structure`: an object `K` of the Weil category carries, in addition
to its underlying complex `For(K)`, the derived Frobenius isomorphism
`θ_K : Fr_X^* For(K) ≅ For(K)`, represented termwise. Here `For`
(`AlgebraicGeometry.WeilComplex.forget`) is induced by the forgetful functor from pro-étale Weil
sheaves to pro-étale `ℓ`-adic sheaves, and the structure isomorphisms `φ : Fr_X^* F ≅ F` of the
Weil sheaves form a natural isomorphism `Fr_X^* ∘ forget ≅ forget`
(`CategoryTheory.Endofunctor.IsoAlgebra.forgetCompIso`); `θ` is the isomorphism it induces on
derived categories (`AlgebraicGeometry.WeilComplex.frobeniusIso`). The Frobenius pullback
`Fr_X^*` is exact, being an equivalence, so it needs no deriving.

## Main definitions

- `CategoryTheory.Endofunctor.IsoAlgebra.forgetCompIso`: `F ∘ forget ≅ forget`.
- `AlgebraicGeometry.WeilComplex.frobeniusIso`: `θ : Fr_X^* ∘ For ≅ For`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category C] (F : C ⥤ C)

/-- The structure isomorphisms `F a ≅ a` of the algebras with invertible structure morphism of
`F` form a natural isomorphism `F ∘ forget ≅ forget`. -/
noncomputable def forgetCompIso : forget F ⋙ F ≅ forget F :=
  NatIso.ofComponents (fun K ↦ K.str) (fun φ ↦ φ.hom.h)

@[simp]
lemma forgetCompIso_hom_app (K : IsoAlgebra F) : (forgetCompIso F).hom.app K = K.obj.str :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry

namespace WeilComplex

open Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex.

The derived Frobenius isomorphism `θ_K : Fr_X^* For(K) ≅ For(K)` of a Weil complex `K`, natural
in `K`: the isomorphism induced on derived categories by the structure isomorphisms
`φ : Fr_X^* F ≅ F` of pro-étale Weil sheaves, through
`D(Fr_X^*) ∘ D(forget) ≅ D(Fr_X^* ∘ forget) ≅ D(forget)`. Here `Fr_X^*`
(`AlgebraicGeometry.WeilSheaf.frobeniusPullback`) is the pullback along the geometric Frobenius
`g_X` of the blueprint; it is exact, so its derived functor `Lg_X^*` is the functor it induces on
derived categories. -/
noncomputable def frobeniusIso :
    forget (k₀ := k₀) (l := l) (X := X) ⋙ (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory ≅
      forget (X := X) :=
  let F := WeilSheaf.frobeniusPullback k₀ l X
  let e : IsoAlgebra.forget F ⋙ F ≅ IsoAlgebra.forget F :=
    IsoAlgebra.forgetCompIso F
  let c : (IsoAlgebra.forget F ⋙ F).mapDerivedCategory ≅
      (IsoAlgebra.forget F).mapDerivedCategory ⋙ F.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget F) F).symm
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
    (c.symm ≪≫ Functor.mapDerivedCategoryNatIso e)

end WeilComplex

end AlgebraicGeometry
