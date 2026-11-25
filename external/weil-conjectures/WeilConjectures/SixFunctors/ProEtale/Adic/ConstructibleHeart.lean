/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation

/-!
# The constructible heart

Let `X` be a scheme. The bounded constructible derived category `D^b_c(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible`) inherits the standard
`t`-structure (blueprint `prop-constructible-truncations`). Its heart
`D^{≤ 0}_c ∩ D^{≥ 0}_c` (`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeart`)
consists of the complexes isomorphic to a constructible `ℓ`-adic sheaf placed in degree `0`
(`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeart_iff`), and placing sheaves
in degree `0` is an equivalence from the abelian category `Sh_c(X, ℚ̄_ℓ)` of constructible
`ℓ`-adic sheaves onto it (`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeartEquiv`).

## Implementation notes

The blueprint defines the heart at the stages `E` and `ℚ̄_ℓ`. This file treats the stage `ℚ̄_ℓ`;
the stage `E`, in the same Bhatt–Scholze model of sheaves of modules over the constant sheaf
`E_X : U ↦ C(U, E)`, is
`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`
(`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleHeart`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.DerivedCategory

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- Constructible heart.

The heart `D^{≤ 0}_c(X, ℚ̄_ℓ) ∩ D^{≥ 0}_c(X, ℚ̄_ℓ)` of the standard `t`-structure on the
bounded constructible derived category `D^b_c(X, ℚ̄_ℓ)`, as an object property of
`D(X_proét, ℚ̄_ℓ)`: the bounded constructible complexes `K` with `τ^{≥ 1} K = 0` and
`τ^{≤ -1} K = 0`. Its objects are the constructible `ℓ`-adic sheaves placed in degree `0`
(`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeart_iff`); it is equivalent to
the abelian category `Sh_c(X, ℚ̄_ℓ)` of constructible `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeartEquiv`), whose objects have
finite-level reductions satisfying the finite-torsion constructibility condition (see
`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`).

This is the stage `ℚ̄_ℓ` of the blueprint node; the stage `E` is
`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`. -/
def adicConstructibleHeart : ObjectProperty (_root_.DerivedCategory (AdicSheaf l X)) :=
  boundedAdicConstructible l X ⊓ _root_.DerivedCategory.TStructure.t.le 0 ⊓
    _root_.DerivedCategory.TStructure.t.ge 0

instance : (adicConstructibleHeart l X).IsClosedUnderIsomorphisms := by
  dsimp only [adicConstructibleHeart, boundedAdicConstructible]
  infer_instance

variable {l X}

/-- A constructible `ℓ`-adic sheaf placed in degree `0` lies in the constructible heart. -/
lemma adicConstructibleHeart_singleFunctor_obj {F : AdicSheaf l X}
    (hF : adicConstructibleSheaf l X F) :
    adicConstructibleHeart l X ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  have hle : _root_.DerivedCategory.IsLE ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0 :=
    inferInstance
  have hge : _root_.DerivedCategory.IsGE ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0 :=
    inferInstance
  refine ⟨⟨⟨⟨⟨0, hge⟩, ⟨0, hle⟩⟩, fun m ↦ ?_⟩, hle.le⟩, hge.ge⟩
  obtain hm | rfl | hm := lt_trichotomy m 0
  · exact (adicConstructibleSheaf l X).prop_of_isZero
      ((_root_.DerivedCategory.isGE_iff _ 0).1 hge m hm)
  · exact (adicConstructibleSheaf l X).prop_of_iso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · exact (adicConstructibleSheaf l X).prop_of_isZero
      ((_root_.DerivedCategory.isLE_iff _ 0).1 hle m hm)

/-- The constructible heart consists of the complexes isomorphic to a constructible `ℓ`-adic
sheaf placed in degree `0`. -/
theorem adicConstructibleHeart_iff (K : _root_.DerivedCategory (AdicSheaf l X)) :
    adicConstructibleHeart l X K ↔ ∃ F : AdicSheaf l X, adicConstructibleSheaf l X F ∧
      Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  refine ⟨fun ⟨⟨⟨_, hK⟩, hle⟩, hge⟩ ↦ ?_, fun ⟨F, hF, ⟨e⟩⟩ ↦ ?_⟩
  · have : _root_.DerivedCategory.IsLE K 0 := ⟨hle⟩
    have : _root_.DerivedCategory.IsGE K 0 := ⟨hge⟩
    obtain ⟨F, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
    refine ⟨F, (adicConstructibleSheaf l X).prop_of_iso ?_ (hK 0), ⟨e⟩⟩
    exact (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F
  · exact (adicConstructibleHeart l X).prop_of_iso e.symm
      (adicConstructibleHeart_singleFunctor_obj hF)

/-- Placing a constructible `ℓ`-adic sheaf in degree `0`, as a functor from `Sh_c(X, ℚ̄_ℓ)` to
the constructible heart. -/
noncomputable def toAdicConstructibleHeart :
    (adicConstructibleSheaf l X).FullSubcategory ⥤ (adicConstructibleHeart l X).FullSubcategory :=
  ObjectProperty.liftFullSubcategory (adicConstructibleSheaf l X) (adicConstructibleHeart l X)
    (_root_.DerivedCategory.singleFunctor _ 0) fun _ hF ↦
      adicConstructibleHeart_singleFunctor_obj hF

instance : (toAdicConstructibleHeart (l := l) (X := X)).Full :=
  ObjectProperty.liftFullSubcategory_full _ _ _ _

instance : (toAdicConstructibleHeart (l := l) (X := X)).Faithful :=
  ObjectProperty.liftFullSubcategory_faithful _ _ _ _

instance : (toAdicConstructibleHeart (l := l) (X := X)).EssSurj where
  mem_essImage K := by
    obtain ⟨F, hF, ⟨e⟩⟩ := (adicConstructibleHeart_iff K.obj).1 K.property
    exact ⟨⟨F, hF⟩, ⟨ObjectProperty.isoMk _ e.symm⟩⟩

/-- The constructible heart is equivalent to the category `Sh_c(X, ℚ̄_ℓ)` of constructible
`ℓ`-adic sheaves, by placing sheaves in degree `0`. -/
noncomputable def adicConstructibleHeartEquiv :
    (adicConstructibleSheaf l X).FullSubcategory ≌ (adicConstructibleHeart l X).FullSubcategory :=
  have : (toAdicConstructibleHeart (l := l) (X := X)).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  (toAdicConstructibleHeart (l := l) (X := X)).asEquivalence

end AlgebraicGeometry.ProEtale.DerivedCategory
