/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Abelian

/-!
# The constructible heart with coefficients in a finite extension of `ℚ_ℓ`

Let `Λ` be a field with an ultrametric norm, for instance a finite extension `E` of `ℚ_ℓ` inside
`ℚ̄_ℓ`, and `X` a scheme. The bounded constructible derived category `D^b_c(X, Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible`) is cut out of the
derived category of sheaves of `Λ_X`-modules on the pro-étale site
(`AlgebraicGeometry.ProEtale.FieldSheaf`) by boundedness and constructibility of the cohomology
sheaves. It is stable under the canonical truncations `τ^{≤ n}` and `τ^{≥ n}`, so it inherits the
standard `t`-structure, and its heart `D^{≤ 0}_c ∩ D^{≥ 0}_c`
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`) is equivalent, by
placing sheaves in degree `0`, to the category `Sh_c(X, Λ)` of constructible `Λ`-adic sheaves
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeartEquiv`), which is abelian on
a locally Noetherian scheme.

This is the constructible heart at the stage `Λ = E`, in the Bhatt–Scholze
model of `D^b_c(X, E)` (*The pro-étale topology for schemes*, §6.8): `E_X`-modules on the
pro-étale site with constructible cohomology. The stage `ℚ̄_ℓ` is
`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeart`.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible`: `D^b_c(X, Λ)`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`: the constructible
  heart.
- `AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeartEquiv`:
  `Sh_c(X, Λ) ≌ D^{≤ 0}_c(X, Λ) ∩ D^{≥ 0}_c(X, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedField Λ] [IsUltrametricDist Λ]

/-- The category `Sh_c(X, Λ)` of constructible `Λ`-adic sheaves on a locally Noetherian scheme
is abelian: constructible sheaves are closed under kernels, cokernels and finite products. -/
noncomputable instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Abelian (fieldConstructibleSheaf Λ X).FullSubcategory :=
  inferInstance

/-- The stage `D^b_c(X, Λ)`, as an object property of `D(X_proét, Λ)`: the complexes of
sheaves of `Λ_X`-modules which are bounded, with constructible cohomology sheaves. -/
def DerivedCategory.boundedFieldConstructible (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (FieldSheaf Λ X)) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (fieldConstructibleSheaf Λ X)

variable {Λ} {X : Scheme.{u}}

/-- `D^b_c(X, Λ)` is stable under the truncation `τ^{≤ n}` of the canonical t-structure: the
cohomology sheaves of `τ^{≤ n} K` are those of `K` in degrees `≤ n`, and zero above. -/
lemma DerivedCategory.boundedFieldConstructible_truncLE
    {K : _root_.DerivedCategory (FieldSheaf Λ X)}
    (hK : DerivedCategory.boundedFieldConstructible Λ X K) (n : ℤ) :
    DerivedCategory.boundedFieldConstructible Λ X
      ((_root_.DerivedCategory.TStructure.t.truncLE n).obj K) := by
  obtain ⟨⟨⟨a, ha⟩, -⟩, hc⟩ := hK
  exact ⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
    _root_.DerivedCategory.homologyProperty_truncLE hc n⟩

/-- `D^b_c(X, Λ)` is stable under the truncation `τ^{≥ n}` of the canonical t-structure: the
cohomology sheaves of `τ^{≥ n} K` are those of `K` in degrees `≥ n`, and zero below. -/
lemma DerivedCategory.boundedFieldConstructible_truncGE
    {K : _root_.DerivedCategory (FieldSheaf Λ X)}
    (hK : DerivedCategory.boundedFieldConstructible Λ X K) (n : ℤ) :
    DerivedCategory.boundedFieldConstructible Λ X
      ((_root_.DerivedCategory.TStructure.t.truncGE n).obj K) := by
  obtain ⟨⟨-, ⟨b, hb⟩⟩, hc⟩ := hK
  exact ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
    _root_.DerivedCategory.homologyProperty_truncGE hc n⟩

namespace DerivedCategory

variable (Λ X) in
/-- Constructible heart, stage `Λ = E`.

The heart `D^{≤ 0}_c(X, Λ) ∩ D^{≥ 0}_c(X, Λ)` of the standard `t`-structure on the bounded
constructible derived category `D^b_c(X, Λ)`, as an object property of `D(X_proét, Λ)`: the
bounded constructible complexes `K` with `τ^{≥ 1} K = 0` and `τ^{≤ -1} K = 0`. For `Λ = E` a
finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` this is `Sh_c(Y, E)` of the blueprint: its objects are
the constructible `E`-adic sheaves placed in degree `0`
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart_iff`), and it is
equivalent to the abelian category of constructible `E`-adic sheaves
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeartEquiv`). The truncations are
those of the canonical `t`-structure, which preserve `D^b_c(X, Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible_truncLE`,
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible_truncGE`). The stage
`ℚ̄_ℓ` is `AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeart`. -/
def fieldConstructibleHeart : ObjectProperty (_root_.DerivedCategory (FieldSheaf Λ X)) :=
  boundedFieldConstructible Λ X ⊓ _root_.DerivedCategory.TStructure.t.le 0 ⊓
    _root_.DerivedCategory.TStructure.t.ge 0

instance : (fieldConstructibleHeart Λ X).IsClosedUnderIsomorphisms := by
  dsimp only [fieldConstructibleHeart, boundedFieldConstructible]
  infer_instance

/-- A constructible `Λ`-adic sheaf placed in degree `0` lies in the constructible heart. -/
lemma fieldConstructibleHeart_singleFunctor_obj {F : FieldSheaf Λ X}
    (hF : fieldConstructibleSheaf Λ X F) :
    fieldConstructibleHeart Λ X ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  have hle : _root_.DerivedCategory.IsLE ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0 :=
    inferInstance
  have hge : _root_.DerivedCategory.IsGE ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0 :=
    inferInstance
  refine ⟨⟨⟨⟨⟨0, hge⟩, ⟨0, hle⟩⟩, fun m ↦ ?_⟩, hle.le⟩, hge.ge⟩
  obtain hm | rfl | hm := lt_trichotomy m 0
  · exact (fieldConstructibleSheaf Λ X).prop_of_isZero
      ((_root_.DerivedCategory.isGE_iff _ 0).1 hge m hm)
  · exact (fieldConstructibleSheaf Λ X).prop_of_iso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · exact (fieldConstructibleSheaf Λ X).prop_of_isZero
      ((_root_.DerivedCategory.isLE_iff _ 0).1 hle m hm)

/-- The constructible heart consists of the complexes isomorphic to a constructible `ℓ`-adic
sheaf placed in degree `0`. -/
theorem fieldConstructibleHeart_iff (K : _root_.DerivedCategory (FieldSheaf Λ X)) :
    fieldConstructibleHeart Λ X K ↔ ∃ F : FieldSheaf Λ X, fieldConstructibleSheaf Λ X F ∧
      Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  refine ⟨fun ⟨⟨⟨_, hK⟩, hle⟩, hge⟩ ↦ ?_, fun ⟨F, hF, ⟨e⟩⟩ ↦ ?_⟩
  · have : _root_.DerivedCategory.IsLE K 0 := ⟨hle⟩
    have : _root_.DerivedCategory.IsGE K 0 := ⟨hge⟩
    obtain ⟨F, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
    refine ⟨F, (fieldConstructibleSheaf Λ X).prop_of_iso ?_ (hK 0), ⟨e⟩⟩
    exact (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F
  · exact (fieldConstructibleHeart Λ X).prop_of_iso e.symm
      (fieldConstructibleHeart_singleFunctor_obj hF)

/-- Placing a constructible `Λ`-adic sheaf in degree `0`, as a functor from `Sh_c(X, Λ)` to
the constructible heart. -/
noncomputable def toFieldConstructibleHeart :
    (fieldConstructibleSheaf Λ X).FullSubcategory ⥤
      (fieldConstructibleHeart Λ X).FullSubcategory :=
  ObjectProperty.liftFullSubcategory (fieldConstructibleSheaf Λ X) (fieldConstructibleHeart Λ X)
    (_root_.DerivedCategory.singleFunctor _ 0) fun _ hF ↦
      fieldConstructibleHeart_singleFunctor_obj hF

instance : (toFieldConstructibleHeart (Λ := Λ) (X := X)).Full :=
  ObjectProperty.liftFullSubcategory_full _ _ _ _

instance : (toFieldConstructibleHeart (Λ := Λ) (X := X)).Faithful :=
  ObjectProperty.liftFullSubcategory_faithful _ _ _ _

instance : (toFieldConstructibleHeart (Λ := Λ) (X := X)).EssSurj where
  mem_essImage K := by
    obtain ⟨F, hF, ⟨e⟩⟩ := (fieldConstructibleHeart_iff K.obj).1 K.property
    exact ⟨⟨F, hF⟩, ⟨ObjectProperty.isoMk _ e.symm⟩⟩

/-- The constructible heart is equivalent to the category `Sh_c(X, Λ)` of constructible
`Λ`-adic sheaves, by placing sheaves in degree `0`. -/
noncomputable def fieldConstructibleHeartEquiv :
    (fieldConstructibleSheaf Λ X).FullSubcategory ≌
      (fieldConstructibleHeart Λ X).FullSubcategory :=
  have : (toFieldConstructibleHeart (Λ := Λ) (X := X)).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  (toFieldConstructibleHeart (Λ := Λ) (X := X)).asEquivalence

end DerivedCategory

end AlgebraicGeometry.ProEtale
