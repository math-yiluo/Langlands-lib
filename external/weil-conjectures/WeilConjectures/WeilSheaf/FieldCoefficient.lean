/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleHeart
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius
public import WeilConjectures.WeilSheaf.FrobeniusDerived

/-!
# Weil sheaves and Weil complexes with coefficients in a finite extension of `ℚ_ℓ`

Let `k₀` be a finite field with algebraic closure `k̄`, `X` a scheme over `k₀`, `X̄ = X ×_{k₀} k̄`
its geometric fiber and `Fr_X : X̄ ≅ X̄` its geometric Galois Frobenius. Let `Λ` be a field with
an ultrametric norm; the case of the blueprint is a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`,
`ℓ` prime to the characteristic of `k₀`. Following blueprint `definition-weil-structure`,

- a *constructible `E`-Weil sheaf* on `X` is a constructible `E`-adic sheaf `F` on the pro-étale
  site of `X̄`, an object of `Sh_c(X̄, E)`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`), together with an
  isomorphism `θ : Fr_X^* F ≅ F` (`AlgebraicGeometry.FieldWeilSheaf`);
- `D^b_{c,W}(X, E)` is the triangulated category obtained from complexes of such sheaves by
  inverting the equivariant quasi-isomorphisms (`AlgebraicGeometry.FieldWeilComplex`);
- the forgetful functor `For : D^b_{c,W}(X, E) ⥤ D^b_c(X̄, E)`
  (`AlgebraicGeometry.FieldWeilComplex.forgetBoundedConstructible`) is exact, and every object
  `K` carries the derived Frobenius isomorphism `θ_K : Fr_X^* For(K) ≅ For(K)`
  (`AlgebraicGeometry.FieldWeilComplex.frobeniusIso`).

This is the construction of `WeilConjectures.WeilSheaf.Category` (the stage `ℚ̄_ℓ`,
`AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`) with the coefficients `ℚ̄_ℓ`
replaced by `Λ`: the sheaves are modules over the constant sheaf `Λ_X̄ : U ↦ C(U, Λ)` of
Bhatt–Scholze (`AlgebraicGeometry.ProEtale.FieldSheaf`), the Frobenius pullback is the
pushforward along `Fr_X⁻¹`, and the Weil complexes are the bounded objects with constructible
cohomology of the derived category of pro-étale Weil sheaves, all of whose terms carry a Weil
structure, so that `θ` is represented termwise. The functors from the stages `E` to the stage
`ℚ̄_ℓ`, induced by the extension of scalars `ℚ̄_ℓ ⊗_E -`, are
`AlgebraicGeometry.FieldWeilComplex.toWeilComplex`
(`WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars`).

## Main definitions

- `AlgebraicGeometry.ProEtaleFieldWeilSheaf`: pro-étale `Λ`-sheaves with a Weil structure.
- `AlgebraicGeometry.FieldWeilSheaf` and `AlgebraicGeometry.FieldWeilComplex`: constructible
  `Λ`-Weil sheaves (an abelian category) and `D^b_{c,W}(X, Λ)` (a triangulated category).
- `AlgebraicGeometry.FieldWeilComplex.forget` and
  `AlgebraicGeometry.FieldWeilComplex.forgetBoundedConstructible`: the forgetful functor `For`.
- `AlgebraicGeometry.FieldWeilComplex.frobeniusIso`: `θ : Fr_X^* ∘ For ≅ For`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Frobenius

variable (k₀ : Type u) [Field k₀] [Finite k₀] (Λ : Type) [NormedField Λ] [IsUltrametricDist Λ]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius pullback `Fr_X^*` of `Λ`-adic pro-étale sheaves on the geometric fiber `X̄`,
along its geometric Galois Frobenius `Fr_X`, realized as the pushforward along `Fr_X⁻¹`, which is
isomorphic to the pullback along `Fr_X`
(`AlgebraicGeometry.ProEtale.fieldUpperStarIsoLowerStarInv`). -/
noncomputable abbrev FieldWeilSheaf.frobeniusPullback :
    FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ]

/-- The Frobenius pullback is an equivalence, `Fr_X` being an automorphism. -/
instance : (FieldWeilSheaf.frobeniusPullback k₀ Λ X).IsEquivalence :=
  isEquivalence_fieldLowerStar _ _

/-- The category of all `Λ`-adic pro-étale sheaves on the geometric fiber `X̄` with a Weil
structure: pairs of a sheaf `F` of `Λ_X̄`-modules on `X̄_proét` and an isomorphism
`θ : Fr_X^* F ≅ F`, with the morphisms of sheaves commuting with the `θ`'s. -/
abbrev ProEtaleFieldWeilSheaf :=
  IsoAlgebra (FieldWeilSheaf.frobeniusPullback k₀ Λ X)

instance : IsGrothendieckAbelian.{u + 1} (ProEtaleFieldWeilSheaf k₀ Λ X) :=
  IsoAlgebra.isGrothendieckAbelian _

/-- The property of a pro-étale `Λ`-sheaf with a Weil structure that the underlying sheaf is
constructible; it cuts out the constructible `Λ`-Weil sheaves. -/
noncomputable abbrev FieldWeilSheaf.objectProperty :
    ObjectProperty (ProEtaleFieldWeilSheaf k₀ Λ X) :=
  (fieldConstructibleSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage
    (IsoAlgebra.forget _)

/-- The property of an object `K` of the derived category of pro-étale `Λ`-Weil sheaves that it
is bounded and that its cohomology objects are constructible `Λ`-Weil sheaves; it cuts out
`D^b_{c,W}(X, Λ)`. -/
noncomputable abbrev FieldWeilComplex.objectProperty :
    ObjectProperty (_root_.DerivedCategory (ProEtaleFieldWeilSheaf k₀ Λ X)) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (FieldWeilSheaf.objectProperty k₀ Λ X)

end Frobenius

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex, stage `Λ = E`.

The category of constructible `Λ`-Weil sheaves on a `k₀`-scheme `X`, for `Λ` a finite extension
`E` of `ℚ_ℓ`: constructible `E`-adic sheaves `F` on the pro-étale site of the geometric fiber
`X̄` (objects of `Sh_c(X̄, E)`, `AlgebraicGeometry.ProEtale.fieldConstructibleSheaf`) with an
isomorphism `θ : Fr_X^* F ≅ F`, where `Fr_X` is the geometric Galois Frobenius of `X̄`; the
morphisms are the morphisms of sheaves commuting with the `θ`'s. The stage `ℚ̄_ℓ` is
`AlgebraicGeometry.WeilSheaf`. -/
def FieldWeilSheaf (k₀ : Type u) [Field k₀] [Finite k₀] (Λ : Type) [NormedField Λ]
    [IsUltrametricDist Λ] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (FieldWeilSheaf.objectProperty k₀ Λ X).FullSubcategory

/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex, stage `Λ = E`.

The triangulated category `D^b_{c,W}(X, E)` of `E`-Weil complexes on a `k₀`-scheme `X`, for
`Λ = E` a finite extension of `ℚ_ℓ`: the objects of the derived category of pro-étale `E`-Weil
sheaves on `X̄` (the localization of the homotopy category of complexes of pro-étale `E`-Weil
sheaves at the equivariant quasi-isomorphisms) which are bounded with constructible cohomology.
Its objects carry the derived Frobenius isomorphism
(`AlgebraicGeometry.FieldWeilComplex.frobeniusIso`), and forgetting it is the exact functor
`For : D^b_{c,W}(X, E) ⥤ D^b_c(X̄, E)`
(`AlgebraicGeometry.FieldWeilComplex.forgetBoundedConstructible`). The stage `ℚ̄_ℓ` is
`AlgebraicGeometry.WeilComplex`, which `D^b_{c,W}(X, E)` maps to by extension of scalars
(`AlgebraicGeometry.FieldWeilComplex.toWeilComplex`). -/
def FieldWeilComplex (k₀ : Type u) [Field k₀] [Finite k₀] (Λ : Type) [NormedField Λ]
    [IsUltrametricDist Λ] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

noncomputable instance : Category (FieldWeilSheaf k₀ Λ X) :=
  inferInstanceAs (Category (FieldWeilSheaf.objectProperty k₀ Λ X).FullSubcategory)

noncomputable instance FieldWeilSheaf.instAbelian
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    Abelian (FieldWeilSheaf k₀ Λ X) := by
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).IsClosedUnderKernels := inferInstance
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).IsClosedUnderCokernels := inferInstance
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).IsClosedUnderFiniteProducts := inferInstance
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).ContainsZero := inferInstance
  exact inferInstanceAs (Abelian (FieldWeilSheaf.objectProperty k₀ Λ X).FullSubcategory)

noncomputable instance : Preadditive (FieldWeilSheaf k₀ Λ X) :=
  inferInstanceAs (Preadditive (FieldWeilSheaf.objectProperty k₀ Λ X).FullSubcategory)

instance FieldWeilComplex.isTriangulated_objectProperty
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (FieldWeilComplex.objectProperty k₀ Λ X).IsTriangulated := by
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).IsClosedUnderKernels := inferInstance
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).IsClosedUnderCokernels := inferInstance
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).IsClosedUnderExtensions := inferInstance
  have : (FieldWeilSheaf.objectProperty k₀ Λ X).ContainsZero := inferInstance
  infer_instance

noncomputable instance : Category (FieldWeilComplex k₀ Λ X) :=
  inferInstanceAs (Category (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory)

noncomputable instance : Preadditive (FieldWeilComplex k₀ Λ X) :=
  inferInstanceAs (Preadditive (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory)

noncomputable instance : HasZeroObject (FieldWeilComplex k₀ Λ X) :=
  inferInstanceAs (HasZeroObject (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory)

noncomputable instance : HasShift (FieldWeilComplex k₀ Λ X) ℤ :=
  inferInstanceAs (HasShift (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory ℤ)

instance (n : ℤ) : (shiftFunctor (FieldWeilComplex k₀ Λ X) n).Additive :=
  inferInstanceAs
    ((shiftFunctor (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory n).Additive)

/-- **`D^b_{c,W}(X, Λ)` is a pretriangulated category**, the triangulated structure being that
of the derived category of pro-étale `Λ`-Weil sheaves. -/
noncomputable instance FieldWeilComplex.instPretriangulated
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    Pretriangulated (FieldWeilComplex k₀ Λ X) :=
  inferInstanceAs (Pretriangulated (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory)

/-- **`D^b_{c,W}(X, Λ)` is a triangulated category.** -/
instance FieldWeilComplex.instIsTriangulated
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    IsTriangulated (FieldWeilComplex k₀ Λ X) :=
  inferInstanceAs (IsTriangulated (FieldWeilComplex.objectProperty k₀ Λ X).FullSubcategory)

namespace FieldWeilComplex

/-- The forgetful functor from `D^b_{c,W}(X, Λ)` to the derived category of `Λ`-adic pro-étale
sheaves on `X̄`, forgetting the Weil structure. -/
noncomputable def forget :
    FieldWeilComplex k₀ Λ X ⥤ _root_.DerivedCategory
      (FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  ObjectProperty.ι _ ⋙ (IsoAlgebra.forget _).mapDerivedCategory

/-- The underlying complex of an object of `D^b_{c,W}(X, Λ)` lies in `D^b_c(X̄, Λ)`: the
forgetful functor is exact, so it commutes with the cohomology objects, and it sends Weil
sheaves to their underlying constructible sheaves. -/
lemma boundedFieldConstructible_forget_obj (K : FieldWeilComplex k₀ Λ X) :
    DerivedCategory.boundedFieldConstructible Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (forget.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ K.property.1, fun n ↦
    (fieldConstructibleSheaf Λ _).prop_of_iso
      (((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso n).app K.obj)
      (K.property.2 n)⟩

/-- Blueprint `definition-weil-structure`: the forgetful functor
`For : D^b_{c,W}(X, Λ) ⥤ D^b_c(X̄, Λ)`, the corestriction of
`AlgebraicGeometry.FieldWeilComplex.forget` to the bounded constructible complexes. -/
noncomputable def forgetBoundedConstructible :
    FieldWeilComplex k₀ Λ X ⥤
      (DerivedCategory.boundedFieldConstructible Λ
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory :=
  ObjectProperty.lift _ forget boundedFieldConstructible_forget_obj

variable (X) in
/-- Blueprint `definition-weil-structure`: Weil sheaf and Weil complex, stage `Λ = E`.

The derived Frobenius isomorphism `θ_K : Fr_X^* For(K) ≅ For(K)` of an object `K` of
`D^b_{c,W}(X, Λ)`, natural in `K`: the isomorphism induced on derived categories by the
structure isomorphisms `θ : Fr_X^* F ≅ F` of the terms of `K`, pro-étale `Λ`-Weil sheaves,
through `D(Fr_X^*) ∘ D(forget) ≅ D(Fr_X^* ∘ forget) ≅ D(forget)`. The Frobenius pullback is
exact, so its derived functor is the functor it induces on derived categories. -/
noncomputable def frobeniusIso :
    forget (k₀ := k₀) (Λ := Λ) (X := X) ⋙
        (FieldWeilSheaf.frobeniusPullback k₀ Λ X).mapDerivedCategory ≅
      forget (X := X) :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
    (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget _)
        (FieldWeilSheaf.frobeniusPullback k₀ Λ X) ≪≫
      Functor.mapDerivedCategoryNatIso (IsoAlgebra.forgetCompIso _))

end FieldWeilComplex

section FiniteExtension

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] E] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- For a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the constructible `E`-Weil sheaves form an
abelian category. -/
noncomputable example : Abelian (FieldWeilSheaf k₀ E X) := inferInstance

/-- For a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`, `D^b_{c,W}(X, E)` is a triangulated
category. -/
example : IsTriangulated (FieldWeilComplex k₀ E X) := inferInstance

end FiniteExtension

end AlgebraicGeometry
