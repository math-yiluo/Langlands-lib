/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.PoincareDuality.ProjectionFormulaShiftBoundedConstructible

/-!
# The purity map is a morphism of triangulated functors

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type. Both sides of the purity
map
```
γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K
```
are triangulated functors of `K ∈ Dᵇc(Y)⟦ℚ̄_ℓ⟧`, and `γ_{f,-}` is a natural transformation
compatible with the shifts (`ProEtale.CondensedRing.upperShriekUnitTensorMapNatTrans`). Hence the
objects `K` for which `γ_{f,K}` is an isomorphism form a triangulated subcategory, closed under
direct summands.

The compatibility with the shifts is obtained by writing the adjoint
`Rf_! (Lf^* K ⊗ Rf^! ℚ̄_ℓ) ⟶ K` of `γ_{f,K}` as a composite of natural transformations which
commute with the shifts: the braiding, the inverse of the exceptional projection formula, the
counit of `Rf_! ⊣ Rf^!` at the unit and the left unitor
(`ProEtale.CondensedRing.upperShriekUnitTensorAdjointNatTrans`).

## Main statements

- `ProEtale.CondensedRing.upperShriekUnitTensorMap_naturality`: `γ_{f,K}` is natural in `K`.
- `ProEtale.CondensedRing.commShift_upperShriekUnitTensorMapNatTrans`: `γ_{f,-}` commutes with
  the shifts.
- `ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_triangEnvelope`: if `γ_{f,K}` is an
  isomorphism for `K` in a class `P`, it is one for `K` in the triangulated envelope of `P`.
- `ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_distinguished`,
  `ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_shift_iff`: two out of three and shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The adjoint `Rf_! (Lf^* K ⊗ Rf^! ℚ̄_ℓ) ⟶ K` of the purity map, as a natural transformation in
`K`: the braiding, the inverse of the exceptional projection formula, the counit of
`Rf_! ⊣ Rf^!` at the unit and the left unitor. -/
noncomputable def upperShriekUnitTensorAdjointNatTrans (f : X ⟶ Y) :
    (boundedConstructibleUpperStar _ ℓ f ⋙
        (curriedTensor _).flip.obj ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _))) ⋙
      boundedConstructibleLowerShriek ℓ f ⟶ 𝟭 _ :=
  Functor.whiskerRight (Functor.whiskerLeft (boundedConstructibleUpperStar _ ℓ f)
      (boundedConstructibleBraidingNatTrans₁
        ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _))))
      (boundedConstructibleLowerShriek ℓ f) ≫
    inv (boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ
      (compactificationOverField f) ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _))) ≫
    (curriedTensor _).map ((boundedConstructibleUpperShriekAdjunction ℓ f).counit.app (𝟙_ _)) ≫
    leftUnitorNatTrans _

/-- The components of `upperShriekUnitTensorAdjointNatTrans` are the adjoints of the purity
maps. -/
lemma upperShriekUnitTensorAdjointNatTrans_app (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (upperShriekUnitTensorAdjointNatTrans ℓ f).app K =
      (boundedConstructibleLowerShriek ℓ f).map (β_ _ _).hom ≫
        inv (((boundedConstructibleExceptionalProjection ℓ f).app
          ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _))).app K) ≫
        ((boundedConstructibleUpperShriekAdjunction ℓ f).counit.app (𝟙_ _) ▷ K) ≫
        (λ_ K).hom := by
  simp only [upperShriekUnitTensorAdjointNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, boundedConstructibleBraidingNatTrans₁_app, NatIso.isIso_inv_app,
    curriedTensor_map_app, leftUnitorNatTrans_app]
  rfl

/-- The purity map is the exceptional adjoint of the components of
`upperShriekUnitTensorAdjointNatTrans`. -/
lemma upperShriekUnitTensorMap_eq_homEquiv (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    upperShriekUnitTensorMap ℓ f K =
      (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _
        ((upperShriekUnitTensorAdjointNatTrans ℓ f).app K) := by
  rw [upperShriekUnitTensorAdjointNatTrans_app]
  rfl

/-- The purity map `γ_{f,K}` is natural in `K`. -/
@[reassoc]
lemma upperShriekUnitTensorMap_naturality (f : X ⟶ Y)
    {K K' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : K ⟶ K') :
    (boundedConstructibleUpperStar _ ℓ f).map φ ▷ _ ≫ upperShriekUnitTensorMap ℓ f K' =
      upperShriekUnitTensorMap ℓ f K ≫ (boundedConstructibleUpperShriek ℓ f).map φ := by
  rw [upperShriekUnitTensorMap_eq_homEquiv, upperShriekUnitTensorMap_eq_homEquiv]
  exact ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_naturality_left _ _).symm.trans
    ((congrArg _ ((upperShriekUnitTensorAdjointNatTrans ℓ f).naturality φ)).trans
      ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_naturality_right _ _))

/-- The adjoint of the purity map commutes with the shifts, being a composite of natural
transformations which do. -/
instance commShift_upperShriekUnitTensorAdjointNatTrans (f : X ⟶ Y) :
    NatTrans.CommShift (upperShriekUnitTensorAdjointNatTrans ℓ f) ℤ := by
  have := NatTrans.CommShift.of_isIso
    (boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ
      (compactificationOverField f)
      ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _))) ℤ
  dsimp only [upperShriekUnitTensorAdjointNatTrans]
  infer_instance

/-- The purity map `γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K`, as a natural transformation in
`K`. -/
@[simps]
noncomputable def upperShriekUnitTensorMapNatTrans (f : X ⟶ Y) :
    boundedConstructibleUpperStar _ ℓ f ⋙
        (curriedTensor _).flip.obj ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ⟶
      𝟭 _ ⋙ boundedConstructibleUpperShriek ℓ f where
  app K := upperShriekUnitTensorMap ℓ f K
  naturality _ _ φ := upperShriekUnitTensorMap_naturality ℓ f φ

/-- The purity map commutes with the shifts. -/
instance commShift_upperShriekUnitTensorMapNatTrans (f : X ⟶ Y) :
    NatTrans.CommShift (upperShriekUnitTensorMapNatTrans ℓ f) ℤ :=
  NatTrans.CommShift.of_homEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
    (upperShriekUnitTensorAdjointNatTrans ℓ f) _
    (upperShriekUnitTensorMap_eq_homEquiv ℓ f)

/-- The objects `K` for which the purity map `γ_{f,K}` is an isomorphism form a triangulated
subcategory. -/
instance isTriangulated_isoLocus_upperShriekUnitTensorMapNatTrans (f : X ⟶ Y) :
    (upperShriekUnitTensorMapNatTrans ℓ f).isoLocus.IsTriangulated := by
  have : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).IsTriangulated :=
    inferInstance
  have : (boundedConstructibleUpperShriek ℓ f).IsTriangulated :=
    inferInstance
  have : (boundedConstructibleUpperStar _ ℓ f ⋙
      (curriedTensor _).flip.obj
        ((boundedConstructibleUpperShriek ℓ f).obj
          (𝟙_ _))).IsTriangulated := inferInstance
  have : (𝟭 _ ⋙ boundedConstructibleUpperShriek ℓ
      f).IsTriangulated := inferInstance
  infer_instance

/-- **Dévissage for the purity map**: if `γ_{f,K}` is an isomorphism for the objects `K` of a
class `P`, it is an isomorphism for every `K` in the triangulated subcategory generated by `P`. -/
lemma isIso_upperShriekUnitTensorMap_of_triangEnvelope (f : X ⟶ Y)
    {P : ObjectProperty (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)}
    (h : ∀ K, P K → IsIso (upperShriekUnitTensorMap ℓ f K))
    {K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hK : P.triangEnvelope K) :
    IsIso (upperShriekUnitTensorMap ℓ f K) :=
  (P.triangEnvelope_le_iff (Q := (upperShriekUnitTensorMapNatTrans ℓ f).isoLocus)).2 h K hK

/-- **Two out of three for the purity map**: for a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of `Dᵇc(Y)⟦ℚ̄_ℓ⟧`, if `γ_{f,K₁}` and `γ_{f,K₃}` are isomorphisms, so is
`γ_{f,K₂}`. -/
lemma isIso_upperShriekUnitTensorMap_of_distinguished (f : X ⟶ Y)
    (T : Pretriangulated.Triangle (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    [IsIso (upperShriekUnitTensorMap ℓ f T.obj₁)] [IsIso (upperShriekUnitTensorMap ℓ f T.obj₃)] :
    IsIso (upperShriekUnitTensorMap ℓ f T.obj₂) :=
  ObjectProperty.ext_of_isTriangulatedClosed₂ (upperShriekUnitTensorMapNatTrans ℓ f).isoLocus T hT
    (inferInstanceAs (IsIso (upperShriekUnitTensorMap ℓ f T.obj₁)))
    (inferInstanceAs (IsIso (upperShriekUnitTensorMap ℓ f T.obj₃)))

/-- The purity map `γ_{f,K[n]}` is an isomorphism if and only if `γ_{f,K}` is. -/
lemma isIso_upperShriekUnitTensorMap_shift_iff (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (n : ℤ) :
    IsIso (upperShriekUnitTensorMap ℓ f (K⟦n⟧)) ↔ IsIso (upperShriekUnitTensorMap ℓ f K) :=
  NatTrans.isIso_app_shift_iff (upperShriekUnitTensorMapNatTrans ℓ f) K n

end AlgebraicGeometry.ProEtale.CondensedRing
