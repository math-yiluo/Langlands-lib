/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.CategoryTheory.Shift.ShiftDecompositionIsIso
public import WeilConjectures.TraceFormula.PointDualizable
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The nearby cycles of the trait are monoidal

Let `S = Spec k'⟦t⟧` be the strictly henselian trait of a separably closed field `k'`, with
geometric generic point `η̄ : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`. The nearby cycles
`Ψ_S = Li^* Rη̄_*` of the trait are monoidal on bounded constructible `ℚ̄_ℓ`-complexes on `Spec Ω`:
the Künneth map of the trait as a model of its geometric generic point is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_traitGenericModel`).
This is the computation, in the global-sections step of Gabber's Künneth formula, of the nearby
cycles of `RΓ(X_η̄, A) ⊗ RΓ(Y_η̄, B)`.

## Proof

Every bounded constructible complex on `Spec Ω` is a finite direct sum of shifts `𝟙⟦d⟧` of the
unit (`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), and `𝟙⟦d⟧ = Lη̄^* 𝟙_S⟦d⟧`. For
`W = 𝟙_S⟦d⟧` the lax tensor map `μ : Rη̄_* Lη̄^* W ⊗ Rη̄_* V ⟶ Rη̄_* (Lη̄^* W ⊗ V)`, precomposed
with the unit `W ⟶ Rη̄_* Lη̄^* W`, is the left projection morphism of `η̄`
(`CategoryTheory.Adjunction.whiskerRight_unit_comp_homEquiv`), an isomorphism since `W` is
invertible. After `Li^*` the unit at `W` is invertible: it is at `W = 𝟙_S` (the cohomology of the
geometric generic point of `S` is that of its closed point,
`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_unit_app`) and the unit commutes with
the shifts. A natural transformation between additive functors which is invertible at the
summands of a finite direct sum is invertible at the sum
(`CategoryTheory.ShiftDecomposition.isIso_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemmas -/

namespace CategoryTheory

namespace Adjunction

section

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The lax tensor map `G F B ⊗ G A ⟶ G (F B ⊗ A)` of the right adjoint `G` (the transpose of the
tensor product of the counits), precomposed with the unit `B ⟶ G F B`, is the left projection
morphism `B ⊗ G A ⟶ G (F B ⊗ A)`. -/
lemma whiskerRight_unit_comp_homEquiv (B : D) (A : C) :
    adj.unit.app B ▷ G.obj A ≫ adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ F (G.obj (F.obj B)) (G.obj A) ≫
          (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)) =
      adj.leftProjectionMorphism B A := by
  rw [← homEquiv_naturality_left, leftProjectionMorphism]
  congr 1
  refine (Functor.OplaxMonoidal.δ_natural_left_assoc F (adj.unit.app B) (G.obj A)
    (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)).symm.trans ?_
  congr 1
  rw [← tensorHom_id, tensorHom_comp_tensorHom]
  erw [left_triangle_components]
  rw [Category.id_comp, id_tensorHom]
  rfl

end

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]

/-- A monoidal functor which inverts the unit at a dualizable object also inverts the lax
tensor map of the right adjoint with the image of that object as its first argument. -/
private lemma isIso_map_homEquiv_counit_tensor_of_isDualizable
    {E : Type*} [Category E] [MonoidalCategory E] (H : D ⥤ E) [H.Monoidal]
    {B : D} (hB : IsDualizable B) (A : C) [IsIso (H.map (adj.unit.app B))] :
    IsIso (H.map (adj.homEquiv _ _
      (Functor.OplaxMonoidal.δ F (G.obj (F.obj B)) (G.obj A) ≫
        (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)))) := by
  have := adj.isIso_leftProjectionMorphism_of_isDualizable hB A
  have h₁ : IsIso (H.map (adj.unit.app B ▷ G.obj A)) := by
    rw [Functor.Monoidal.map_whiskerRight]
    infer_instance
  have h := H.map_isIso (adj.leftProjectionMorphism B A)
  rw [← adj.whiskerRight_unit_comp_homEquiv B A, Functor.map_comp] at h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ h

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The unit of the geometric generic point of the trait -/

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

/-- After restriction to the closed point, the derived unit `Λ_S ⟶ Rη̄_* Lη̄^* Λ_S` of the
geometric generic point of the trait is an isomorphism. -/
lemma isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit :
    IsIso (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ (NearbyCyclesModel.traitGenericModel k').j).unit.app
        (𝟙_ _))) := by
  have hU : UpperStarInvertsLowerStarUnit Λ (traitGenericPoint k') (traitClosedPoint k') :=
    ⟨isIso_upperStar_traitClosedPoint_map_unit_app Λ k',
      isZero_upperStar_traitClosedPoint_obj_rightDerived Λ k'⟩
  have h := (NearbyCyclesModel.traitGenericModel k').isIso_unit_of_upperStarInvertsLowerStarUnit Λ
    hU
  have h' := @IsIso.of_isIso_comp_left _ _ _ _ _ (leftDerivedUpperStarUnitIso Λ _).inv _ _ h
  rw [Functor.map_comp] at h'
  exact IsIso.of_isIso_comp_right _ (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
    (R(((NearbyCyclesModel.traitGenericModel k').j)_*⟦Λ⟧).map
      ((leftDerivedUpperStarUnitIso Λ (NearbyCyclesModel.traitGenericModel k').j).hom ≫
        (leftDerivedUpperStarUnitIso Λ (NearbyCyclesModel.traitGenericModel k').ε).inv)))

/-- After restriction to the closed point, the derived unit `W ⟶ Rη̄_* Lη̄^* W` of the geometric
generic point of the trait is an isomorphism at the shifts `W = Λ_S⟦d⟧` of the unit. -/
lemma isIso_upperStar_traitClosedPoint_map_derivedUnit_app_shift (d : ℤ) :
    IsIso (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ (NearbyCyclesModel.traitGenericModel k').j).unit.app
        ((shiftFunctor _ d).obj (𝟙_ _)))) := by
  let τ := Functor.whiskerRight
    (derivedUpperStarLowerStarAdjunction Λ (NearbyCyclesModel.traitGenericModel k').j).unit
    L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧)
  have := isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit Λ k'
  exact (NatTrans.isIso_app_shift_iff τ (𝟙_ _) d).2 this

end Unit

/-! ### The lax tensor map of the geometric generic point -/

section TensorMap

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The shifts `𝟙⟦d⟧` of the unit of the derived category of module objects are dualizable: they
are invertible, with inverse `𝟙⟦-d⟧`. -/
lemma isDualizable_shift_unit_derivedCategory (X : Scheme.{u}) (d : ℤ) :
    IsDualizable ((shiftFunctor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u + 1}) (condensedRingObj Λ X))) d).obj (𝟙_ _)) := by
  let e : ∀ a b : ℤ, a + b = 0 →
      ((shiftFunctor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) a).obj (𝟙_ _) ⊗ (shiftFunctor _ b).obj (𝟙_ _) ≅ 𝟙_ _) :=
    fun a b h ↦ DerivedCategory.shiftTensorShiftIso _ (𝟙_ _) (𝟙_ _) a b ≪≫
      (shiftFunctor _ _).mapIso (λ_ _) ≪≫ eqToIso (by rw [h]) ≪≫ (shiftFunctorZero _ ℤ).app _
  exact isDualizable_of_tensorIso (e d (-d) (add_neg_cancel d)) (e (-d) d (neg_add_cancel d))

variable (k' : Type u) [Field k'] [IsSepClosed k']

/-- After restriction to the closed point of the trait, the lax tensor map
`Rη̄_* U ⊗ Rη̄_* V ⟶ Rη̄_* (U ⊗ V)` of the geometric generic point is an isomorphism for
`U = Lη̄^* (𝟙⟦d⟧)`: precomposed with the unit, it is the left projection morphism of the
invertible object `𝟙⟦d⟧`. -/
lemma isIso_upperStar_map_lowerStarTensorMap'_upperStar_shift (d : ℤ)
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (NearbyCyclesModel.traitGenericModel k').generic) Ab.{u + 1})
        (condensedRingObj Λ (NearbyCyclesModel.traitGenericModel k').generic))) :
    IsIso (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
      (lowerStarTensorMap' Λ (NearbyCyclesModel.traitGenericModel k').j
        (L(((NearbyCyclesModel.traitGenericModel k').j)^*⟦Λ⟧).obj
          ((shiftFunctor _ d).obj (𝟙_ _))) V)) := by
  have := isIso_upperStar_traitClosedPoint_map_derivedUnit_app_shift Λ k' d
  exact (derivedUpperStarLowerStarAdjunction Λ
    (NearbyCyclesModel.traitGenericModel k').j).isIso_map_homEquiv_counit_tensor_of_isDualizable
      L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧)
      (isDualizable_shift_unit_derivedCategory Λ (NearbyCyclesModel.traitGenericModel k').total d)
      V

/-- The lax tensor map `Rη̄_* U ⊗ Rη̄_* V ⟶ Rη̄_* (U ⊗ V)`, restricted to the closed point of the
trait, as a natural transformation in `U`. -/
@[simps]
noncomputable def upperStarLowerStarTensorMapNatTrans
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (NearbyCyclesModel.traitGenericModel k').generic) Ab.{u + 1})
        (condensedRingObj Λ (NearbyCyclesModel.traitGenericModel k').generic))) :
    R(((NearbyCyclesModel.traitGenericModel k').j)_*⟦Λ⟧) ⋙
        tensorRight (R(((NearbyCyclesModel.traitGenericModel k').j)_*⟦Λ⟧).obj V) ⋙
          L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧) ⟶
      tensorRight V ⋙ R(((NearbyCyclesModel.traitGenericModel k').j)_*⟦Λ⟧) ⋙
        L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧) where
  app U := L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
    (lowerStarTensorMap' Λ (NearbyCyclesModel.traitGenericModel k').j U V)
  naturality U U' x := by
    have h := lowerStarTensorMap'_natural Λ (NearbyCyclesModel.traitGenericModel k').j x (𝟙 V)
    rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
    simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg _ h

-- the derived functors of the trait unfold to large terms
/-- After restriction to the closed point of the trait, the lax tensor map
`Rη̄_* U ⊗ Rη̄_* V ⟶ Rη̄_* (U ⊗ V)` of the geometric generic point is an isomorphism when `U` is a
finite direct sum of shifts of the unit. -/
lemma isIso_upperStar_map_lowerStarTensorMap'_of_shiftDecomposition
    {U V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (NearbyCyclesModel.traitGenericModel k').generic) Ab.{u + 1})
        (condensedRingObj Λ (NearbyCyclesModel.traitGenericModel k').generic))}
    (hU : ShiftDecomposition (𝟙_ _) U) :
    IsIso (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
      (lowerStarTensorMap' Λ (NearbyCyclesModel.traitGenericModel k').j U V)) := by
  have : L(((NearbyCyclesModel.traitGenericModel k').j)^*⟦Λ⟧).Additive :=
    Functor.additive_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (NearbyCyclesModel.traitGenericModel k').j).symm
  have : L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).Additive :=
    Functor.additive_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (NearbyCyclesModel.traitGenericModel k').i).symm
  have : R(((NearbyCyclesModel.traitGenericModel k').j)_*⟦Λ⟧).Additive :=
    (derivedUpperStarLowerStarAdjunction Λ
      (NearbyCyclesModel.traitGenericModel k').j).right_adjoint_additive
  rw [← upperStarLowerStarTensorMapNatTrans_app]
  refine ShiftDecomposition.isIso_app (upperStarLowerStarTensorMapNatTrans Λ k' V) hU fun j ↦ ?_
  have := isIso_upperStar_map_lowerStarTensorMap'_upperStar_shift Λ k' (hU.deg j) V
  exact @NatTrans.isIso_app_of_iso' _ _ _ _ _ _ (upperStarLowerStarTensorMapNatTrans Λ k' V) _ _
    ((shiftFunctor _ (hU.deg j)).mapIso
      (leftDerivedUpperStarUnitIso Λ (NearbyCyclesModel.traitGenericModel k').j).symm ≪≫
      ((L(((NearbyCyclesModel.traitGenericModel k').j)^*⟦Λ⟧).commShiftIso
        (hU.deg j)).app (𝟙_ _)).symm)
    this

end TensorMap

/-- Over a separably closed field, every bounded constructible `ℚ̄_ℓ`-complex on the point is a
finite direct sum of shifts of the unit
(`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), in the ambient derived category. -/
lemma nonempty_shiftDecomposition_of_boundedConstructible (ℓ : ℕ) [Fact ℓ.Prime] {K : Type u}
    [Field K] [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of K))) C) :
    Nonempty (ShiftDecomposition (𝟙_ _) C) :=
  ⟨(nonempty_shiftDecomposition_point ℓ K ⟨C, hC⟩).some.map (boundedConstructible _).ι⟩

/-! ### The Künneth map of the trait -/

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

/-- The pullback exchange of the identity morphism of the trait (as a model of its geometric
generic point) is invertible: its base change morphism is the mate of an isomorphism along
`L(𝟙)^* ≅ 𝟭`. -/
instance isIso_pullbackExchange_id_traitGenericModel :
    IsIso ((Hom.id (traitGenericModel k')).pullbackExchange Λ) := by
  have : L(((Hom.id (traitGenericModel k')).total)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have : L(((Hom.id (traitGenericModel k')).generic)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have := isIso_mateEquiv_of_isEquivalence (derivedUpperStarLowerStarAdjunction Λ
    (traitGenericModel k').j) (derivedUpperStarLowerStarAdjunction Λ (traitGenericModel k').j)
    (pullbackSquareComparison Λ (Hom.id (traitGenericModel k')).commSq_j).hom
  unfold Hom.pullbackExchange
  infer_instance

-- the Künneth map of the trait unfolds to large terms
/-- **The nearby cycles of the trait are monoidal on the geometric generic point**: the Künneth
map of the trait `T` (as a model of its geometric generic point) is an isomorphism at `(C, D)`
if `C` is a finite direct sum of shifts of the unit. -/
theorem isIso_kunnethMap_traitGenericModel_of_shiftDecomposition
    (C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (traitGenericModel k').generic)
      Ab.{u + 1}) (condensedRingObj Λ (traitGenericModel k').generic)))
    (hC : Nonempty (ShiftDecomposition (𝟙_ _) C)) :
    IsIso (kunnethMap Λ (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k')) C D) := by
  have hC' : ShiftDecomposition (𝟙_ _) (L(((traitGenericModel k').ε)^*⟦Λ⟧).obj
      (L((𝟙 (Spec (.of (traitGenericField k'))))^*⟦Λ⟧).obj C)) :=
    ((hC.some.ofIso ((leftDerivedUpperStarId Λ _).app C).symm).ofIso
      ((leftDerivedUpperStarId Λ _).app _).symm)
  have hμ := isIso_upperStar_map_lowerStarTensorMap'_of_shiftDecomposition Λ k'
    (V := L(((traitGenericModel k').ε)^*⟦Λ⟧).obj
      (L((𝟙 (Spec (.of (traitGenericField k'))))^*⟦Λ⟧).obj D)) hC'
  have ha : IsIso (((Hom.id (traitGenericModel k')).pullbackExchange Λ).app C ⊗ₘ
      ((Hom.id (traitGenericModel k')).pullbackExchange Λ).app D) := inferInstance
  unfold kunnethMap tensorMap
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' ha (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' hμ inferInstance))

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
