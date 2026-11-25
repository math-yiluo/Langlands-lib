/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeDualizable
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.TraceFormula.Specialization.NearbyDuality
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal

/-!

# Nearby cycles commute with twists by dualizable objects

Let `M` be a model with nearby cycles `Ψ = Li^* Rj_* Lε^*`, let `W` be a dualizable object of the
derived category of the total space and `T` a complex on `X` with an isomorphism
`e : Lε^* T ≅ Lj^* W`. The *specialization map* `σ_e : Li^* W ⟶ Ψ T` is `Li^*` of the unit
`W ⟶ Rj_* Lj^* W` followed by `e⁻¹`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.twistSpecializationMap`). Then the
lax tensor map of nearby cycles, precomposed with `Ψ A ◁ σ_e`,
```
Ψ A ⊗ Li^* W ⟶ Ψ A ⊗ Ψ T ⟶ Ψ (A ⊗ T),
```
is an isomorphism
(`NearbyCyclesModel.isIso_whiskerLeft_twistSpecializationMap_comp_tensorMap`):
it is `Li^*` of the projection morphism `Rj_* Lε^* A ⊗ W ⟶ Rj_* (Lε^* A ⊗ Lj^* W)` of `j`,
invertible for dualizable `W`, up to the monoidal structures of `Li^*` and `Lε^*`.

The Tate twists `ℚ̄_ℓ(d)` of a scheme over a field in which `ℓ` is invertible are dualizable in
the derived category (`AlgebraicGeometry.ProEtale.CondensedRing.isDualizable_tateTwistDerived`,
and `isDualizable_tateTwistDerived_of_trait` over the trait). Given isomorphisms
`Lε^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ(d)`, `Lj^* ℚ̄_ℓ,𝒳(d) ≅ ℚ̄_ℓ(d)` and `Li^* ℚ̄_ℓ,𝒳(d) ≅ ℚ̄_ℓ,X'(d)` (the
compatibility of the Tate twists with pullbacks, taken as hypotheses), this gives, on bounded
constructible complexes, `Ψ (A ⊗ ℚ̄_ℓ(d)[n]) ≅ Ψ A ⊗ ℚ̄_ℓ(d)[n]`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesTateTwistIso`), inverse
to the lax tensor map precomposed with the specialization map of the Tate twist.

-/

@[expose] public section

universe u

set_option linter.unusedSectionVars false

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemma -/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The lax tensor map `G A ⊗ G F B ⟶ G (A ⊗ F B)` of the right adjoint `G` (the transpose of the
tensor product of the counits), precomposed with the unit `B ⟶ G F B`, is the projection
morphism `G A ⊗ B ⟶ G (A ⊗ F B)`. -/
lemma whiskerLeft_unit_comp_homEquiv (A : C) (B : D) :
    G.obj A ◁ adj.unit.app B ≫ adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ F (G.obj A) (G.obj (F.obj B)) ≫
          (adj.counit.app A ⊗ₘ adj.counit.app (F.obj B))) =
      adj.projectionMorphism A B := by
  rw [← homEquiv_naturality_left, projectionMorphism]
  congr 1
  refine (Functor.OplaxMonoidal.δ_natural_right_assoc F (G.obj A) (adj.unit.app B)
    (adj.counit.app A ⊗ₘ adj.counit.app (F.obj B))).symm.trans ?_
  congr 1
  rw [← id_tensorHom, tensorHom_comp_tensorHom]
  erw [left_triangle_components]
  rw [Category.id_comp, tensorHom_id]
  rfl

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

/-- A strong monoidal functor carries the projection formula, followed by a change of
the second factor along an isomorphism, to an isomorphism. -/
private lemma isIso_map_whiskerLeft_unit_comp_tensor
    {B C D S : Type*} [Category B] [Category C] [Category D] [Category S]
    [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory S]
    [BraidedCategory D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]
    (E : B ⥤ C) (I : D ⥤ S) [E.Monoidal] [I.Monoidal]
    {W : D} (hW : IsDualizable W) {T : B} (e : E.obj T ≅ F.obj W) (A : B) :
    IsIso (I.obj (G.obj (E.obj A)) ◁ I.map (adj.unit.app W ≫ G.map e.inv) ≫
      (Functor.LaxMonoidal.μ I _ _ ≫ I.map
        (adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F _ _ ≫
          (adj.counit.app (E.obj A) ⊗ₘ adj.counit.app (E.obj T))) ≫
            G.map (Functor.LaxMonoidal.μ E A T)))) := by
  let := adj.rightAdjointLaxMonoidal
  have hp := adj.isIso_projectionMorphism_of_isDualizable hW (E.obj A)
  have hunit : G.obj (E.obj A) ◁ adj.unit.app W ≫
      Functor.LaxMonoidal.μ G (E.obj A) (F.obj W) =
        adj.projectionMorphism (E.obj A) W :=
    adj.whiskerLeft_unit_comp_homEquiv (E.obj A) W
  have key : G.obj (E.obj A) ◁ (adj.unit.app W ≫ G.map e.inv) ≫
      Functor.LaxMonoidal.μ G (E.obj A) (E.obj T) =
        adj.projectionMorphism (E.obj A) W ≫ G.map (E.obj A ◁ e.inv) := by
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right, ← Category.assoc, hunit]
  change IsIso (I.obj (G.obj (E.obj A)) ◁ I.map (adj.unit.app W ≫ G.map e.inv) ≫
    (Functor.LaxMonoidal.μ I _ _ ≫ I.map
      (Functor.LaxMonoidal.μ G (E.obj A) (E.obj T) ≫
        G.map (Functor.LaxMonoidal.μ E A T))))
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← I.map_comp,
    ← Category.assoc, key, Category.assoc]
  infer_instance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Nearby cycles of a twist by a dualizable object -/

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] in
/-- The lax tensor map of the derived pushforward is natural in its second variable. -/
@[reassoc]
lemma lowerStarTensorMap'_natural_right {U T : Scheme.{u}} (j : U ⟶ T)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))} (y : B ⟶ B') :
    R((j)_*⟦Λ⟧).obj A ◁ R((j)_*⟦Λ⟧).map y ≫ lowerStarTensorMap' Λ j A B' =
      lowerStarTensorMap' Λ j A B ≫ R((j)_*⟦Λ⟧).map (A ◁ y) := by
  let := (derivedUpperStarLowerStarAdjunction Λ j).rightAdjointLaxMonoidal
  have := Functor.LaxMonoidal.μ_natural_right R((j)_*⟦Λ⟧) A y
  simp only [Adjunction.rightAdjointLaxMonoidal_μ] at this
  exact this

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- The *specialization map* `σ_e : Li^* W ⟶ Ψ T` of an isomorphism `e : Lε^* T ≅ Lj^* W`:
`Li^*` of the unit `W ⟶ Rj_* Lj^* W` followed by `Rj_* e⁻¹`. -/
noncomputable def twistSpecializationMap
    {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj Λ M.total))}
    {T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (e : L((M.ε)^*⟦Λ⟧).obj T ≅ L((M.j)^*⟦Λ⟧).obj W) :
    L((M.i)^*⟦Λ⟧).obj W ⟶ (M.nearbyCycles Λ).obj T :=
  L((M.i)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ M.j).unit.app W ≫
    R((M.j)_*⟦Λ⟧).map e.inv)

attribute [local instance] DerivedCategory.braidedCategory' in
/-- **Nearby cycles commute with twists by dualizable objects**: for a dualizable `W` on the total
space and `e : Lε^* T ≅ Lj^* W`, the lax tensor map `Ψ A ⊗ Ψ T ⟶ Ψ (A ⊗ T)`, precomposed with
`Ψ A ◁ σ_e`, is an isomorphism `Ψ A ⊗ Li^* W ≅ Ψ (A ⊗ T)`. It is `Li^*` of the projection
morphism of `Lj^* ⊣ Rj_*` at `(Lε^* A, W)`, up to the monoidal structures of `Li^*` and `Lε^*`. -/
theorem isIso_whiskerLeft_twistSpecializationMap_comp_tensorMap
    {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj Λ M.total))} (hW : IsDualizable W)
    {T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (e : L((M.ε)^*⟦Λ⟧).obj T ≅ L((M.j)^*⟦Λ⟧).obj W)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso ((M.nearbyCycles Λ).obj A ◁ M.twistSpecializationMap Λ e ≫ M.tensorMap Λ A T) := by
  exact (derivedUpperStarLowerStarAdjunction Λ M.j).isIso_map_whiskerLeft_unit_comp_tensor
    L((M.ε)^*⟦Λ⟧) L((M.i)^*⟦Λ⟧) hW e A


/-- **Nearby cycles of a twist by a dualizable object**: `Ψ (A ⊗ T) ≅ Ψ A ⊗ Li^* W` for a
dualizable `W` on the total space and `e : Lε^* T ≅ Lj^* W`. Its inverse is the lax tensor map
`μ_{A,T}` precomposed with `Ψ A ◁ σ_e`
(`NearbyCyclesModel.isIso_whiskerLeft_twistSpecializationMap_comp_tensorMap`). -/
noncomputable def nearbyCyclesTwistIso
    {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj Λ M.total))} (hW : IsDualizable W)
    {T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (e : L((M.ε)^*⟦Λ⟧).obj T ≅ L((M.j)^*⟦Λ⟧).obj W)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (M.nearbyCycles Λ).obj (A ⊗ T) ≅ (M.nearbyCycles Λ).obj A ⊗ L((M.i)^*⟦Λ⟧).obj W :=
  have := M.isIso_whiskerLeft_twistSpecializationMap_comp_tensorMap Λ hW e A
  (asIso ((M.nearbyCycles Λ).obj A ◁ M.twistSpecializationMap Λ e ≫ M.tensorMap Λ A T)).symm

end NearbyCyclesModel

/-! ### The Tate twists are dualizable in the derived category -/

/-- The shifts of a dualizable object of the derived category of module objects are dualizable:
`L⟦n⟧ ≅ L ⊗ 𝟙⟦n⟧`, a tensor product of dualizable objects. -/
lemma isDualizable_shift_derivedCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z : Scheme.{u}}
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))} (hL : IsDualizable L) (n : ℤ) :
    IsDualizable ((shiftFunctor _ n).obj L) := by
  refine IsDualizable.of_iso (DerivedCategory.shiftTensorShiftIso _ L (𝟙_ _) 0 n ≪≫
    (shiftFunctor _ (0 + n)).mapIso (ρ_ L) ≪≫ eqToIso (by rw [zero_add])) ?_
  exact (IsDualizable.of_iso ((shiftFunctorZero _ ℤ).app L).symm hL).tensorObj
    (isDualizable_shift_unit_derivedCategory Λ Z n)

/-- **The Tate twists are dualizable** in the derived category: for a scheme `Z` over a field in
which `ℓ` is invertible, `ℚ̄_ℓ,Z(d)` is locally free (`ProEtale.isLocallyFree_tateTwist`), hence
dualizable in `Mod_{ℚ̄_ℓ,Z}`, and so is the complex `ℚ̄_ℓ,Z(d)[0]`. -/
lemma isDualizable_tateTwistDerived (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [NeZero (ℓ : k)] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (d : ℤ) :
    IsDualizable (tateTwistDerived Z ℓ d) := by
  let := DerivedCategory.braidedCategory'
    (C := Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z))
  refine DerivedCategory.isDualizable_Q_obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (tateTwist Z ℓ d)) 0 0 fun n ↦ ?_
  by_cases hn : n = 0
  · subst hn
    exact IsDualizable.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm
      (isLocallyFree_tateTwist ℓ f d).isDualizable
  · exact IsZero.isDualizable (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-! ### Bounded constructible complexes -/

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory`, as in
-- `NearbyCyclesModel.boundedConstructibleTensorMap`.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- **Nearby cycles of bounded constructible complexes commute with twists by dualizable
objects**: for a dualizable `W` on the total space, `e : Lε^* T ≅ Lj^* W` and an identification
`e' : W' ≅ Li^* W`, the lax tensor map `μ_{A,T} : Ψ A ⊗ Ψ T ⟶ Ψ (A ⊗ T)`, precomposed with
`Ψ A ◁ (σ_e ∘ e')`, is an isomorphism `Ψ A ⊗ W' ≅ Ψ (A ⊗ T)`. -/
theorem isIso_whiskerLeft_twistSpecializationMap_comp_boundedConstructibleTensorMap
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))} (hW : IsDualizable W)
    {T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {W' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj T.obj ≅
      L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj W)
    (e' : W'.obj ≅ L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj W)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleNearbyCycles hP).obj A ◁
        (ObjectProperty.homMk (e'.hom ≫ M.twistSpecializationMap _ e) :
          W' ⟶ (boundedConstructibleNearbyCycles hP).obj T) ≫
      boundedConstructibleTensorMap hP A T) := by
  have := M.isIso_whiskerLeft_twistSpecializationMap_comp_tensorMap _ hW e A.obj
  have h : IsIso ((M.nearbyCycles _).obj A.obj ◁ (e'.hom ≫ M.twistSpecializationMap _ e) ≫
      M.tensorMap _ A.obj T.obj) := by
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    infer_instance
  rw [← isIso_iff_of_reflects_iso _ (boundedConstructible _).ι]
  exact h

/-- The specialization map `σ : ℚ̄_ℓ,X'(d)[n] ⟶ Ψ (ℚ̄_ℓ,X(d)[n])` of the Tate twists, given the
compatibility of the Tate twists with the pullbacks along `ε`, `j` and `i`: the specialization
map `σ_e` (`NearbyCyclesModel.twistSpecializationMap`) of `W = ℚ̄_ℓ,𝒳(d)[n]` on the total
space. -/
noncomputable def tateTwistSpecializationMap
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) {d : ℤ}
    (eε : L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived X.left ℓ d) ≅
      tateTwistDerived M.generic ℓ d)
    (ej : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived M.total ℓ d) ≅
      tateTwistDerived M.generic ℓ d)
    (ei : L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived M.total ℓ d) ≅
      tateTwistDerived X'.left ℓ d) (n : ℤ) :
    boundedConstructibleTateTwist ℓ X' d n ⟶
      (boundedConstructibleNearbyCycles hP).obj (boundedConstructibleTateTwist ℓ X d n) :=
  ObjectProperty.homMk (((shiftFunctor _ n).mapIso ei.symm ≪≫
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm).hom ≫
      M.twistSpecializationMap _
        (((L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _) ≪≫
          (shiftFunctor _ n).mapIso (eε ≪≫ ej.symm) ≪≫
          ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm))

/-- **Nearby cycles commute with Tate twists**: if `ℚ̄_ℓ,𝒳(d)` is dualizable on the total space
(`ProEtale.CondensedRing.isDualizable_tateTwistDerived`) and compatible with the pullbacks along
`ε`, `j` and `i`, the lax tensor map `μ : Ψ A ⊗ Ψ (ℚ̄_ℓ,X(d)[n]) ⟶ Ψ (A ⊗ ℚ̄_ℓ,X(d)[n])`,
precomposed with `Ψ A ◁ σ` for the specialization map
`σ : ℚ̄_ℓ,X'(d)[n] ⟶ Ψ (ℚ̄_ℓ,X(d)[n])` (`NearbyCyclesModel.tateTwistSpecializationMap`), is an
isomorphism. -/
theorem isIso_whiskerLeft_tateTwistSpecializationMap_comp_boundedConstructibleTensorMap
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) {d : ℤ}
    (hW : IsDualizable (tateTwistDerived M.total ℓ d))
    (eε : L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived X.left ℓ d) ≅
      tateTwistDerived M.generic ℓ d)
    (ej : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived M.total ℓ d) ≅
      tateTwistDerived M.generic ℓ d)
    (ei : L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived M.total ℓ d) ≅
      tateTwistDerived X'.left ℓ d) (n : ℤ) (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleNearbyCycles hP).obj A ◁
        M.tateTwistSpecializationMap hP eε ej ei n ≫
      boundedConstructibleTensorMap hP A (boundedConstructibleTateTwist ℓ X d n)) :=
  isIso_whiskerLeft_twistSpecializationMap_comp_boundedConstructibleTensorMap hP
    (isDualizable_shift_derivedCategory _ hW n) _ _ A

/-- **Nearby cycles commute with Tate twists**: `Ψ (A ⊗ ℚ̄_ℓ,X(d)[n]) ≅ Ψ A ⊗ ℚ̄_ℓ,X'(d)[n]`, the
inverse of the lax tensor map precomposed with `Ψ A ◁ σ`
(`isIso_whiskerLeft_tateTwistSpecializationMap_comp_boundedConstructibleTensorMap`).
-/
noncomputable def nearbyCyclesTateTwistIso
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) {d : ℤ}
    (hW : IsDualizable (tateTwistDerived M.total ℓ d))
    (eε : L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived X.left ℓ d) ≅
      tateTwistDerived M.generic ℓ d)
    (ej : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived M.total ℓ d) ≅
      tateTwistDerived M.generic ℓ d)
    (ei : L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived M.total ℓ d) ≅
      tateTwistDerived X'.left ℓ d) (n : ℤ) (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles hP).obj (A ⊗ boundedConstructibleTateTwist ℓ X d n) ≅
      (boundedConstructibleNearbyCycles hP).obj A ⊗ boundedConstructibleTateTwist ℓ X' d n :=
  have := M.isIso_whiskerLeft_tateTwistSpecializationMap_comp_boundedConstructibleTensorMap hP
    hW eε ej ei n A
  (asIso ((boundedConstructibleNearbyCycles hP).obj A ◁
    M.tateTwistSpecializationMap hP eε ej ei n ≫
      boundedConstructibleTensorMap hP A (boundedConstructibleTateTwist ℓ X d n))).symm

end NearbyCyclesModel

/-- The Tate twists of a scheme over the trait `Spec k'⟦t⟧`, with `ℓ ≠ char k'`, are dualizable
(`ProEtale.CondensedRing.isDualizable_tateTwistDerived` along `Spec k'⟦t⟧ ⟶ Spec k'`); for
instance on the total space of a trait model. -/
lemma isDualizable_tateTwistDerived_of_trait (ℓ : ℕ) [Fact ℓ.Prime] {k' : Type u} [Field k']
    [Fact (ringChar k' ≠ ℓ)] {Z : Scheme.{u}} (q : Z ⟶ trait k') (d : ℤ) :
    IsDualizable (tateTwistDerived Z ℓ d) :=
  have : NeZero (ℓ : k') := ⟨fun h ↦ (Fact.out : ringChar k' ≠ ℓ)
    (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k' ℓ).1 h)).resolve_left
      (CharP.ringChar_ne_one))⟩
  isDualizable_tateTwistDerived ℓ (q ≫ traitToBase k' k') d

end AlgebraicGeometry.ProEtale.CondensedRing
