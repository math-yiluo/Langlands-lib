/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionExchange
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTensor
public import WeilConjectures.TateTwist.UpperStar
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesBraided
public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingAutInvariant

/-!

# Nearby cycles and the twist by `ℚ̄_ℓ(0)[n]`

Let `M` be a model with nearby cycles `Ψ = Li^* Rj_* Lε^*` on bounded constructible complexes,
`X` over a field `k` and `X'` over a field `k'`, and let `T = ℚ̄_ℓ,X(0)[n]`,
`T' = ℚ̄_ℓ,X'(0)[n]` (`ProEtale.CondensedRing.boundedConstructibleTateTwist`). This file provides
the inputs on the twist `T` of the slice step of nearby duality (blueprint
`lemma-nearby-duality-slice--1`, the twist (1), "`P` acts trivially on `A(1)[2]`"), in the degree
`d = 0`, where the comparisons of the Tate twists with the pullbacks are canonical
(`ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedZeroIso`):

* the isomorphism `κ_A : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'`
  (`NearbyCyclesModel.zeroTwistIso`, the instance of
  `NearbyCyclesModel.nearbyCyclesTateTwistIso` for `d = 0`), inverse to
  `μ_{A,T} ∘ (Ψ A ◁ σ)` for the specialization map `σ : T' ⟶ Ψ T`;
* its naturality (`NearbyCyclesModel.zeroTwistIso_hom_naturality`) and its compatibility with the
  lax tensor map `μ` of nearby cycles (`NearbyCyclesModel.zeroTwistIso_tensor`), in the form of
  the hypotheses of `CategoryTheory.Verdier.isIso_nearbyDualityMap_of_iso_twist_iff`;
* its invariance under the action of the self-maps of the model
  (`NearbyCyclesModel.boundedConstructibleAutAction_app_comp_zeroTwistIso_hom`): the action
  `ρ(s)` fixes the specialization map, `σ ∘ ρ(s)_T = σ`
  (`NearbyCyclesModel.zeroTwistSpecializationMap_comp_boundedConstructibleAutAction_app`);
* `T` is invertible (`ProEtale.CondensedRing.isInvertible_boundedConstructibleTateTwist_zero`).

The invariance of `σ` is reduced to that of the specialization unit
(`NearbyCyclesModel.Hom.unit_comp_autAction`): in degree `0` the canonical comparisons of the
Tate twists are the unit comparisons of the monoidal pullbacks
(`ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedZeroIso_eq`), the action of a self-map
commutes with the shifts (`NearbyCyclesModel.Hom.autAction_shift_comp`, from
`NearbyCyclesModel.Hom.commShift_pullbackExchange`), and so does the specialization map
(`NearbyCyclesModel.twistSpecializationMap_shift_comp`).

-/

@[expose] public section

universe u

set_option linter.unusedSectionVars false

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemmas -/

namespace CategoryTheory

/-- An endomorphism `ι'⁻¹ ≫ α ≫ Ψ ι` of `Ψ`, obtained from an exchange `α : Ψ ⋙ I' ⟶ I ⋙ Ψ`
commuting with the shifts and identifications `ι : I ≅ 𝟭`, `ι' : I' ≅ 𝟭` commuting with the
shifts, commutes with the shifts. -/
lemma comp_commShiftIso_hom_app_of_exchange {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] {Ψ : C ⥤ D} {I : C ⥤ C} {I' : D ⥤ D} [Ψ.CommShift ℤ]
    [I.CommShift ℤ] [I'.CommShift ℤ] (ι : I ≅ 𝟭 C) (ι' : I' ≅ 𝟭 D)
    [NatTrans.CommShift ι.hom ℤ] [NatTrans.CommShift ι'.hom ℤ] (α : Ψ ⋙ I' ⟶ I ⋙ Ψ)
    [NatTrans.CommShift α ℤ] (n : ℤ) (K : C) :
    (ι'.inv.app (Ψ.obj (K⟦n⟧)) ≫ α.app (K⟦n⟧) ≫ Ψ.map (ι.hom.app (K⟦n⟧))) ≫
        (Ψ.commShiftIso n).hom.app K =
      (Ψ.commShiftIso n).hom.app K ≫
        (ι'.inv.app (Ψ.obj K) ≫ α.app K ≫ Ψ.map (ι.hom.app K))⟦n⟧' := by
  have hι := NatTrans.app_shift ι.hom n K
  have hι' := NatTrans.shift_app_comm ι'.inv n (Ψ.obj K)
  have hα := NatTrans.shift_app_comm α n K
  have hn := ι'.inv.naturality ((Ψ.commShiftIso n).hom.app K)
  simp only [Functor.commShiftIso_id_inv_app, Functor.commShiftIso_id_hom_app,
    Category.comp_id, Functor.commShiftIso_comp_hom_app, Functor.id_map, Functor.id_obj,
    Category.assoc] at hι hι' hα hn
  erw [Category.id_comp] at hι'
  rw [hι, Functor.map_comp]
  simp only [Category.assoc]
  rw [Functor.commShiftIso_hom_naturality, ← reassoc_of% hα, ← reassoc_of% hn,
    ← reassoc_of% hι']
  simp only [Functor.map_comp]

/-- A morphism `I (W ⟶ R J W ≅ R E T)`, built from the unit of an adjunction `J ⊣ R` commuting
with the shifts and an isomorphism `e : E T ≅ J W`, commutes with the shifts: its version for the
shifted objects, transported along the commutation isomorphisms of `I`, `E ⋙ R ⋙ I`, `E` and
`J`, is its shift. -/
lemma shift_map_unit_comp_eq {DX DG DT DX' : Type*} [Category DX] [Category DG] [Category DT]
    [Category DX'] [HasShift DX ℤ] [HasShift DG ℤ] [HasShift DT ℤ] [HasShift DX' ℤ]
    {E : DX ⥤ DG} {J : DT ⥤ DG} {R : DG ⥤ DT} {I : DT ⥤ DX'} [E.CommShift ℤ] [J.CommShift ℤ]
    [R.CommShift ℤ] [I.CommShift ℤ] (adj : J ⊣ R) [adj.CommShift ℤ] {T : DX} {W : DT}
    (e : E.obj T ≅ J.obj W) (n : ℤ) :
    (I.commShiftIso n).inv.app W ≫ I.map (adj.unit.app (W⟦n⟧) ≫
        R.map (((E.commShiftIso n).app T ≪≫ (shiftFunctor _ n).mapIso e ≪≫
          ((J.commShiftIso n).app W).symm).inv)) ≫ ((E ⋙ R ⋙ I).commShiftIso n).hom.app T =
      (I.map (adj.unit.app W ≫ R.map e.inv))⟦n⟧' := by
  have hu := adj.unit_app_commShiftIso_hom_app ℤ n W
  have hR := R.commShiftIso_hom_naturality e.inv n
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map] at hu ⊢
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc]
  have hX : adj.unit.app (W⟦n⟧) ≫ R.map ((J.commShiftIso n).hom.app W ≫ (e.inv)⟦n⟧' ≫
      (E.commShiftIso n).inv.app T) ≫ R.map ((E.commShiftIso n).hom.app T) ≫
        (R.commShiftIso n).hom.app (E.obj T) = (adj.unit.app W ≫ R.map e.inv)⟦n⟧' := by
    rw [← R.map_comp_assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [R.map_comp_assoc, hR, reassoc_of% hu, Functor.map_comp]
  rw [← I.map_comp_assoc, ← I.map_comp_assoc]
  simp only [Category.assoc]
  rw [hX, Functor.commShiftIso_hom_naturality]
  exact Iso.inv_hom_id_app_assoc _ _ _


/-- The diagram chase behind
`NearbyCyclesModel.zeroTwistSpecializationMap_comp_boundedConstructibleAutAction_app`: if
`q ≫ τ ≫ c = τ₀⟦n⟧`, `ρ ≫ c = c ≫ ρ₀⟦n⟧` and `τ₀ ≫ ρ₀ = τ₀`, then `a ≫ q ≫ τ` is fixed by
`ρ`. -/
lemma comp_eq_of_shift_comp {D : Type*} [Category D] [HasShift D ℤ] (n : ℤ)
    {Y Z P Q Y₀ : D} (a : Y ⟶ Y₀⟦n⟧) (q : Y₀⟦n⟧ ⟶ Z) (τ : Z ⟶ P) (c : P ⟶ Q⟦n⟧) [Mono c]
    (τ₀ : Y₀ ⟶ Q) (ρ : P ⟶ P) (ρ₀ : Q ⟶ Q) (hb : q ≫ τ ≫ c = τ₀⟦n⟧')
    (ha : ρ ≫ c = c ≫ ρ₀⟦n⟧') (hc : τ₀ ≫ ρ₀ = τ₀) :
    a ≫ q ≫ τ ≫ ρ = a ≫ q ≫ τ := by
  rw [← cancel_mono c]
  simp only [Category.assoc]
  rw [ha, reassoc_of% hb, ← Functor.map_comp, hc, hb]

section Twist

variable {C C' : Type*} [Category C] [MonoidalCategory C] [Category C'] [MonoidalCategory C']
  {Ψ : C ⥤ C'} (μ : ∀ A B : C, Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B)) {T : C} {T' : C'}
  (σ : T' ⟶ Ψ.obj T) (κ : ∀ A : C, Ψ.obj (A ⊗ T) ≅ Ψ.obj A ⊗ T')

/-- The twist isomorphism `κ_A : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'` with inverse `μ_{A,T} ∘ (Ψ A ◁ σ)` is
natural if `μ` is. -/
lemma twistIso_hom_naturality (hκ : ∀ A, (κ A).inv = Ψ.obj A ◁ σ ≫ μ A T)
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    {A B : C} (f : A ⟶ B) :
    Ψ.map (f ▷ T) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ T' := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, hκ, hκ, Category.assoc,
    ← tensorHom_id, ← hμ, CategoryTheory.Functor.map_id, tensorHom_id, whisker_exchange_assoc]

/-- The twist isomorphism `κ_A : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'` with inverse `μ_{A,T} ∘ (Ψ A ◁ σ)` is
compatible with `μ` if `μ` is associative. -/
lemma twistIso_tensor (hκ : ∀ A, (κ A).inv = Ψ.obj A ◁ σ ≫ μ A T)
    (hassoc : ∀ A B C : C, Ψ.obj A ◁ μ B C ≫ μ A (B ⊗ C) ≫ Ψ.map (α_ A B C).inv =
      (α_ _ _ _).inv ≫ μ A B ▷ _ ≫ μ (A ⊗ B) C) (A B : C) :
    μ A (B ⊗ T) ≫ Ψ.map (α_ A B T).inv ≫ (κ (A ⊗ B)).hom =
      Ψ.obj A ◁ (κ B).hom ≫ (α_ _ _ _).inv ≫ μ A B ▷ T' := by
  rw [← cancel_mono (κ (A ⊗ B)).inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Category.assoc, Category.assoc, hκ, ← whisker_exchange_assoc,
    ← associator_inv_naturality_right_assoc, ← hassoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp_assoc, Category.assoc, ← hκ, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The twist isomorphism `κ_A : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'` with inverse `μ_{A,T} ∘ (Ψ A ◁ σ)`
intertwines an endomorphism `ρ` of `Ψ` commuting with `μ` and fixing `σ`, with `ρ ▷ T'`. -/
lemma app_comp_twistIso_hom (hκ : ∀ A, (κ A).inv = Ψ.obj A ◁ σ ≫ μ A T)
    (ρ : ∀ A : C, Ψ.obj A ⟶ Ψ.obj A)
    (hρ : ∀ A B, (ρ A ⊗ₘ ρ B) ≫ μ A B = μ A B ≫ ρ (A ⊗ B)) (hσ : σ ≫ ρ T = σ) (A : C) :
    ρ (A ⊗ T) ≫ (κ A).hom = (κ A).hom ≫ ρ A ▷ T' := by
  have key : (κ A).inv ≫ ρ (A ⊗ T) = ρ A ▷ T' ≫ (κ A).inv := by
    rw [hκ, Category.assoc, ← hρ, ← Category.assoc, ← Category.assoc, tensorHom_def',
      ← whiskerLeft_comp_assoc, hσ, whisker_exchange]
  rw [← cancel_epi (κ A).inv, Iso.inv_hom_id_assoc, ← Category.assoc, key, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Twist

end CategoryTheory

/-! ### Left derived functors of exact functors on objects in degree `0` -/

namespace CategoryTheory.Functor

universe wC wD vC vD uC uD

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For an exact functor `F`, the identification `LF(A[0]) ≅ D(F)(A[0]) ≅ (F A)[0]` followed by
`φ[0]` for `φ : F A ⟶ B` is the counit of the left derived functor followed by the morphism
`F(A[0]) ⟶ B[0]` of the homotopy category induced by `φ`. -/
private lemma leftDerivedFunctorIsoMapDerivedCategory_hom_app_single_comp {A : C} {B : D}
    (φ : F.obj A ⟶ B) :
    F.leftDerivedFunctorIsoMapDerivedCategory.hom.app ((DerivedCategory.singleFunctor C 0).obj A) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app A ≫ (DerivedCategory.singleFunctor D 0).map φ =
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C _).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj A)) ≫
      DerivedCategory.Qh.map (F.mapHomotopyCategorySingleHom φ) := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  congr 1
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, mapDerivedCategorySingleFunctor_hom_app_eq,
    mapHomotopyCategorySingleHom, mapHomotopyCategoryFactors_hom_app_eq_id]
  have h₁ (K : CochainComplex C ℤ) : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have h₂ (K : CochainComplex D ℤ) : (DerivedCategory.quotientCompQhIso D).inv.app K = 𝟙 _ := rfl
  have h₃ (K : CochainComplex C ℤ) :
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := rfl
  simp only [h₁, h₂, h₃, Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc]
  congr 1
  erw [Category.id_comp, Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The isomorphism `LF(A[0]) ≅ D(F)(A[0]) ≅ (F A)[0] ≅ B[0]` induced by `e : F A ≅ B` is the
counit of the left derived functor followed by the morphism of the homotopy category induced by
`e`. -/
private lemma leftDerivedFunctorIsoMapDerivedCategory_app_single_trans_hom {A : C} {B : D}
    (e : F.obj A ≅ B) :
    ((F.leftDerivedFunctorIsoMapDerivedCategory.app ((DerivedCategory.singleFunctor C 0).obj A) ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app A) ≪≫
        (DerivedCategory.singleFunctor D 0).mapIso e).hom =
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C _).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj A)) ≫
      DerivedCategory.Qh.map (F.mapHomotopyCategorySingleHom e.hom) := by
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Iso.app_hom, Iso.app_hom, Functor.mapIso_hom]
  exact F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_single_comp e.hom

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- **The canonical pullback isomorphism of `ℚ̄_ℓ(0)` is the unit comparison**: since
`ℚ̄_ℓ,Y(0)[0]` is the tensor unit, the isomorphism `Lf^* ℚ̄_ℓ,Y(0) ≅ ℚ̄_ℓ,X(0)`
(`ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedZeroIso`) is the unit comparison
`Lf^* Λ_Y ≅ Λ_X` of the monoidal derived pullback. -/
private lemma leftDerivedUpperStarTateTwistDerivedZeroIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (ℓ : ℕ)
    [Fact ℓ.Prime] :
    leftDerivedUpperStarTateTwistDerivedZeroIso f ℓ =
      leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f :=
  Iso.ext ((Functor.leftDerivedFunctorIsoMapDerivedCategory_app_single_trans_hom _
    (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm).trans
    (leftDerivedUpperStarUnitIso_hom_eq _ f).symm)

namespace NearbyCyclesModel

/-! ### The action of self-maps and the specialization maps commute with the shifts -/

section Shift

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

/-- **The action of a self-map of a model commutes with the shifts**:
`ρ(s)(K[n]) = Ψ(K[n]) ≅ (Ψ K)[n] ⟶ (Ψ K)[n] ≅ Ψ(K[n])`, by the commutation of the pullback
exchange with the shifts (`NearbyCyclesModel.Hom.commShift_pullbackExchange`). -/
lemma Hom.autAction_shift_comp (s : M.Hom M (𝟙 X) (𝟙 X')) (n : ℤ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    s.autAction Λ (K⟦n⟧) ≫ ((M.nearbyCycles Λ).commShiftIso n).hom.app K =
      ((M.nearbyCycles Λ).commShiftIso n).hom.app K ≫ (shiftFunctor _ n).map (s.autAction Λ K) :=
  comp_commShiftIso_hom_app_of_exchange (leftDerivedUpperStarId Λ X)
    (leftDerivedUpperStarId Λ X') (s.pullbackExchange Λ) n K

/-- **The specialization map commutes with the shifts**: for `e : Lε^* T ≅ Lj^* W`, the
specialization map of the shifted isomorphism `Lε^*(T[n]) ≅ (Lε^* T)[n] ≅ (Lj^* W)[n] ≅
Lj^*(W[n])`, transported along the commutation of `Li^*` and `Ψ` with the shifts, is the shift of
the specialization map `σ_e` (`NearbyCyclesModel.twistSpecializationMap`). -/
lemma twistSpecializationMap_shift_comp
    {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj Λ M.total))}
    {T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (e : L((M.ε)^*⟦Λ⟧).obj T ≅ L((M.j)^*⟦Λ⟧).obj W) (n : ℤ) :
    ((L((M.i)^*⟦Λ⟧).commShiftIso n).app W).inv ≫
        M.twistSpecializationMap Λ (((L((M.ε)^*⟦Λ⟧).commShiftIso n).app T) ≪≫
          (shiftFunctor _ n).mapIso e ≪≫ ((L((M.j)^*⟦Λ⟧).commShiftIso n).app W).symm) ≫
        ((M.nearbyCycles Λ).commShiftIso n).hom.app T =
      (shiftFunctor _ n).map (M.twistSpecializationMap Λ e) :=
  shift_map_unit_comp_eq (I := L((M.i)^*⟦Λ⟧)) (derivedUpperStarLowerStarAdjunction Λ M.j) e n

end Shift

/-! ### The action of self-maps fixes the specialization map of `ℚ̄_ℓ(0)` -/

section Zero

variable {ℓ : ℕ} [Fact ℓ.Prime] {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

/-- In degree `0`, the specialization map `σ : Li^* ℚ̄_ℓ(0) ⟶ Ψ ℚ̄_ℓ(0)` for the canonical
comparisons of the Tate twists with the pullbacks along `ε` and `j` is the specialization unit,
up to the unit comparison of `Li^*`. -/
private lemma twistSpecializationMap_tateTwistZero :
    M.twistSpecializationMap (Profinite.padicAlgClRingObj ℓ)
        (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
          (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) M.i).hom ≫
        M.unit (Profinite.padicAlgClRingObj ℓ) := by
  rw [leftDerivedUpperStarTateTwistDerivedZeroIso_eq,
    leftDerivedUpperStarTateTwistDerivedZeroIso_eq, unit, Iso.hom_inv_id_assoc]
  rfl

/-- **The action of a self-map fixes the specialization map of `ℚ̄_ℓ(0)`**, since it fixes the
specialization unit (`NearbyCyclesModel.Hom.unit_comp_autAction`). -/
lemma twistSpecializationMap_tateTwistZero_comp_autAction (s : M.Hom M (𝟙 X) (𝟙 X')) :
    M.twistSpecializationMap (Profinite.padicAlgClRingObj ℓ)
        (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
          (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) ≫
        s.autAction (Profinite.padicAlgClRingObj ℓ) (tateTwistDerived X ℓ 0) =
      M.twistSpecializationMap (Profinite.padicAlgClRingObj ℓ)
        (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
          (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) := by
  rw [twistSpecializationMap_tateTwistZero, Category.assoc]
  exact congrArg _ (s.unit_comp_autAction _)

set_option maxRecDepth 20000 in
-- the defeq checks of the shifts of the derived categories of module objects are deep, and the
-- specialization maps and the actions of the model unfold to large terms
/-- **The action of a self-map fixes the specialization map of `ℚ̄_ℓ(0)[n]`**, on the ambient
derived categories: the action and the specialization map commute with the shifts
(`NearbyCyclesModel.Hom.autAction_shift_comp`,
`NearbyCyclesModel.twistSpecializationMap_shift_comp`), and in degree `0` the action fixes the
specialization map (`NearbyCyclesModel.twistSpecializationMap_tateTwistZero_comp_autAction`). -/
lemma twistSpecializationMap_tateTwistZero_shift_comp_autAction (s : M.Hom M (𝟙 X) (𝟙 X'))
    (n : ℤ) :
    (shiftFunctor _ n).map (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv ≫
      ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).inv ≫
        M.twistSpecializationMap _
          (((L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _) ≪≫
            (shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
              (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) ≪≫
            ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm) ≫
          s.autAction (Profinite.padicAlgClRingObj ℓ) ((shiftFunctor _ n).obj
            (tateTwistDerived X ℓ 0)) =
      (shiftFunctor _ n).map (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv ≫
        ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).inv ≫
          M.twistSpecializationMap _
            (((L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _) ≪≫
              (shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
                (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) ≪≫
              ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm) := by
  refine comp_eq_of_shift_comp n
    ((shiftFunctor _ n).map (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv)
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).inv
    (M.twistSpecializationMap _
      (((L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _) ≪≫
        (shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
          (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) ≪≫
        ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm))
    (((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).commShiftIso n).hom.app
      (tateTwistDerived X ℓ 0))
    (M.twistSpecializationMap _ (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
      (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm))
    (s.autAction (Profinite.padicAlgClRingObj ℓ) ((shiftFunctor _ n).obj (tateTwistDerived X ℓ 0)))
    (s.autAction (Profinite.padicAlgClRingObj ℓ) (tateTwistDerived X ℓ 0))
    ?_ ?_ ?_
  · exact twistSpecializationMap_shift_comp _ _ n
  · exact s.autAction_shift_comp (Profinite.padicAlgClRingObj ℓ) n (tateTwistDerived X ℓ 0)
  · exact twistSpecializationMap_tateTwistZero_comp_autAction (ℓ := ℓ) s

end Zero

end NearbyCyclesModel


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

/-- The specialization map `σ : ℚ̄_ℓ,X'(0)[n] ⟶ Ψ (ℚ̄_ℓ,X(0)[n])`: the specialization map of the
Tate twists (`NearbyCyclesModel.tateTwistSpecializationMap`) for the canonical comparisons
`Lε^* ℚ̄_ℓ(0) ≅ ℚ̄_ℓ(0)`, `Lj^* ℚ̄_ℓ(0) ≅ ℚ̄_ℓ(0)` and `Li^* ℚ̄_ℓ(0) ≅ ℚ̄_ℓ(0)`
(`ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedZeroIso`). -/
noncomputable def zeroTwistSpecializationMap
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) (n : ℤ) :
    boundedConstructibleTateTwist ℓ X' 0 n ⟶
      (boundedConstructibleNearbyCycles hP).obj (boundedConstructibleTateTwist ℓ X 0 n) :=
  ObjectProperty.homMk (((shiftFunctor _ n).mapIso
      (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).symm ≪≫
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm).hom ≫
      M.twistSpecializationMap _
        (((L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _) ≪≫
          (shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
            (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) ≪≫
          ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm))

/-- **Nearby cycles commute with the twist by `ℚ̄_ℓ(0)[n]`** (blueprint
`lemma-nearby-duality-slice--1`, the twist (1)): `κ_A : Ψ (A ⊗ ℚ̄_ℓ,X(0)[n]) ≅ Ψ A ⊗ ℚ̄_ℓ,X'(0)[n]`,
the isomorphism `NearbyCyclesModel.nearbyCyclesTateTwistIso` for `d = 0` and the canonical
comparisons of `ℚ̄_ℓ(0)` with the pullbacks; `ℚ̄_ℓ(0)` is dualizable on the total space, which
lives over the trait through `q` (`ProEtale.CondensedRing.isDualizable_tateTwistDerived_of_trait`).
Its inverse is `μ_{A,T} ∘ (Ψ A ◁ σ)` (`NearbyCyclesModel.zeroTwistIso_inv`). -/
noncomputable def zeroTwistIso
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (q : M.total ⟶ trait k') (n : ℤ) (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles hP).obj (A ⊗ boundedConstructibleTateTwist ℓ X 0 n) ≅
      (boundedConstructibleNearbyCycles hP).obj A ⊗ boundedConstructibleTateTwist ℓ X' 0 n :=
  M.nearbyCyclesTateTwistIso hP (isDualizable_tateTwistDerived_of_trait ℓ q 0)
    (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ)
    (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ)
    (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ) n A

/-- The inverse of `κ_A` is the lax tensor map precomposed with `Ψ A ◁ σ`. -/
lemma zeroTwistIso_inv (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (q : M.total ⟶ trait k') (n : ℤ) (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (M.zeroTwistIso hP q n A).inv =
      (boundedConstructibleNearbyCycles hP).obj A ◁ M.zeroTwistSpecializationMap hP n ≫
        boundedConstructibleTensorMap hP A (boundedConstructibleTateTwist ℓ X 0 n) :=
  rfl

/-- **Naturality of `κ`**: `κ_B ∘ Ψ(f ▷ T) = (Ψ f ▷ T') ∘ κ_A`. -/
lemma zeroTwistIso_hom_naturality
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (q : M.total ⟶ trait k') (n : ℤ) {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : A ⟶ B) :
    (boundedConstructibleNearbyCycles hP).map (f ▷ boundedConstructibleTateTwist ℓ X 0 n) ≫
        (M.zeroTwistIso hP q n B).hom =
      (M.zeroTwistIso hP q n A).hom ≫
        (boundedConstructibleNearbyCycles hP).map f ▷ boundedConstructibleTateTwist ℓ X' 0 n :=
  twistIso_hom_naturality (boundedConstructibleTensorMap hP) (M.zeroTwistSpecializationMap hP n)
    (M.zeroTwistIso hP q n) (M.zeroTwistIso_inv hP q n)
    (fun x y ↦ boundedConstructibleTensorMap_natural hP x y) f

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- The lax tensor map of nearby cycles on bounded constructible complexes is associative. -/
lemma boundedConstructibleTensorMap_associativity_inv
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles hP).obj A ◁ boundedConstructibleTensorMap hP B C ≫
        boundedConstructibleTensorMap hP A (B ⊗ C) ≫
          (boundedConstructibleNearbyCycles hP).map (α_ A B C).inv =
      (α_ _ _ _).inv ≫ boundedConstructibleTensorMap hP A B ▷ _ ≫
        boundedConstructibleTensorMap hP (A ⊗ B) C := by
  let := boundedConstructibleNearbyCyclesLaxMonoidal hP
  have h := Functor.LaxMonoidal.associativity_inv (boundedConstructibleNearbyCycles hP) A B C
  simp only [boundedConstructibleNearbyCycles_μ] at h
  exact h

/-- **Compatibility of `κ` with the lax tensor map** of nearby cycles, in the form of the
hypothesis of `CategoryTheory.Verdier.isIso_nearbyDualityMap_of_iso_twist_iff`: it follows from
the associativity of `μ`, `κ⁻¹` being `μ ∘ (Ψ ◁ σ)`. -/
lemma zeroTwistIso_tensor (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (q : M.total ⟶ trait k') (n : ℤ) (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleTensorMap hP A (B ⊗ boundedConstructibleTateTwist ℓ X 0 n) ≫
        (boundedConstructibleNearbyCycles hP).map (α_ A B _).inv ≫
          (M.zeroTwistIso hP q n (A ⊗ B)).hom =
      (boundedConstructibleNearbyCycles hP).obj A ◁ (M.zeroTwistIso hP q n B).hom ≫
        (α_ _ _ _).inv ≫ boundedConstructibleTensorMap hP A B ▷ _ :=
  twistIso_tensor (boundedConstructibleTensorMap hP) (M.zeroTwistSpecializationMap hP n)
    (M.zeroTwistIso hP q n) (M.zeroTwistIso_inv hP q n)
    (boundedConstructibleTensorMap_associativity_inv hP) A B

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- The action of a self-map of the model on bounded constructible complexes is monoidal
(`NearbyCyclesModel.Hom.autAction_tensor`). -/
lemma Hom.boundedConstructibleAutAction_tensor (s : M.Hom M (𝟙 _) (𝟙 _))
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((s.boundedConstructibleAutAction hP).app A ⊗ₘ (s.boundedConstructibleAutAction hP).app B) ≫
        boundedConstructibleTensorMap hP A B =
      boundedConstructibleTensorMap hP A B ≫ (s.boundedConstructibleAutAction hP).app (A ⊗ B) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.tensorHom_hom',
    Hom.boundedConstructibleAutAction_app, boundedConstructibleTensorMap, ObjectProperty.homMk_hom]
  exact s.autAction_tensor _ A.obj B.obj


/-- **The action of a self-map fixes the specialization map of `ℚ̄_ℓ(0)[n]`** (blueprint
`lemma-nearby-duality-slice--1`, "`P` acts trivially on the twist"): `σ ∘ ρ(s) = σ`. The action
commutes with the shifts (`NearbyCyclesModel.Hom.autAction_shift_comp`), so does `σ`
(`NearbyCyclesModel.twistSpecializationMap_shift_comp`), and in degree `0` the specialization
map is the specialization unit
(`NearbyCyclesModel.twistSpecializationMap_tateTwistZero_comp_autAction`). -/
lemma zeroTwistSpecializationMap_comp_boundedConstructibleAutAction_app
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (s : M.Hom M (𝟙 _) (𝟙 _)) (n : ℤ) :
    M.zeroTwistSpecializationMap hP n ≫
        (s.boundedConstructibleAutAction hP).app (boundedConstructibleTateTwist ℓ X 0 n) =
      M.zeroTwistSpecializationMap hP n := by
  apply ObjectProperty.hom_ext
  simp only [zeroTwistSpecializationMap, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, Hom.boundedConstructibleAutAction_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Category.assoc, boundedConstructibleTateTwist]
  exact twistSpecializationMap_tateTwistZero_shift_comp_autAction (ℓ := ℓ) s n

/-- **`κ` is invariant under the self-maps of the model** (blueprint
`lemma-nearby-duality-slice--1`, "`P` acts trivially on `A(1)[2]`", for the twist by `ℚ̄_ℓ(0)[n]`):
`κ_A ∘ ρ(s)_{A ⊗ T} = (ρ(s)_A ▷ T') ∘ κ_A`, by the monoidality of the action
(`NearbyCyclesModel.Hom.boundedConstructibleAutAction_tensor`) and its triviality on the
specialization map
(`NearbyCyclesModel.zeroTwistSpecializationMap_comp_boundedConstructibleAutAction_app`). -/
lemma boundedConstructibleAutAction_app_comp_zeroTwistIso_hom
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (q : M.total ⟶ trait k') (s : M.Hom M (𝟙 _) (𝟙 _)) (n : ℤ)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (s.boundedConstructibleAutAction hP).app (A ⊗ boundedConstructibleTateTwist ℓ X 0 n) ≫
        (M.zeroTwistIso hP q n A).hom =
      (M.zeroTwistIso hP q n A).hom ≫
        (s.boundedConstructibleAutAction hP).app A ▷ boundedConstructibleTateTwist ℓ X' 0 n :=
  app_comp_twistIso_hom (boundedConstructibleTensorMap hP) (M.zeroTwistSpecializationMap hP n)
    (M.zeroTwistIso hP q n) (M.zeroTwistIso_inv hP q n)
    (fun A ↦ (s.boundedConstructibleAutAction hP).app A)
    (s.boundedConstructibleAutAction_tensor hP)
    (M.zeroTwistSpecializationMap_comp_boundedConstructibleAutAction_app hP s n) A

end NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The isomorphism `ℚ̄_ℓ(0)[a] ⊗ ℚ̄_ℓ(0)[b] ≅ ℚ̄_ℓ` for `a + b = 0` in the derived category. -/
noncomputable def tateTwistDerivedZeroShiftTensorShiftIso (Z : Scheme.{u}) {a b : ℤ}
    (h : a + b = 0) :
    (shiftFunctor _ a).obj (tateTwistDerived Z ℓ 0) ⊗
        (shiftFunctor _ b).obj (tateTwistDerived Z ℓ 0) ≅ 𝟙_ _ :=
  DerivedCategory.shiftTensorShiftIso _ _ _ a b ≪≫
    (shiftFunctor _ (a + b)).mapIso
      ((tateTwistDerivedZeroIso ℓ Z ⊗ᵢ tateTwistDerivedZeroIso ℓ Z) ≪≫ λ_ _) ≪≫
    (shiftFunctorZero' _ (a + b) h).app _

/-- **The twist `ℚ̄_ℓ(0)[n]` is invertible**: its inverse is `ℚ̄_ℓ(0)[-n]`
(`ProEtale.CondensedRing.tateTwistDerivedZeroShiftTensorShiftIso`). -/
theorem isInvertible_boundedConstructibleTateTwist_zero (n : ℤ) :
    IsInvertible (boundedConstructibleTateTwist ℓ X 0 n) :=
  ⟨boundedConstructibleTateTwist ℓ X 0 (-n),
    ⟨(boundedConstructible _).fullyFaithfulι.preimageIso
      (tateTwistDerivedZeroShiftTensorShiftIso ℓ X.left (add_neg_cancel n))⟩,
    ⟨(boundedConstructible _).fullyFaithfulι.preimageIso
      (tateTwistDerivedZeroShiftTensorShiftIso ℓ X.left (neg_add_cancel n))⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
