/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafReduction
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Derived pushforward of `𝒪_{E,T}` as a derived limit of étale pushforwards

Let `g : T ⟶ Y` be a morphism of schemes and `E` a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`. In the
derived category of abelian sheaves on `Y_proét`:

- `AlgebraicGeometry.ProEtale.isHomotopyLimit_rightDerivedLowerStar_padicIntegersSheafCone`:
  `Rg_* 𝒪_{E,T} ≅ R lim_n Rg_* C(-, 𝒪_E ⧸ ℓⁿ)`, the derived pushforward being a triangulated right
  adjoint and `𝒪_{E,T} ≅ R lim_n C(-, 𝒪_E ⧸ ℓⁿ)`
  (`AlgebraicGeometry.ProEtale.isHomotopyLimit_padicIntegersSheafCone`);
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarContinuousMapAbSheafIso`: for `g`
  quasi-compact and quasi-separated and a discrete ring `Q` (such as `𝒪_E ⧸ ℓⁿ`),
  `Rg_* C(-, Q) ≅ ν^* Rg_*^{ét} Q`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarContinuousMapAbSheafTowerIso`: the same, as
  an isomorphism of towers `n ↦ Rg_* C(-, Qₙ) ≅ ν^* Rg_*^{ét} Qₙ` for a tower of discrete rings,
  using the naturality of `C(-, Q) ≅ ν^* Q` in `Q`.
- `isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower` (in the
  namespace `AlgebraicGeometry.ProEtale`): consequently
  `Rg_* 𝒪_{E,T} ≅ R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`.

These are steps (3)–(5) of the comparison of `ℓ`-adic and torsion étale direct images for the
constant sheaf, needed for the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`). The comparison `Rg_* ν^* ≅ ν^* Rg_*^{ét}`
uses `AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {T Y : Scheme.{u}} (g : T ⟶ Y) (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- **`Rg_* 𝒪_{E,T} = R lim_n Rg_* C(-, 𝒪_E ⧸ ℓⁿ)`**: the derived pushforward, a triangulated right
adjoint, commutes with the derived limit `𝒪_{E,T} ≅ R lim_n C(-, 𝒪_E ⧸ ℓⁿ)`
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_padicIntegersSheafCone`). -/
theorem isHomotopyLimit_rightDerivedLowerStar_padicIntegersSheafCone :
    letI := normedFieldOfAlgebra l E
    IsHomotopyLimit ((ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor.mapCone
      ((DerivedCategory.singleFunctor _ 0).mapCone
        (continuousMapAbSheafCone T (integersModPowTransition l E)
          (fun _ ↦ continuous_of_discreteTopology) (integersModPowMk l E)
          (continuous_integersModPowMk l E) (integersModPowTransition_comp l E)))) :=
  letI := normedFieldOfAlgebra l E
  have := ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    |>.mapDerivedCategoryRightDerivedAdjunction).isRightAdjoint
  (isHomotopyLimit_padicIntegersSheafCone T l E).map _

section Comparison

variable (Q : Type) [TopologicalSpace Q] [Ring Q] [IsTopologicalRing Q] [DiscreteTopology Q]

/-- **Pushforward of continuous maps to a discrete ring**: for `g` quasi-compact and
quasi-separated and a discrete ring `Q`, the derived pushforward `Rg_* C(-, Q)` on the pro-étale
site is the comparison pullback `ν^*` of the derived étale pushforward `Rg_*^{ét} Q` of the
constant étale sheaf: `C(-, Q) ≅ ν^* Q`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf`) and
`Rg_* ν^* ≅ ν^* Rg_*^{ét}` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'`). -/
noncomputable def rightDerivedLowerStarContinuousMapAbSheafIso [QuasiCompact g]
    [QuasiSeparated g] :
    (ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (continuousMapAbSheaf T Q)) ≅
      (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj
        ((Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf T.smallEtaleTopology Ab.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} Q)))))) :=
  (ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf T Q).symm ≪≫
        (((comparisonUpperStar Ab.{u + 1} T).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
        (comparisonUpperStar Ab.{u + 1} T).mapDerivedCategory.mapIso
          ((DerivedCategory.Plus.singleFunctorιIso _ 0).app _).symm) ≪≫
    ((rightDerivedLowerStarComparisonIso' g Ab.{u + 1}).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ((constantSheaf T.smallEtaleTopology
        Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} Q))))).symm

end Comparison

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

section Naturality

variable (X : Scheme.{u}) {T T' : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  [DiscreteTopology T] [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T'] [DiscreteTopology T']

/-- A ring homomorphism, as a morphism of the universe lifts of the underlying groups. -/
noncomputable def uliftAddHom (τ : T →+* T') :
    AddCommGrpCat.of (ULift.{u + 1} T) ⟶ AddCommGrpCat.of (ULift.{u + 1} T') :=
  AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (τ.toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom))

/-- The identification of the constant sheaf with continuous maps to a discrete ring is natural
in the ring. -/
lemma constantSheaf_map_comp_constantSheafIsoContinuousMapRingSheaf_hom (τ : T →+* T') :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).map (uliftAddHom.{u} τ) ≫
        (constantSheafIsoContinuousMapRingSheaf X T').hom =
      (constantSheafIsoContinuousMapRingSheaf X T).hom ≫
        continuousMapAbSheafMap X τ continuous_of_discreteTopology := by
  have hc := (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).counit.naturality
    (continuousMapAbSheafMap X τ continuous_of_discreteTopology)
  simp only [Functor.comp_map, Functor.id_map] at hc
  simp only [constantSheafIsoContinuousMapRingSheaf, Iso.trans_hom, asIso_hom, Category.assoc]
  refine Eq.trans ?_ (congrArg (fun k ↦ (presheafToSheaf _ _).map
    (constToContinuousMapPresheaf X T) ≫ k) hc)
  change (presheafToSheaf _ _).map ((Functor.const _).map (uliftAddHom τ)) ≫
    (presheafToSheaf _ _).map (constToContinuousMapPresheaf X T') ≫ _ = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rfl

end Naturality

section Tower

variable {T Y : Scheme.{u}} (g : T ⟶ Y) {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)]
  [∀ n, Ring (Qs n)] [∀ n, IsTopologicalRing (Qs n)] [∀ n, DiscreteTopology (Qs n)]
  (τ : ∀ n, Qs (n + 1) →+* Qs n)

variable (T) in
/-- The tower of constant étale sheaves `n ↦ Qₙ` attached to a tower of rings. -/
noncomputable def constantSheafTower : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology Ab.{u + 1} :=
  Functor.ofOpSequence (C := Sheaf T.smallEtaleTopology Ab.{u + 1})
    (X := fun n ↦ (constantSheaf T.smallEtaleTopology Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (Qs n))))
    fun n ↦ (constantSheaf T.smallEtaleTopology Ab.{u + 1}).map (uliftAddHom.{u} (τ n))

omit [∀ n, TopologicalSpace (Qs n)] [∀ n, IsTopologicalRing (Qs n)]
  [∀ n, DiscreteTopology (Qs n)] in
lemma constantSheafTower_map_succ (n : ℕ) :
    (constantSheafTower T τ).map (homOfLE (n.le_add_right 1)).op =
      (constantSheaf T.smallEtaleTopology Ab.{u + 1}).map (uliftAddHom.{u} (τ n)) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

variable (T) in
/-- The tower `n ↦ C(-, Qₙ)` is the comparison pullback of the tower of constant étale sheaves
`n ↦ Qₙ`. -/
noncomputable def comparisonUpperStarConstantSheafTowerIso :
    constantSheafTower T τ ⋙ ν^*(T)[Ab.{u + 1}] ≅
      continuousMapAbSheafTower T τ (fun _ ↦ continuous_of_discreteTopology) :=
  let α : constantSheafTower T τ ⋙ ν^*(T)[Ab.{u + 1}] ⟶
      continuousMapAbSheafTower T τ (fun _ ↦ continuous_of_discreteTopology) :=
    NatTrans.ofOpSequence
      (fun n ↦ (comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf T (Qs n)).hom)
      fun n ↦ by
        rw [Functor.comp_map]
        erw [constantSheafTower_map_succ, continuousMapAbSheafTower_map_succ]
        have h1 := (constantSheafCompComparisonUpperStarIso Ab.{u + 1} T).hom.naturality
          (uliftAddHom.{u} (τ n))
        have h2 := constantSheaf_map_comp_constantSheafIsoContinuousMapRingSheaf_hom T (τ n)
        simp only [comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf, Iso.trans_hom,
          Iso.app_hom, Category.assoc, ← h2]
        exact (reassoc_of% h1) _
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    rw [NatTrans.ofOpSequence_app]
    infer_instance
  have := NatIso.isIso_of_isIso_app α
  asIso α

/-- `Rg_* ν^* ≅ ν^* Rg_*^{ét}` on sheaves placed in degree `0`, as functors from étale sheaves on
`T` to the derived category of pro-étale sheaves on `Y`. -/
noncomputable def comparisonUpperStarCompRightDerivedLowerStarIso [QuasiCompact g]
    [QuasiSeparated g] :
    ν^*(T)[Ab.{u + 1}] ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        (ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor ≅
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι ⋙ (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((comparisonUpperStar Ab.{u + 1} T).mapDerivedCategorySingleFunctor
      0).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (DerivedCategory.Plus.singleFunctorιIso _ 0).symm _) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      (rightDerivedLowerStarComparisonIso' g Ab.{u + 1}).symm)

/-- `Rg_* C(-, Qₙ) ≅ ν^* Rg_*^{ét} Qₙ`, as an isomorphism of towers. -/
noncomputable def rightDerivedLowerStarContinuousMapAbSheafTowerIso [QuasiCompact g]
    [QuasiSeparated g] :
    (continuousMapAbSheafTower T τ (fun _ ↦ continuous_of_discreteTopology) ⋙
        DerivedCategory.singleFunctor _ 0) ⋙ (ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor ≅
      constantSheafTower T τ ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι ⋙ (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (comparisonUpperStarConstantSheafTowerIso T τ).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (comparisonUpperStarCompRightDerivedLowerStarIso g)

end Tower

variable {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (l : ℕ) [Fact l.Prime]
  (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- **`Rg_* 𝒪_{E,T} ≅ R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`**: for `g` quasi-compact and
quasi-separated and `E` a finite extension of `ℚ_ℓ`, the derived pushforward of `𝒪_{E,T}` is the
derived limit of the tower `n ↦ ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)` of comparison pullbacks of derived étale
pushforwards of the constant torsion sheaves `𝒪_E ⧸ ℓⁿ`. -/
theorem isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower :
    letI := normedFieldOfAlgebra l E
    IsHomotopyLimit ((Cone.postcompose
      (rightDerivedLowerStarContinuousMapAbSheafTowerIso g (integersModPowTransition l E)).hom).obj
        ((ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor.mapCone
          ((DerivedCategory.singleFunctor _ 0).mapCone
            (continuousMapAbSheafCone T (integersModPowTransition l E)
              (fun _ ↦ continuous_of_discreteTopology) (integersModPowMk l E)
              (continuous_integersModPowMk l E) (integersModPowTransition_comp l E))))) :=
  letI := normedFieldOfAlgebra l E
  (isHomotopyLimit_rightDerivedLowerStar_padicIntegersSheafCone g l E).of_iso
    (rightDerivedLowerStarContinuousMapAbSheafTowerIso g (integersModPowTransition l E)) _
    (Iso.refl _)
    fun n ↦ by simp

end AlgebraicGeometry.ProEtale
