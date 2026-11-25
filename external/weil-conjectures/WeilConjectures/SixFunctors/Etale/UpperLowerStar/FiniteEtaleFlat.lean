/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Pullback along a finite étale morphism preserves flat sheaves

Let `f : X ⟶ Y` be finite étale. Then `f_*` is exact, being both a left adjoint
(`AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`) and a right adjoint of `f^*`,
and extension by zero off the graphs `η : 𝟭 ⟶ f_* ⋙ f^*` is a natural section of the counit of
`f^* ⊣ f_*`. Hence for a sheaf `F` on `Y_ét`, tensoring with `f^* F` is a natural retract of

`G ↦ f^* F ⊗ f^* f_* G ≅ f^* (F ⊗ f_* G)`,

which is exact when `F` is flat. So `f^*` sends flat sheaves to flat sheaves.

## Main results

- `AlgebraicGeometry.Etale.preservesFlat_upperStar_of_isFinite`: for a finite étale `f`, the
  pullback `f^*` preserves flat objects.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Etale f] [IsFinite f]

/-- For a finite étale `f`, extension by zero off the graphs, `𝟭 ⟶ f_* ⋙ f^*`. -/
noncomputable def lowerStarUnitUpperStar : 𝟭 (Sheaf X.smallEtaleTopology A) ⟶ (f)_*[A] ⋙ (f)^*[A] :=
  Etale.lowerStarUnit A f ≫
    Functor.whiskerLeft (f)_*[A] (Etale.upperStarIsoLocalizationRestriction A f ‹_›).inv

/-- A natural retraction of `AlgebraicGeometry.Etale.lowerStarUnitUpperStar`. -/
noncomputable def lowerStarUnitUpperStarRetraction :
    (f)_*[A] ⋙ (f)^*[A] ⟶ 𝟭 (Sheaf X.smallEtaleTopology A) :=
  Functor.whiskerLeft (f)_*[A] (Etale.upperStarIsoLocalizationRestriction A f ‹_›).hom ≫
    (Etale.localizationRestrictionLowerStarAdjunction A f ‹_›).counit

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A] in
@[reassoc (attr := simp)]
lemma lowerStarUnitUpperStar_comp_retraction :
    lowerStarUnitUpperStar A f ≫ lowerStarUnitUpperStarRetraction A f = 𝟙 _ := by
  ext G : 2
  simp only [lowerStarUnitUpperStar, lowerStarUnitUpperStarRetraction, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun φ ↦ φ.app G) (lowerStarUnit_comp_counit A f)

instance preservesFiniteColimits_lowerStar_of_isFinite_of_etale :
    PreservesFiniteColimits (f)_*[A] :=
  have : PreservesColimitsOfSize.{0, 0} (f)_*[A] :=
    (lowerStarUpperStarAdjunctionOfIsFinite A f).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

omit [MonoidalPreadditive A] in
/-- For a finite étale `f` and a flat `F`, the functor `f_* ⋙ (F ⊗ -) ⋙ f^*` is exact. -/
lemma exactFunctor_lowerStar_comp_tensorLeft_comp_upperStar {F : Sheaf Y.smallEtaleTopology A}
    (hF : ObjectProperty.flat F) :
    exactFunctor _ _ ((f)_*[A] ⋙ tensorLeft F ⋙ (f)^*[A]) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 hF.tensorLeft
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

omit [MonoidalPreadditive A] in
/-- For a finite étale `f` and a flat `F`, the functor `f_* ⋙ (- ⊗ F) ⋙ f^*` is exact. -/
lemma exactFunctor_lowerStar_comp_tensorRight_comp_upperStar {F : Sheaf Y.smallEtaleTopology A}
    (hF : ObjectProperty.flat F) :
    exactFunctor _ _ ((f)_*[A] ⋙ tensorRight F ⋙ (f)^*[A]) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 hF.tensorRight
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- The pullback `f^*` along a finite étale `f` sends flat étale sheaves to flat étale
sheaves. -/
instance preservesFlat_upperStar_of_isFinite : (f)^*[A].PreservesFlat where
  flat_obj {F} hF := by
    let η := lowerStarUnitUpperStar A f
    let ε := lowerStarUnitUpperStarRetraction A f
    constructor
    · -- `f^* F ⊗ -` is a retract of `f^* F ⊗ f^* f_* - ≅ f^* (F ⊗ f_* -)`
      let e := Functor.isoWhiskerLeft (f)_*[A] (Functor.Monoidal.commTensorLeft (f)^*[A] F)
      refine Functor.exactFunctor_of_retract
        ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight η _ ≫ (Functor.associator _ _ _).hom ≫
          e.hom)
        (e.inv ≫ (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε _ ≫
          (Functor.leftUnitor _).hom) ?_
        ((exactFunctor _ _).prop_of_iso (Functor.associator _ _ _).symm
          (exactFunctor_lowerStar_comp_tensorLeft_comp_upperStar A f hF))
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      ext G : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
        Functor.leftUnitor_hom_app, Category.id_comp, NatTrans.id_app]
      rw [← Functor.map_comp_assoc, ← NatTrans.comp_app, lowerStarUnitUpperStar_comp_retraction]
      simp
    · let e := Functor.isoWhiskerLeft (f)_*[A] (Functor.Monoidal.commTensorRight (f)^*[A] F)
      refine Functor.exactFunctor_of_retract
        ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight η _ ≫ (Functor.associator _ _ _).hom ≫
          e.hom)
        (e.inv ≫ (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε _ ≫
          (Functor.leftUnitor _).hom) ?_
        ((exactFunctor _ _).prop_of_iso (Functor.associator _ _ _).symm
          (exactFunctor_lowerStar_comp_tensorRight_comp_upperStar A f hF))
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      ext G : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
        Functor.leftUnitor_hom_app, Category.id_comp, NatTrans.id_app]
      rw [← Functor.map_comp_assoc, ← NatTrans.comp_app, lowerStarUnitUpperStar_comp_retraction]
      simp

end Etale

end AlgebraicGeometry
