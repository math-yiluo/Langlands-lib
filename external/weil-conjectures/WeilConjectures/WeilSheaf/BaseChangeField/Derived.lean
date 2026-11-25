/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-!
# Right derived functors of composites on categories of algebras

Let `Φ : IsoAlgebra F ⥤ IsoAlgebra F'` be an exact functor between categories of algebras with
invertible structure morphism whose underlying functor `L` preserves K-injective complexes, in
the sense that `Φ ⋙ For ≅ For ⋙ L`. Then the right derived functor of `Φ ⋙ mapOfNatIso e` is
`Φ ⋙ R(mapOfNatIso e)`
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIsoOfIso`): the
complexes of algebras with K-injective underlying complex are acyclic for `R(mapOfNatIso e)`
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_rightDerivedFunctorUnit_app_mapOfNatIso`).
This generalises `CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso`,
where `Φ` is itself a transport `mapOfNatIso`, and
`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIso`, where `Φ` is an
endofunctor of `IsoAlgebra F`.
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  {E : Type u''} [Category.{v''} E] [Abelian E] {H : E ⥤ E} [H.Additive] [H.IsEquivalence]
  (Φ : IsoAlgebra F ⥤ IsoAlgebra G) [Φ.Additive] {L : C ⥤ D} [L.Additive]
  [L.PreservesKInjectiveComplexes] (ε : Φ ⋙ forget G ≅ forget F ⋙ L)
  {L₂ : D ⥤ E} [L₂.Additive] (e₂ : L₂ ⋙ H ≅ G ⋙ L₂)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w''} (IsoAlgebra H)]
  [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra H)]

include ε in
/-- The right derived functor of `Φ`, followed by that of `mapOfNatIso e₂`, is a right derived
functor of the composite `Φ ⋙ mapOfNatIso e₂`, if the underlying functor of `Φ` preserves
K-injective complexes. -/
lemma isRightDerivedFunctor_rightDerivedFunctor_comp_mapOfNatIso_of_iso :
    (Φ.rightDerivedFunctor ⋙ (mapOfNatIso e₂).rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorCompUnit Φ (mapOfNatIso e₂))
      (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((Φ ⋙ mapOfNatIso e₂).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((Functor.rightDerivedFunctorCompUnit Φ (mapOfNatIso e₂)).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
  have h₁ : IsIso (Φ.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := inferInstance
  have : CochainComplex.IsKInjective ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := inferInstance
  have : CochainComplex.IsKInjective (((forget G).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    CochainComplex.isKInjective_of_iso
      (HomologicalComplex.Hom.isoOfComponents
        (C₁ := (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        (fun n ↦ (ε.app (K.X n)).symm)
        (fun i j _ ↦ (ε.inv.naturality (K.d i j)).symm))
  have h₂ := isIso_rightDerivedFunctorUnit_app_mapOfNatIso e₂
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h₂' : IsIso ((mapOfNatIso e₂).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient (IsoAlgebra G) (ComplexShape.up ℤ)).obj
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K).as))) := h₂
  dsimp [Functor.rightDerivedFunctorCompUnit]
  infer_instance

/-- The composition isomorphism `R(Φ ⋙ mapOfNatIso e₂) ≅ Φ ⋙ R(mapOfNatIso e₂)` for an exact
functor `Φ` of algebras whose underlying functor preserves K-injective complexes. -/
noncomputable def rightDerivedFunctorCompMapOfNatIsoIsoOfIso [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] :
    (Φ ⋙ mapOfNatIso e₂).rightDerivedFunctor ≅
      Φ.mapDerivedCategory ⋙ (mapOfNatIso e₂).rightDerivedFunctor :=
  have := isRightDerivedFunctor_rightDerivedFunctor_comp_mapOfNatIso_of_iso Φ ε e₂
  Functor.rightDerivedUnique _ _ (Φ ⋙ mapOfNatIso e₂).rightDerivedFunctorUnit
    (Functor.rightDerivedFunctorCompUnit Φ (mapOfNatIso e₂))
    (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) ≪≫
  Functor.isoWhiskerRight Φ.rightDerivedFunctorIsoMapDerivedCategory _

end CategoryTheory.Endofunctor.IsoAlgebra
