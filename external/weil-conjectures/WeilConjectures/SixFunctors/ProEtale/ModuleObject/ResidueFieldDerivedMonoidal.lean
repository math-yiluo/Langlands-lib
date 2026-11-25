/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafMonoidal

/-!
# The residue field module sheaves are compatible with the derived tensor products

Write `G_X = residueFieldModuleSheaf X ℓ E` for the equivalence between module objects over
`𝔽_{E,X}` and pro-étale sheaves of `𝔽_E`-modules. The derived equivalences `D(G_X)` commute with
the derived tensor products, compatibly with the tensor comparisons of the derived pullbacks and
the isomorphisms `Lf^* ⋙ D(G_X) ≅ D(G_Y) ⋙ Lf^*` (`ProEtale.residueFieldDerivedUpperStarIso`)
(`ProEtale.exists_comparisonCompatible_residueFieldDerivedUpperStarIso`).

The tensor isomorphisms are the derived comparisons
`Functor.leftDerivedTensorComparisonOfNatTrans` of the tensor isomorphisms of `G`
(`ProEtale.residueFieldModuleSheafTensorIso`). Since all the functors involved are exact,
`residueFieldDerivedUpperStarIso` is the isomorphism of composites of left derived functors induced
by the underived commutation `f^* ⋙ G_X ≅ G_Y ⋙ f^*`
(`ProEtale.residueFieldDerivedUpperStarIso_symm_eq`), which is compatible with the tensor
isomorphisms (`ProEtale.tensorCompatible_residueFieldModuleSheafUpperStarIso`); the result follows
from `Functor.comparisonCompatible_leftDerivedFunctorCompNatIso_of_tensorComparison`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

-- Transport the comparisons abstractly so that rewriting does not expand derived categories.
private lemma comparisonCompatible_of_eq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    {F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
    {α α' : N_D ⋙ F' ≅ F ⋙ N_C}
    {φ φ' : F.TensorComparison} {ψ ψ' : F'.TensorComparison}
    {m_C : N_C.TensorIso} {m_D : N_D.TensorIso}
    (hα : α = α') (hφ : φ = φ') (hψ : ψ = ψ')
    (h : Adjunction.ComparisonCompatible α' φ' ψ' m_C m_D) :
    Adjunction.ComparisonCompatible α φ ψ m_C m_D := by
  subst α' φ' ψ'
  exact h

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The residue field `𝔽_E` is a noetherian ring, being finite. -/
instance isNoetherianRing_residueFieldCoeff : IsNoetherianRing (ResidueFieldCoeff.{u} ℓ E) :=
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E)))
  inferInstance

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The inverse of `residueFieldDerivedUpperStarIso` is, through the identifications
`L(G) ≅ D(G)`, the isomorphism `LG_Y ⋙ Lf^* ≅ Lf^* ⋙ LG_X` of composites of left derived functors
induced by the underived commutation `G_Y ⋙ f^* ≅ f^* ⋙ G_X`, all functors being exact. -/
lemma residueFieldDerivedUpperStarIso_symm_eq :
    (residueFieldDerivedUpperStarIso ℓ E f).symm =
      Functor.isoWhiskerRight
          (residueFieldModuleSheaf Y ℓ E).leftDerivedFunctorIsoMapDerivedCategory.symm
          ((f)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]).leftDerivedFunctor ≪≫
        Functor.leftDerivedFunctorCompNatIso
          (f)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧
          (residueFieldModuleSheaf X ℓ E) (residueFieldModuleSheaf Y ℓ E)
          (f)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]
          (residueFieldModuleSheafUpperStarIso ℓ E f).symm ≪≫
        Functor.isoWhiskerLeft
          ((f)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).leftDerivedFunctor
          (residueFieldModuleSheaf X ℓ E).leftDerivedFunctorIsoMapDerivedCategory := by
  ext K
  simp [residueFieldDerivedUpperStarIso, Functor.leftDerivedFunctorCompNatIso,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategoryNatIso_symm]

/-- **`D(G)` is monoidal, compatibly with the derived pullbacks**: there are isomorphisms
`D(G_X)(A ⊗ᴸ B) ≅ D(G_X) A ⊗ᴸ D(G_X) B` such that the isomorphism
`Lf^* ⋙ D(G_X) ≅ D(G_Y) ⋙ Lf^*` is compatible with them and with the tensor comparisons of the
derived pullbacks of module objects over `𝔽̲_E` and of pro-étale sheaves of `𝔽_E`-modules. -/
theorem exists_comparisonCompatible_residueFieldDerivedUpperStarIso :
    ∃ (m_X : (Functor.postcompose₂.obj (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).obj
        (curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).obj
        (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).obj (curriedTensor _))
      (m_Y : (Functor.postcompose₂.obj (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory).obj
        (curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory).obj
        (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory).obj (curriedTensor _)),
      Adjunction.ComparisonCompatible (residueFieldDerivedUpperStarIso ℓ E f).symm
        (leftDerivedUpperStarTensor
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
        (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)
        m_X m_Y := by
  refine ⟨Functor.TensorIso.ofIso
      (asIso ((residueFieldModuleSheaf X ℓ E).leftDerivedTensorComparisonOfNatTrans
        (residueFieldModuleSheafTensorIso X ℓ E).hom))
      (residueFieldModuleSheaf X ℓ E).leftDerivedFunctorIsoMapDerivedCategory,
    Functor.TensorIso.ofIso
      (asIso ((residueFieldModuleSheaf Y ℓ E).leftDerivedTensorComparisonOfNatTrans
        (residueFieldModuleSheafTensorIso Y ℓ E).hom))
      (residueFieldModuleSheaf Y ℓ E).leftDerivedFunctorIsoMapDerivedCategory, ?_⟩
  refine comparisonCompatible_of_eq (residueFieldDerivedUpperStarIso_symm_eq ℓ E f)
    ((CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f).trans
      (Functor.leftDerivedTensorComparisonOfNatTrans_δNatTrans _).symm)
    ((ProEtale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f).trans
      (Functor.leftDerivedTensorComparisonOfNatTrans_δNatTrans _).symm) ?_
  have h := Functor.comparisonCompatible_leftDerivedFunctorCompNatIso_of_tensorComparison
    (f)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧
    (Functor.OplaxMonoidal.δNatTrans _)
    (residueFieldModuleSheaf X ℓ E) (residueFieldModuleSheafTensorIso X ℓ E).hom
    (residueFieldModuleSheaf Y ℓ E) (residueFieldModuleSheafTensorIso Y ℓ E).hom
    (f)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]
    (Functor.OplaxMonoidal.δNatTrans _)
    (residueFieldModuleSheafUpperStarIso ℓ E f).symm
    (tensorCompatible_residueFieldModuleSheafUpperStarIso ℓ E f).inv
  exact h.ofIso (residueFieldModuleSheaf X ℓ E).leftDerivedFunctorIsoMapDerivedCategory
    (residueFieldModuleSheaf Y ℓ E).leftDerivedFunctorIsoMapDerivedCategory

end AlgebraicGeometry.ProEtale
