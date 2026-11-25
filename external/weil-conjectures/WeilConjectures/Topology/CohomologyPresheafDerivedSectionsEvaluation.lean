/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleDerivedSections
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Evaluation of the cohomology presheaf

Source: Stacks Project, Cohomology, Tags 0BKJ and 0D60.
(blueprint: lem-pc-cohomology-presheaf-derived-sections-evaluation).
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- Evaluating any descent of the cohomology presheaf computed on functorial
K-injective replacements gives cohomology of the right derived sections functor.
Source: Stacks Project, Cohomology, Tag 0BKJ, proof, and Tag 0D60, proof.
(blueprint: lem-pc-cohomology-presheaf-derived-sections-evaluation).

Proof: Fix an open U. Evaluation at U is exact in abelian-group presheaves,
so it commutes with cohomology. Evaluating the given presentation of P therefore
identifies Q followed by evaluation of P with cohomology of sections of the
functorial K-injective replacement. The quasi-isomorphism from a complex to its
replacement becomes a natural isomorphism under Q. The right-derived-functor
unit on that replacement is an isomorphism, since the replacement is K-injective.
Its naturality identifies this same functor with Q followed by RΓ(U,-) followed
by cohomology. Compose these natural isomorphisms and descend along Q using the
fully faithful precomposition functor for localization. This proves the claimed
natural isomorphism, including compatibility with every derived morphism.
This argument also covers the empty open and every integer cohomological degree. -/
theorem cohomology_presheaf_derivedSections_evaluation
    (X : RingedSpace.{u})
    [HasDerivedCategory.{v} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (q : ℤ)
    (P : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hP : Nonempty (DerivedCategory.Q ⋙ P ≅
      CochainComplex.kInjectiveResolutionFunctor.{u}
          (SheafOfModules.{u} (moduleRings X)) ⋙
        (Functor.mapHomologicalComplex
          (SheafOfModules.toSheaf (moduleRings X) ⋙
            sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (ComplexShape.up ℤ)) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q))
    (U : Opens X) :
    Nonempty (P ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      openModuleDerivedSections X U ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} q) := by
  let C := SheafOfModules.{u} (moduleRings X)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let A := SheafOfModules.toSheaf (moduleRings X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let E := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let F := openModuleSections X U
  obtain ⟨eP⟩ := hP
  have heval : HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q ⋙ E ≅
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q := by
    exact (Functor.isoWhiskerLeft
      (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) q)
      (ShortComplex.homologyFunctorIso E)).symm
  have e₁ : DerivedCategory.Q ⋙ (P ⋙ E) ≅
      I ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q := by
    exact Functor.isoWhiskerRight eP E ≪≫
      Functor.isoWhiskerLeft (I ⋙ A.mapHomologicalComplex (ComplexShape.up ℤ)) heval
  let α : I ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      I ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    Functor.whiskerLeft I
      (Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv ≫
        Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
          DerivedCategory.Qh ≫
        Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
          F.rightDerivedFunctorUnit ≫
        Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom F.rightDerivedFunctor)
  have : IsIso α := by
    have (T : CochainComplex C ℤ) : IsIso (α.app T) := by
      dsimp [α]
      infer_instance
    exact NatIso.isIso_of_isIso_app α
  let γ : DerivedCategory.Q (C := C) ⟶ I ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (CochainComplex.toKInjectiveResolution.{u} C) DerivedCategory.Q
  have : IsIso γ := by
    have (T : CochainComplex C ℤ) : IsIso (γ.app T) := by
      have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} C).app T) :=
        (HomologicalComplex.mem_quasiIso_iff _).mp
          (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C T).2
      change IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u} C).app T))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  have e₂ : DerivedCategory.Q ⋙
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} q) ≅
      I ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (asIso γ) F.rightDerivedFunctor ≪≫ (asIso α).symm)
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q) ≪≫
      Functor.isoWhiskerLeft (I ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} q)
  exact ⟨Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _
    (P ⋙ E) (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} q)
    (e₁ ≪≫ e₂.symm)⟩

end AlgebraicGeometry.RingedSpace
