/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals

/-! # Changing the trace of a diagonal kernel

Projection naturality describes the kernel counit after changing its trace.
A named datum constructor keeps this comparison independent of the size of the original datum.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 100000] sheafIsAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] SfDiagonalKernel.unit SfDiagonalKernel.counit
  derivedTensor singleFunctorObjUnitIso
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

private theorem counit_map_generic
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P : D ⥤ C) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (B : C) (V K : D) (a : B ≅ B)
    (p : (S.obj (F.obj B)).obj K ≅ F.obj ((T.obj B).obj (P.obj K)))
    (trace trace' : F.obj B ⟶ V) (l : (S.obj V).obj K ⟶ K)
    (hp : (S.map (F.map a.hom)).app K ≫ p.hom =
      p.hom ≫ F.map ((T.map a.hom).app (P.obj K)))
    (ht : trace' = F.map a.hom ≫ trace) :
    F.map ((T.map a.hom).app (P.obj K)) ≫
        (p.inv ≫ (S.map trace).app K ≫ l) =
      p.inv ≫ (S.map trace').app K ≫ l := by
  have hi : F.map ((T.map a.hom).app (P.obj K)) ≫ p.inv =
      p.inv ≫ (S.map (F.map a.hom)).app K := by
    apply (cancel_epi p.hom).1
    rw [← Category.assoc, ← hp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [ht, S.map_comp]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [← Category.assoc, hi]
  simp only [Category.assoc]

private theorem projection_counit_map
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
    {FC : C → C → Type (u + 1)} {CC : C → Type (u + 1)}
    [∀ (P Q : C), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} C FC]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [HasCompactification q]
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (p : (derivedTensor C Y).obj ((rightDerivedLowerShriek C q).obj B) ≅
      ((upperStar C q).leftDerivedFunctor) ⋙ (derivedTensor C X).obj B ⋙
        rightDerivedLowerShriek C q)
    (hp : p.hom = (projectionMap C q).app B) (a : B ≅ B)
    (τ τ' : (rightDerivedLowerShriek C q).obj B ⟶ derivedTensorUnit C Y)
    (ht : τ' = (rightDerivedLowerShriek C q).map a.hom ≫ τ)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (rightDerivedLowerShriek C q).map
        (((derivedTensor C X).map a.hom).app (((upperStar C q).leftDerivedFunctor).obj K)) ≫
        (p.inv.app K ≫ ((derivedTensor C Y).map τ).app K ≫
          (derivedTensorUnitLeftUnitor C Y).hom.app K) =
      p.inv.app K ≫ ((derivedTensor C Y).map τ').app K ≫
        (derivedTensorUnitLeftUnitor C Y).hom.app K := by
  have hn := NatTrans.congr_app ((projectionMap C q).naturality a.hom) K
  rw [← hp] at hn
  have hh := counit_map_generic (rightDerivedLowerShriek C q) (((upperStar C q).leftDerivedFunctor))
    (derivedTensor C X) (derivedTensor C Y) B (derivedTensorUnit C Y) K a (p.app K)
    τ τ' ((derivedTensorUnitLeftUnitor C Y).hom.app K) hn ht
  simpa only [NatTrans.comp_app, Iso.app_inv] using hh

private theorem kernelCounit_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    {B : DerivedCategoryModule A X} (D : TraceDiagonalDatum A q B)
    (K : DerivedCategoryModule A Y) :
    (SfDiagonalKernel.counit A D).app K =
      (projectionIso A q B).inv.app K ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map D.trace).app K ≫
        (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app K := by
  rw [SfDiagonalKernel.counit]
  rfl

private theorem kernelCounit_map
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (D D' : TraceDiagonalDatum A q B)
    (a : B ≅ B)
    (ht : D'.trace = (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫
      D.trace) (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map a.hom).app
          ((CoordinateTrace.pull A q).obj K)) ≫ (SfDiagonalKernel.counit A D).app K =
      (SfDiagonalKernel.counit A D').app K := by
  rw [kernelCounit_app, kernelCounit_app]
  exact projection_counit_map (ModuleCat.{u + 1} A) q B (projectionIso A q B) rfl a
    D.trace D'.trace ht K

/-- Replace only the trace of the given diagonal datum.
Source: coefficient normalization in the projective-line diagonal argument.
(auxiliary; not a blueprint node). -/
@[irreducible]
noncomputable def kernelDatumWithTrace
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (D : TraceDiagonalDatum A q B)
    (τ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj B ⟶
      derivedTensorUnit (ModuleCat.{u + 1} A) Y) : TraceDiagonalDatum A q B :=
  { trace := τ
    diagonalClass := D.diagonalClass }

/-- Tensoring a coefficient automorphism changes the kernel counit by its action on the trace.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, transport of the kernel counit.
(auxiliary; not a blueprint node).

Proof: the new datum retains the diagonal class and has the specified trace by construction.
Naturality of the projection map in its coefficient moves the image of the automorphism
across the projection isomorphism. Cancel that isomorphism to obtain the equation for its
inverse. Functoriality of tensoring then combines the automorphism with the old trace.
The final left-unitor factor is the same in both composites. -/
theorem kernelCounit_traceChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (D : TraceDiagonalDatum A q B) (a : B ≅ B)
    (τ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj B ⟶
      derivedTensorUnit (ModuleCat.{u + 1} A) Y)
    (hτ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫ D.trace = τ) :
    let D' := kernelDatumWithTrace A q B D τ
    D'.trace = τ ∧ ∀ K : DerivedCategoryModule A Y,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map a.hom).app
            ((CoordinateTrace.pull A q).obj K)) ≫ (SfDiagonalKernel.counit A D).app K =
        (SfDiagonalKernel.counit A D').app K := by
  have htr : (kernelDatumWithTrace A q B D τ).trace = τ := by
    unfold kernelDatumWithTrace
    rfl
  refine ⟨htr, ?_⟩
  intro K
  exact kernelCounit_map A q B D (kernelDatumWithTrace A q B D τ) a
    (htr.trans hτ.symm) K

end AlgebraicGeometry.Etale
