/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import all WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseComparisonModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseTransport

/-! # Lisse finite-projective étale sheaves have local scalar models

Source: blueprint scalar-six-ctf (1), finite-projective local models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- Realization of a lisse finite-projective étale sheaf is locally perfect over the
specified condensed coefficient ring.

Source: blueprint scalar-six-ctf (1), finite projective local models; Stacks 00NX, 099Y.

Proof: Choose an étale trivializing cover for L. On a nonempty member a geometric stalk
identifies the constant module with a finite projective module; replace empty members
by zero models. Regard the cover as a pro-étale cover. Each finite projective module
splits a finite free surjection. The sectionwise constant-ring equivalence identifies
finite free modules with finite sums of the scalar regular module and lifts the splitting
by full faithfulness. Restriction along e identifies the regular scalar modules and
carries this splitting to the Λ scalar category. Put the resulting scalar module in
degree zero, with bounds [0,0] and rank-zero splittings in every other degree. The
constant-model and coefficient-pullback comparisons identify its scalar realization with
the pullback of the realized L. Exact functors commute with the single-complex functor,
so these are the isomorphisms required by IsLocallyPerfectScalarModel. The same proof
handles the zero ring, empty covers and rank zero. -/
theorem isLocallyPerfectScalarModel_finiteScalarRealization (S : Scheme.{u}) [IsNoetherian S]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hL : FlatModelEtaleLisseProjective (ULift.{u + 1} A) L) :
    IsLocallyPerfectScalarModel Λ.X S
      ((finiteScalarRealization A e eR S).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := finiteEtaleLisseScalarComparisonData A S L hL
  refine ⟨𝒰, fun j ↦ ?_⟩
  obtain ⟨P, hfin, hproj, ⟨i⟩⟩ := h𝒰 j
  obtain ⟨Q, n, ⟨r⟩, ⟨q⟩⟩ :=
    finiteProjectiveConstantScalarModel A e eR (𝒰.X j) P hfin hproj
  obtain ⟨d⟩ := finiteScalarRealizationConstantChart A e eR S (𝒰.X j) (𝒰.f j) L P i
  let C := (HomologicalComplex.single _ (.up ℤ) 0).obj Q
  refine ⟨C, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · subst k
      exact ⟨n, ⟨(Retract.ofIso (HomologicalComplex.singleObjXSelf _ 0 Q)).trans r⟩⟩
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Q k hk
      have hzero : IsZero (Mod.finiteFree (scalarRingObj Λ.X) 0) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      exact ⟨0, ⟨Retract.ofIso (hz.iso hzero)⟩⟩
  · let F := finiteConstantScalarExtension Λ.X (𝒰.X j)
    let : F.Additive := AlgebraicGeometry.ProEtale.scalarExtension_additive Λ.X (𝒰.X j)
    exact ⟨d ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso q ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj Q) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app Q).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
