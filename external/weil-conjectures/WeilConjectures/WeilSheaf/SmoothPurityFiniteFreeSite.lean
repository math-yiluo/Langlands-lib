/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreePullback

/-! # Factoring the finite free-module comparison through the pro-étale site -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

lemma purity_leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

/-- Composition of two comparisons of left adjoints, expressed through their
right-adjoint comparisons. -/
lemma purity_conjugate_comp_factor
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {RF : B ⥤ A} (f : F ⊣ RF)
    {G : B ⥤ C} {RG : C ⥤ B} (g : G ⊣ RG)
    {H : C ⥤ D} {RH : D ⥤ C} (h : H ⊣ RH)
    {I : B ⥤ D} {RI : D ⥤ B} (i : I ⊣ RI)
    {J : A ⥤ D} {RJ : D ⥤ A} (j : J ⊣ RJ)
    (a : RI ≅ RH ⋙ RG) (b : RJ ≅ RI ⋙ RF) :
    (conjugateIsoEquiv j ((f.comp g).comp h)).symm
        (b ≪≫ Functor.isoWhiskerRight a RF ≪≫ Functor.associator _ _ _) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft F ((conjugateIsoEquiv i (g.comp h)).symm a) ≪≫
        (conjugateIsoEquiv j (f.comp i)).symm b := by
  apply (conjugateIsoEquiv j ((f.comp g).comp h)).injective
  rw [Equiv.apply_symm_apply,
    conjugateIsoEquiv_trans _ (f.comp (g.comp h)),
    conjugateIsoEquiv_trans _ (f.comp i),
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Iso.trans_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] (X : Scheme.{u})

/-- Free sheaves commute with the comparison-site inverse image. -/
noncomputable def purityComparisonFreeSheafIso :
    ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T X ≅
      Etale.extendScalars (ULift.{u + 1} T) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  (conjugateIsoEquiv
    ((Etale.extendScalarsAdjunction (ULift.{u + 1} T) X).comp (comparisonAdjunction _ X))
    ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X))).symm
    (Iso.refl _)

/-- The existing finite-root free-module comparison factors through the ordinary
free sheaf and the comparison-site free-sheaf isomorphism. -/
lemma purity_comparisonUpperStarFreeIso_factor :
    comparisonUpperStarFreeIso T X =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ν^*(X)[Ab.{u + 1}] (purityFiniteCoefficientFreeIso T X) ≪≫
        purityComparisonFreeSheafIso T X := by
  unfold comparisonUpperStarFreeIso
  rw [CategoryTheory.purity_leftAdjointUniq_ofNatIsoRight]
  have h := purity_conjugate_comp_factor (comparisonAdjunction Ab.{u + 1} X)
    (Mod.freeForgetAdjunction (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (finiteCoefficientModEquivalence X T).toAdjunction
    (purityFiniteFreeSheafAdjunction T X)
    ((Etale.extendScalarsAdjunction (ULift.{u + 1} T) X).comp (comparisonAdjunction _ X))
    (finiteCoefficientModEquivalenceInverseCompForgetIso T X).symm (Iso.refl _)
  refine Eq.trans ?_ h
  congr 1

/-- Component form of the factorization, without associator identities. -/
lemma purity_comparisonUpperStarFreeIso_hom_app
    (M : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (comparisonUpperStarFreeIso T X).hom.app M =
      (purityFiniteCoefficientFreeIso T X).hom.app (ν^*(X)[Ab.{u + 1}].obj M) ≫
        (purityComparisonFreeSheafIso T X).hom.app M := by
  rw [purity_comparisonUpperStarFreeIso_factor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [Category.id_comp]

end AlgebraicGeometry.ProEtale
