/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoComplex

/-!
# A criterion for the derived (Push) comparison to be invertible

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and
`f : X ⟶ Y` a morphism of schemes. We show that the comparison
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom a f : T^Y Rf_* K ⟶ Rf_* T^X K` is
an isomorphism at `K` as soon as `K` is represented by a bounded below complex `J` such that

* the terms `J^k` are `f_*`-acyclic, and so are the terms `Λ' ⊗_Λ J^k`;
* the underived (Push) comparisons `Λ' ⊗ f_* J^k ⟶ f_*(Λ' ⊗ J^k)` are isomorphisms;
* the derived extensions of scalars are computed by `J` and `f_* J`, i.e. the counits
  `T(J) ⟶ Λ' ⊗ J` and `T(f_* J) ⟶ Λ' ⊗ f_* J` are isomorphisms

(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_isStrictlyGE`).
This follows from the computation of the comparison on complexes
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom_app_Qh_fac`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

-- unifying objects of the derived categories of module objects is slow
/-- **A criterion for the derived (Push) comparison to be invertible**: if `K` is represented by
a bounded below complex `J` of `f_*`-acyclic objects, whose extensions of scalars are
`f_*`-acyclic, on which the underived (Push) comparison is invertible and on which (as well as on
`f_* J`) the derived extension of scalars is computed levelwise, then
`derivedUpperStarExtendScalarsPushHom a f` is an isomorphism at `K`. -/
theorem isIso_derivedUpperStarExtendScalarsPushHom_app_of_isStrictlyGE
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (J : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (e : K ≅ Q.obj J) (n : ℤ) [J.IsStrictlyGE n]
    (hJ : ∀ k, ((f)_*⟦Λ⟧).rightAcyclic (J.X k))
    (hJ' : ∀ k, ((f)_*⟦Λ'⟧).rightAcyclic ((Mod.extendScalars (coefficientMap a X)).obj (J.X k)))
    (hpush : ∀ k, IsIso ((pushHom a f).app (J.X k)))
    (hX : IsIso ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj J)))
    (hY : IsIso ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app
      ((((f)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj J)))) :
    IsIso ((derivedUpperStarExtendScalarsPushHom a f).app K) := by
  rw [NatTrans.isIso_app_iff_of_iso _ (e ≪≫ ((quotientCompQhIso _).app J).symm)]
  have h := derivedUpperStarExtendScalarsPushHom_app_Qh_fac a f J
  have : ∀ k, IsIso (((NatTrans.mapHomologicalComplex (pushHom a f) (ComplexShape.up ℤ)).app
      J).f k) := hpush
  have : IsIso ((NatTrans.mapHomologicalComplex (pushHom a f) (ComplexShape.up ℤ)).app J) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((NatTrans.mapHomotopyCategory (pushHom a f) (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient _ _).obj J)) :=
    Functor.map_isIso (HomotopyCategory.quotient _ _)
      ((NatTrans.mapHomologicalComplex (pushHom a f) (ComplexShape.up ℤ)).app J)
  have : IsIso (((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj J)) :=
    Functor.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE _ J n hJ
  have : CochainComplex.IsStrictlyGE ((Mod.extendScalars
      (coefficientMap a X)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj J) n :=
    (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi ↦
      show IsZero ((Mod.extendScalars _).obj (J.X i)) from
        Functor.map_isZero _ (J.isZero_of_isStrictlyGE n i hi)
  have : IsIso (((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app
      (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ _).obj J))) :=
    Functor.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE _ ((Mod.extendScalars
      (coefficientMap a X)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj J) n hJ'
  have := IsIso.of_isIso_fac_left h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this

end AlgebraicGeometry.ProEtale.CondensedRing
