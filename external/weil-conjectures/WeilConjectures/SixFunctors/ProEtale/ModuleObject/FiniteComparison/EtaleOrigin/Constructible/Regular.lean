/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteLocallyConstantCokernel
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# The free module objects with finite coefficients are constant sheaves

Let `T` be a finite discrete commutative ring and `X` a scheme. Under the equivalence
`ProEtale.finiteCoefficientModEquivalence` between module objects over `Λ_X = p_X^* T̲` and
sheaves of `T`-modules on `X_proét`, the regular module object `Λ_X` corresponds to the constant
sheaf `T`, since both corepresent the global sections
(`ProEtale.finiteCoefficientModEquivalenceRegularIso`). Hence the free module object `Λ_X^k`
corresponds to the constant sheaf `T^k`, and a finitely presented module object, the cokernel of
a morphism `Λ_X^m ⟶ Λ_X^n`, corresponds to the cokernel of a morphism of constant sheaves
`T^m ⟶ T^n`, which is locally constant with finite stalks
(`ProEtale.isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj`).

## Main statements

- `ProEtale.finiteCoefficientModEquivalenceRegularIso`: `Λ_X` corresponds to the constant sheaf
  `T`.
- `ProEtale.finiteCoefficientModEquivalenceFiniteFreeIso`: `Λ_X^k` corresponds to the constant
  sheaf `T^k`.
- `ProEtale.isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj`: a finitely presented
  module object over `Λ_X` corresponds to a sheaf of `T`-modules which is locally constant with
  finite stalks.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] (X : Scheme.{u})

/-- Morphisms of `Λ_X`-modules out of `Λ_X` are the global sections. -/
noncomputable def regularHomEquivSections
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) X) ⟶ M) ≃
      M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  (Mod.regularHomAddEquiv M).toEquiv.trans
    (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId X) M.X).toEquiv

/-- Morphisms out of the module object corresponding to the constant sheaf `T` are the global
sections. -/
noncomputable def inverseConstantHomEquivSections
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    ((finiteCoefficientModEquivalence X T).inverse.obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T))) ⟶ M) ≃
      M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  ((finiteCoefficientModEquivalence X T).symm.toAdjunction.homEquiv _ _).trans <|
    ((constantSheafAdj _ _ (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _).trans <|
      ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf _ ℕ _).toEquiv

omit [DiscreteTopology T] [Finite T] in
/-- `regularHomEquivSections` is natural in the target module object. -/
lemma regularHomEquivSections_comp
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)}
    (x : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) X) ⟶ M) (f : M ⟶ N) :
    regularHomEquivSections T X N (x ≫ f) =
      f.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (regularHomEquivSections T X M x) := by
  rfl

/-- `inverseConstantHomEquivSections` is natural in the target module object. -/
lemma inverseConstantHomEquivSections_comp
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)}
    (x : (finiteCoefficientModEquivalence X T).inverse.obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T))) ⟶ M) (f : M ⟶ N) :
    inverseConstantHomEquivSections T X N (x ≫ f) =
      f.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (inverseConstantHomEquivSections T X M x) := by
  rfl

/-- The regular module object `Λ_X` corresponds, under `finiteCoefficientModEquivalence`, to
the module object of the constant sheaf `T`: both corepresent the global sections. -/
noncomputable def regularIsoInverseConstant :
    Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) X) ≅
      (finiteCoefficientModEquivalence X T).inverse.obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T))) where
  hom := (regularHomEquivSections T X _).symm (inverseConstantHomEquivSections T X _ (𝟙 _))
  inv := (inverseConstantHomEquivSections T X _).symm (regularHomEquivSections T X _ (𝟙 _))
  hom_inv_id := by
    refine (regularHomEquivSections T X _).injective ?_
    rw [regularHomEquivSections_comp, Equiv.apply_symm_apply,
      ← inverseConstantHomEquivSections_comp,
      Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    refine (inverseConstantHomEquivSections T X _).injective ?_
    rw [inverseConstantHomEquivSections_comp, Equiv.apply_symm_apply,
      ← regularHomEquivSections_comp,
      Category.id_comp, Equiv.apply_symm_apply]

/-- **The regular module object corresponds to the constant sheaf `T`**: under
`finiteCoefficientModEquivalence`, `Λ_X` is the constant sheaf of `T`-modules `T`. -/
noncomputable def finiteCoefficientModEquivalenceRegularIso :
    (finiteCoefficientModEquivalence X T).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) X)) ≅
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
        (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)) :=
  (finiteCoefficientModEquivalence X T).functor.mapIso (regularIsoInverseConstant T X) ≪≫
    (finiteCoefficientModEquivalence X T).counitIso.app _

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Under `finiteCoefficientModEquivalence`, the free module object `Λ_X^k` is the constant sheaf
of `T`-modules `T^k`. -/
noncomputable def finiteCoefficientModEquivalenceFiniteFreeIso (k : ℕ) :
    (finiteCoefficientModEquivalence X T).functor.obj
        (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) X) k) ≅
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
        (ModuleCat.of (ULift.{u + 1} T) (Fin k → ULift.{u + 1} T)) :=
  (finiteCoefficientModEquivalence X T).functor.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ finiteCoefficientModEquivalenceRegularIso T X) ≪≫
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).mapBiproduct
      _).symm ≪≫
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).mapIso
      (ModuleCat.biproductIsoPi _)

/-- A finitely presented module object over `Λ_X` corresponds, under
`finiteCoefficientModEquivalence`, to a sheaf of `T`-modules which is locally constant with
finitely generated stalks: it is the cokernel of a morphism of constant sheaves `T^m ⟶ T^n`. -/
theorem isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)}
    (hN : Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) X) N) :
    IsFiniteLocallyConstant (ULift.{u + 1} T)
      ((finiteCoefficientModEquivalence X T).functor.obj N) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hN
  let F := (finiteCoefficientModEquivalence X T).functor
  exact isFiniteLocallyConstant_of_iso
    ((cokernel.mapIso _ _ (finiteCoefficientModEquivalenceFiniteFreeIso T X m)
      (finiteCoefficientModEquivalenceFiniteFreeIso T X n) (by simp)).symm ≪≫
      (PreservesCokernel.iso F f).symm ≪≫ F.mapIso e.symm)
    (isFiniteLocallyConstant_cokernel ((finiteCoefficientModEquivalenceFiniteFreeIso T X m).inv ≫
      F.map f ≫ (finiteCoefficientModEquivalenceFiniteFreeIso T X n).hom))

end AlgebraicGeometry.ProEtale
