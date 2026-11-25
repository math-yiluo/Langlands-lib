/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EllGroupMonodromyDevissage
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorThickOrigin
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorTriangulated
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantThickOrigin

/-!

# The thick origin with coefficients in a finite free module

Let `X = 𝔸¹_k` and `Z = V(x^m)` with `m ≥ 1`. The thick origin (blueprint `lemma-case-z-v-x-m`)
asserts that the defect `C_{X,Z}(M_X)` of the constant sheaf of a finite `A`-module `M` vanishes.
The library proves it for `M = A`, i.e. for the unit, both for a finite coefficient ring `T` and
for `ℚ̄_ℓ`. Since the complexes with vanishing defect form a triangulated subcategory
(`ProEtale.CondensedRing.isTriangulated_vanishingDefect`), they are closed under finite biproducts,
and the vanishing extends to finite direct sums of copies of the unit, that is to finite free
modules.

For a finite coefficient ring `T`, the constant complex `M_Y` of a `T`-module `M` on a scheme `Y`
is the constant étale sheaf of `M` placed in degree `0`, pulled back to the pro-étale site and
transported to module objects over `C(-, T)` by the inverse of the derived comparison
`ProEtale.finiteCoefficientDerivedEquivalence` (`ProEtale.finiteCoefficientConstantFunctor`). Its
value at `M = T` is the unit (`ProEtale.finiteCoefficientConstantFunctorObjSelfIso`).

## Main results

- `ProEtale.CondensedRing.isZero_specializationDefect_biproduct`: the defect of a finite biproduct
  vanishes if it vanishes at each summand.
- `isZero_specializationDefect_polyAffineThickOrigin_biproduct_unit_padicAlgCl`,
  `isZero_specializationDefect_polyAffineThickOrigin_biproduct_unit_finiteCoefficient`:
  the thick origin for finite direct sums of copies of the unit.
- `isZero_specializationDefect_polyAffineThickOrigin_finiteCoefficientConstant`:
  the thick origin for the constant complex `M_X` of a finite free `T`-module `M`, hence of every
  finite `T`-module when `T` is a field.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The constant complex `M_Y` of a module `M` over a finite coefficient ring `T` on a scheme `Y`:
the constant étale sheaf of `M` placed in degree `0`, pulled back to the pro-étale site and
transported to module objects over `C(-, T)` by the inverse of the derived comparison. -/
noncomputable def finiteCoefficientConstantFunctor (Y : Scheme.{u}) :
    ModuleCat.{u + 1} (ULift.{u + 1} T) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) Y)) :=
  constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ⋙
      (finiteCoefficientDerivedEquivalence Y T).inverse

instance (Y : Scheme.{u}) : (finiteCoefficientConstantFunctor T Y).Additive := by
  have : (finiteCoefficientDerivedEquivalence Y T).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold finiteCoefficientConstantFunctor
  infer_instance

/-- The constant complex of `T` itself is the unit. -/
noncomputable def finiteCoefficientConstantFunctorObjSelfIso (Y : Scheme.{u}) :
    (finiteCoefficientConstantFunctor T Y).obj
      (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)) ≅ 𝟙_ _ :=
  (finiteCoefficientDerivedEquivalence Y T).inverse.mapIso
      (((ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (comparisonUpperStarUnitIso _ Y) ≪≫
        DerivedCategory.singleFunctorObjUnitIso _) ≪≫
    (finiteCoefficientDerivedEquivalence Y T).inverse.mapIso
      (finiteCoefficientDerivedEquivalenceUnitIso Y T).symm ≪≫
    ((finiteCoefficientDerivedEquivalence Y T).unitIso.app _).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

instance : (vanishingDefect X I k' Λ).IsClosedUnderIsomorphisms := by
  rw [vanishingDefect_eq_isoLocus]
  infer_instance

/-- The defect of a finite biproduct vanishes if it vanishes at each summand: the complexes with
vanishing defect form a triangulated subcategory, which is closed under finite products. -/
theorem isZero_specializationDefect_biproduct {J : Type*} [Finite J]
    (f : J → DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) [HasBiproduct f]
    (h : ∀ j, IsZero (specializationDefect X I k' Λ (f j))) :
    IsZero (specializationDefect X I k' Λ (⨁ f)) :=
  (vanishingDefect X I k' Λ).prop_of_iso (biproduct.isoProduct f).symm
    ((vanishingDefect X I k' Λ).prop_product h)

end General

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The thick origin for a finite free `ℚ̄_ℓ`-module** (blueprint `lemma-case-z-v-x-m`, for
`M = ℚ̄_ℓ^J` with `J` finite): for `m ≥ 1`, the defect `C_{𝔸¹, V(x^m)}(⨁_J ℚ̄_ℓ)` vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_biproduct_unit_padicAlgCl
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {m : ℕ} (hm : 0 < m)
    (J : Type*) [Finite J] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.padicAlgClRingObj ℓ) (⨁ fun _ : J ↦ 𝟙_ _)) :=
  isZero_specializationDefect_biproduct _ _ k' _ _ fun _ ↦
    isZero_specializationDefect_polyAffineThickOrigin_unit_padicAlgCl k' hm

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The thick origin for a finite free module, with finite coefficients** (blueprint
`lemma-case-z-v-x-m`, for `M = T^J` with `J` finite and `T` a finite ring killed by a prime
`ℓ ≠ char k'`): for `m ≥ 1`, the defect `C_{𝔸¹, V(x^m)}(⨁_J T̲)` vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_biproduct_unit_finiteCoefficient
    (hT : (ℓ : T) = 0) {m : ℕ} (hm : 0 < m) (J : Type*) [Finite J] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T) (⨁ fun _ : J ↦ 𝟙_ _)) :=
  isZero_specializationDefect_biproduct _ _ k' _ _ fun _ ↦
    isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient T k' hT hm

/-- **The thick origin for the constant complex of a finite free module, with finite
coefficients** (blueprint `lemma-case-z-v-x-m`, for `M` finite free over a finite ring `T` killed
by a prime `ℓ ≠ char k'`; every finite `T`-module is free when `T` is a field): for `m ≥ 1`, the
defect `C_{𝔸¹, V(x^m)}(M_X)` of the constant complex `M_X` vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_finiteCoefficientConstant
    (hT : (ℓ : T) = 0) {m : ℕ} (hm : 0 < m) (M : ModuleCat.{u + 1} (ULift.{u + 1} T))
    [Module.Free (ULift.{u + 1} T) M] [Module.Finite (ULift.{u + 1} T) M] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T)
      ((finiteCoefficientConstantFunctor T (polyAffine k 1).left).obj M)) := by
  let G := finiteCoefficientConstantFunctor T (polyAffine k 1).left
  let R := ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)
  let n := Fintype.card (Module.Free.ChooseBasisIndex (ULift.{u + 1} T) M)
  let b := (Module.Free.chooseBasis (ULift.{u + 1} T) M).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex (ULift.{u + 1} T) M))
  have e : M ≅ ⨁ fun _ : Fin n ↦ R :=
    b.equivFun.toModuleIso ≪≫ (ModuleCat.biproductIsoPi fun _ : Fin n ↦ R).symm
  have hR : IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T) (G.obj R)) :=
    (vanishingDefect (polyAffine k 1) (polyAffineThickOrigin k m) k' _).prop_of_iso
      (finiteCoefficientConstantFunctorObjSelfIso T (polyAffine k 1).left).symm
      (isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient T k' hT hm)
  exact (vanishingDefect (polyAffine k 1) (polyAffineThickOrigin k m) k' _).prop_of_iso
    ((G.mapBiproduct _).symm ≪≫ G.mapIso e.symm)
    (isZero_specializationDefect_biproduct _ _ k' _ _ fun _ ↦ hR)

end AlgebraicGeometry.ProEtale.CondensedRing
