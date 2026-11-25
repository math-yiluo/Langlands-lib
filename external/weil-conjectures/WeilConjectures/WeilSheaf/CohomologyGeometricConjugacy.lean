/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence

/-!
# Cohomology and conjugate geometric Frobenius automorphisms

An isomorphism `e : Ȳ ≅ X̄` of geometric fibers which conjugates the geometric Frobenius of `Ȳ` to
the `r`-th power of that of `X̄` makes the induced equivalence
`Hⁱ(Y ⊗ k̄', ℚ̄_ℓ) ≃ Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` intertwine the Frobenius of the source with the `r`-th power
of the Frobenius of the target
(`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso_map_frobenius`). This is
the transport-of-structure part of the base-change clause of `theorem-poincare-duality-frobenius`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.WeilSheaf

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- Under `Hⁱ(X ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ RΓ(X̄, ℚ̄_ℓ)`, the `n`-th power of the Frobenius is induced by the
transport of `RΓ(X̄, ℚ̄_ℓ)` along the inverse of the `n`-th power of the geometric Frobenius. -/
lemma cohomologyCarrierIso_inv_derivedGlobalSectionsUnitIso_pow (i : ℤ) (n : ℕ)
    (z : (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).obj
      (ProEtale.derivedGlobalSectionsUnit l (X ↘ Spec (.of k)).geometricFiber)) :
    (cohomologyCarrierIso k l X i).inv.hom (((DerivedCategory.homologyFunctor _ i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).asIso.symm).hom).hom z) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ n)
        ((cohomologyCarrierIso k l X i).inv.hom z) := by
  have hF : (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
        (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm).hom ≫
        (cohomologyCarrierIso k l X i).inv =
      (cohomologyCarrierIso k l X i).inv ≫
        (IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
          (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)).hom.app
          ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X)) := by
    rw [Iso.comp_inv_eq, Category.assoc, cohomologyCarrierIso_hom_frobenius,
      Iso.inv_hom_id_assoc]
  have hF' : ∀ w, (cohomologyCarrierIso k l X i).inv.hom
      (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
        (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm).hom).hom w) =
      ((adicConstant k l X).cohomology i).frobenius
        ((cohomologyCarrierIso k l X i).inv.hom w) := by
    intro w
    rw [cohomology_adicConstant_frobenius]
    exact congrArg (fun f ↦ f.hom w) hF
  induction n generalizing z with
  | zero =>
    rw [pow_zero, pow_zero, Aut.one_asIso,
      Iso.refl_symm, ProEtale.derivedGlobalSectionsUnitIso_refl, Iso.refl_hom,
      CategoryTheory.Functor.map_id]
    rfl
  | succ n ih =>
    have hσ : ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ (n + 1)).asIso.symm =
        ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).asIso.symm ≪≫
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm := by
      rw [pow_succ, Aut.mul_asIso, Iso.trans_symm]
    have hD : ProEtale.derivedGlobalSectionsUnitIso l
        ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ (n + 1)).asIso.symm =
        ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).asIso.symm ≪≫
        ProEtale.derivedGlobalSectionsUnitIso l
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm := by
      rw [hσ, ProEtale.derivedGlobalSectionsUnitIso_trans]
    have hmor : (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ (n + 1)).asIso.symm).hom =
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).asIso.symm).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm).hom := by
      rw [hD, Iso.trans_hom, Functor.map_comp]
    calc _ = (cohomologyCarrierIso k l X i).inv.hom
          (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
            (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.symm).hom).hom
          (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
            ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).asIso.symm).hom).hom z)) :=
          congrArg (fun f ↦ (cohomologyCarrierIso k l X i).inv.hom (f.hom z)) hmor
      _ = ((adicConstant k l X).cohomology i).frobenius
          ((cohomologyCarrierIso k l X i).inv.hom
            (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
              ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).asIso.symm).hom).hom z)) := hF' _
      _ = ((adicConstant k l X).cohomology i).frobenius
          ((((adicConstant k l X).cohomology i).frobeniusEnd ^ n)
            ((cohomologyCarrierIso k l X i).inv.hom z)) :=
          congrArg (fun w : ((adicConstant k l X).cohomology i).carrier ↦
            ((adicConstant k l X).cohomology i).frobenius w) (ih z)
      _ = (((adicConstant k l X).cohomology i).frobeniusEnd *
            ((adicConstant k l X).cohomology i).frobeniusEnd ^ n)
            ((cohomologyCarrierIso k l X i).inv.hom z) :=
          rfl
      _ = _ := congrArg
          (fun f : Module.End (PadicAlgCl l) ((adicConstant k l X).cohomology i).carrier ↦
            f ((cohomologyCarrierIso k l X i).inv.hom z))
            (pow_succ' ((adicConstant k l X).cohomology i).frobeniusEnd n).symm

/-- An isomorphism of geometric fibers conjugating one geometric Frobenius to a power of the other
makes the cohomology equivalence
`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso` intertwine those
operators. This is an ingredient of the base-change clause of `theorem-poincare-duality-frobenius`,
with the transport convention of `definition-frobenius-operator--1`.

Proof: under the identification of the carriers with `Hⁱ RΓ(-, ℚ̄_ℓ)`, the Frobenius is the
transport along the inverse of the geometric Frobenius
(`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso_hom_frobenius`), and the equivalence is the
transport along `e`. Transport is compatible with composition
(`AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso_trans`), and `he` says
`Fr_Y⁻¹ ≫ e = e ≫ Fr_X⁻ʳ`. -/
theorem cohomologyLinearEquivOfGeometricFiberIso_map_frobenius
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (r : ℕ) (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber)
    (he : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.asIso.hom ≫ e.hom =
      e.hom ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).asIso.hom) (i : ℤ)
    (x : ((adicConstant k' l Y).cohomology i).carrier) :
    cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i
        (((adicConstant k' l Y).cohomology i).frobenius x) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ r)
        (cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i x) := by
  have he' : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.asIso.symm ≪≫ e =
      e ≪≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).asIso.symm := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [Iso.inv_comp_eq, ← Category.assoc]
    erw [he]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hD : (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          (Y ↘ Spec (.of k')).geometricGaloisFrobenius.asIso.symm).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l e).hom =
      (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l e).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).asIso.symm).hom := by
    have := congrArg (fun φ ↦ (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).map
      (ProEtale.derivedGlobalSectionsUnitIso l φ).hom) he'
    simpa only [ProEtale.derivedGlobalSectionsUnitIso_trans, Iso.trans_hom,
      Functor.map_comp] using this
  have hY : ∀ y, (cohomologyCarrierIso k' l Y i).hom.hom
      (((adicConstant k' l Y).cohomology i).frobenius y) =
      ((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
        (Y ↘ Spec (.of k')).geometricGaloisFrobenius.asIso.symm).hom).hom
        ((cohomologyCarrierIso k' l Y i).hom.hom y) := fun y ↦ by
    rw [cohomology_adicConstant_frobenius]
    exact congrArg (fun f ↦ f.hom y) (cohomologyCarrierIso_hom_frobenius k' l Y i)
  have hT : ∀ y, cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i y =
      (cohomologyCarrierIso k l X i).inv.hom
        (((DerivedCategory.homologyFunctor _ i).map
          (ProEtale.derivedGlobalSectionsUnitIso l e).hom).hom
            ((cohomologyCarrierIso k' l Y i).hom.hom y)) := fun _ ↦ rfl
  rw [hT, hT, hY, ← cohomologyCarrierIso_inv_derivedGlobalSectionsUnitIso_pow]
  exact congrArg (fun f ↦ (cohomologyCarrierIso k l X i).inv.hom
    (f.hom ((cohomologyCarrierIso k' l Y i).hom.hom x))) hD

end AlgebraicGeometry.WeilSheaf
