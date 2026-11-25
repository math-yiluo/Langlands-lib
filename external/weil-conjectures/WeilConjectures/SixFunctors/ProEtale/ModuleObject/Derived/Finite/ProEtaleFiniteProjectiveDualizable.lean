/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Dualizability of finite locally projective coefficient modules

Source: blueprint main-20261015, stratum Hom lemma, proof step 3.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma isDualizable_finite_power
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e

private theorem finiteFree_retract_isDualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (r : ℕ)
    (L : supportModules Λ S) (ι : L ⟶ Mod.finiteFree (condensedRingObj Λ S) r)
    (π : Mod.finiteFree (condensedRingObj Λ S) r ⟶ L) (h : ι ≫ π = 𝟙 _) :
    IsDualizable L := by
  apply IsDualizable.of_retract ⟨ι, π, h⟩
  exact (isDualizable_finite_power _ isDualizable_unit r).of_iso
    (biproduct.isoProduct (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ S))).symm

end AlgebraicGeometry.ProEtale.CondensedRing
