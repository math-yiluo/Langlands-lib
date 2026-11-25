/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.LinearAlgebra.TensorProduct.Prod
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import WeilConjectures.RingTheory.SymmetricAlgebraSmooth
import WeilConjectures.AlgebraicGeometry.CotangentComplexSymmetricAlgebra

/-! # Differentials of a localized symmetric algebra

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CE, lines 419–440
(blueprint: lem-weil-pbc-localized-symmetric-differentials-split).
-/

@[expose] public section

universe u v w
open scoped TensorProduct

namespace SymmetricAlgebra

/-- On the smooth locus, the differentials of a symmetric algebra split into the conormal
and base differential summands.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CE, lines 419–440;
Algebra, Tags 00S2 and 031K; More on Algebra, Tag 07EV
(blueprint: lem-weil-pbc-localized-symmetric-differentials-split).

Proof: write `S = A_a` and `N = S ⊗[A] M`. Base change and tensor localization identify
`T` with `Sym_S(N)`. Since `N` is finite projective, this symmetric algebra is smooth over
`S`. The cotangent lemma gives `Ω[C/A] ≃ C ⊗[A] M`. Mathlib's Kähler base-change
equivalence for the localization pushout, followed by tensor cancellation, identifies the
relative differentials `Ω[T/S]` with `T ⊗[S] N`.
The Jacobi–Zariski sequence for `R → S → T` is therefore short exact: its left obstruction
is `H₁(L_{T/S}) = 0`. Its right term is projective by base change of `N`, so the sequence
splits. Commuting the two summands and distributing tensor products over their product
gives the displayed linear equivalence. All identifications use the canonical localized
algebra structure; the zero module and zero localization satisfy the same argument. -/
theorem localized_differentials_equiv
    (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (a : A)
    [Algebra.Smooth R (Localization.Away a)]
    [Module.Projective (Localization.Away a) (Localization.Away a ⊗[A] M)] :
    let C := SymmetricAlgebra A M
    letI : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
    let T := Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
    Nonempty (KaehlerDifferential R T ≃ₗ[T]
      T ⊗[Localization.Away a] ((Localization.Away a ⊗[A] M) ×
        KaehlerDifferential R (Localization.Away a))) := by
  classical
  dsimp only
  let C := SymmetricAlgebra A M
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  let S := Localization.Away a
  let N := S ⊗[A] M
  let T := Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A C T := inferInstance
  have : IsScalarTower A S T := inferInstance
  have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun r ↦
    (IsScalarTower.algebraMap_apply R A T r).trans
      ((IsScalarTower.algebraMap_apply A S T (algebraMap R A r)).trans
        (congrArg (algebraMap S T) (IsScalarTower.algebraMap_apply R A S r).symm)))
  have : Algebra.IsPushout A S C T :=
    Algebra.IsPushout.symm
      (Algebra.isPushout_of_isLocalization (Submonoid.powers a) S C T)
  have : Module.Finite S N := inferInstance
  let β : C →ₐ[A] SymmetricAlgebra S N := lift
    (((ι S N).restrictScalars A).comp (TensorProduct.mk A S M 1))
  have hβ : ∀ x : M, β (ι A M x) = ι S N (1 ⊗ₜ[A] x) := fun x ↦ lift_ι_apply _ x
  let e : T ≃ₐ[S] SymmetricAlgebra S N :=
    (Localization.tensorRightAlgEquiv (Submonoid.powers a) C).symm.trans
      (AlgEquiv.ofBijective (AlgHom.liftEquiv A S C (SymmetricAlgebra S N) β)
        (baseChange_bijective β hβ))
  have : Algebra.Smooth S (SymmetricAlgebra S N) := smooth_of_finite_projective S N
  have : Algebra.Smooth S T := Algebra.Smooth.of_equiv e.symm
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨eC, _⟩ :=
    (AlgebraicGeometry.cotangentComplex_symmetricAlgebra (LinearMap.ker π) π hπ rfl).2
  let eRel : KaehlerDifferential S T ≃ₗ[T] T ⊗[S] N :=
    (KaehlerDifferential.tensorKaehlerEquiv A S C T).symm.trans
      ((eC.baseChange C T _ _).trans
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A C T T M).trans
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M).symm))
  let w := KaehlerDifferential.mapBaseChange R S T
  let z := KaehlerDifferential.map R S T T
  have hw : Function.Injective w := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T)).mpr
    ext x
    simp only [Subsingleton.elim x 0, map_zero]
  have hwz : Function.Exact w z := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hz : Function.Surjective z := KaehlerDifferential.map_surjective R S T
  obtain ⟨s, hs⟩ := z.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hz)
  let q := (hwz.splitSurjectiveEquiv hw ⟨s, hs⟩).1
  let q' := q.trans ((LinearEquiv.refl T _).prodCongr eRel)
  exact ⟨q'.trans ((LinearEquiv.prodComm T _ _).trans
    (TensorProduct.prodRight S T T N (KaehlerDifferential R S)).symm)⟩

end SymmetricAlgebra
