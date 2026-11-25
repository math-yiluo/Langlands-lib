/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.RingTheory.PresentationLocalizedConormalSplit
import WeilConjectures.RingTheory.LocalizedSymmetricDifferentialsSplit
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation
import WeilConjectures.RingTheory.SymmetricAlgebraSmooth

/-!
# Improving a presentation by a symmetric algebra

Source: Stacks Project, Smoothing Ring Maps, Lemma 07CE and its proof, restricted to
smooth localizations (blueprint: lem-weil-pbc-improve-presentation).

## Main statements

* `Algebra.exists_finiteType_retract_smooth_free_differentials`: the finite type retract.
* `Algebra.Presentation.symmetricAlgebra_improves`: the specified conormal construction.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Stacks Project, proof of Lemma 07CE: for any finite presentation one may take
`Sym_A(I/I²)` and its degree-zero projection
(blueprint: lem-weil-pbc-improve-presentation).

Proof: the relations generate the conormal module, by Mathlib's
`Extension.Cotangent.finite`. Its finite module generators generate the symmetric algebra
by `SymmetricAlgebra.generators_and_finitePresentation`. The zero linear map induces the
retraction `SymmetricAlgebra.lift 0`, whose restriction to `A` is the identity.
For a smooth `A_a`, `Presentation.localized_conormal_equiv`
(lem-weil-pbc-presentation-localized-conormal-split) identifies the product of the localized
conormal module and base differentials with `A_a^n`. The conormal module is therefore a
finite projective direct summand. Tensor localization and `baseChange_bijective` identify
`C_a` with its symmetric algebra, which is smooth over `A_a` by
`SymmetricAlgebra.smooth_of_finite_projective`, hence smooth over `R` by composition.
Finally `SymmetricAlgebra.localized_differentials_equiv`
(lem-weil-pbc-localized-symmetric-differentials-split) identifies the differentials with
the base change of that free product, hence they are free. -/
theorem Presentation.symmetricAlgebra_improves
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Presentation R A (Fin n) (Fin m)) :
    let C := SymmetricAlgebra A P.toExtension.Cotangent
    letI : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
    FiniteType A C ∧
      (∀ x : A, (SymmetricAlgebra.lift (0 : P.toExtension.Cotangent →ₗ[A] A))
        (algebraMap A C x) = x) ∧
      ∀ a : A, Smooth R (Localization.Away a) →
        Smooth R (Localization.Away (algebraMap A C a)) ∧
        Module.Free (Localization.Away (algebraMap A C a))
          (KaehlerDifferential R (Localization.Away (algebraMap A C a))) := by
  classical
  dsimp only
  have : Module.Finite A P.toExtension.Cotangent := Extension.Cotangent.finite P.fg_ker
  obtain ⟨k, x, hx⟩ := Module.Finite.exists_fin (R := A) (M := P.toExtension.Cotangent)
  have hgen := (SymmetricAlgebra.generators_and_finitePresentation
    A P.toExtension.Cotangent).1 k x hx
  refine ⟨⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hgen⟩⟩, ?_, ?_⟩
  · intro x
    exact AlgHom.commutes _ x
  · intro a ha
    have : Smooth R (Localization.Away a) := ha
    let S := Localization.Away a
    let M := P.toExtension.Cotangent
    let C := SymmetricAlgebra A M
    let N := TensorProduct A S M
    let T := Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
    have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower A C T := inferInstance
    have : IsScalarTower A S T := inferInstance
    have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun r ↦ by
      exact (IsScalarTower.algebraMap_apply R A T r).trans
        ((IsScalarTower.algebraMap_apply A S T (algebraMap R A r)).trans
          (congrArg (algebraMap S T) (IsScalarTower.algebraMap_apply R A S r).symm)))
    obtain ⟨q⟩ := P.localized_conormal_equiv a
    have : Module.Free S (N × KaehlerDifferential R S) := Module.Free.of_equiv q.symm
    have : Module.Projective S N := Module.Projective.of_split
      (LinearMap.inl S N (KaehlerDifferential R S)) (LinearMap.fst S N
        (KaehlerDifferential R S)) (by ext; rfl)
    have : Module.Finite S N := inferInstance
    let β : C →ₐ[A] SymmetricAlgebra S N := SymmetricAlgebra.lift
      (((SymmetricAlgebra.ι S N).restrictScalars A).comp (TensorProduct.mk A S M 1))
    have hβ : ∀ x : M, β (SymmetricAlgebra.ι A M x) =
        SymmetricAlgebra.ι S N (TensorProduct.mk A S M 1 x) := by
      intro x
      exact SymmetricAlgebra.lift_ι_apply _ x
    let e : T ≃ₐ[S] SymmetricAlgebra S N :=
      (Localization.tensorRightAlgEquiv (Submonoid.powers a) C).symm.trans
        (AlgEquiv.ofBijective (AlgHom.liftEquiv A S C (SymmetricAlgebra S N) β)
          (SymmetricAlgebra.baseChange_bijective β hβ))
    have : Smooth S (SymmetricAlgebra S N) :=
      SymmetricAlgebra.smooth_of_finite_projective S N
    have : Smooth S T := Smooth.of_equiv e.symm
    have hsm : Smooth R T := Smooth.comp R S T
    obtain ⟨d⟩ := SymmetricAlgebra.localized_differentials_equiv R A M a
    have : Module.Free T (TensorProduct S T (N × KaehlerDifferential R S)) := inferInstance
    have hfree : Module.Free T (KaehlerDifferential R T) := Module.Free.of_equiv d.symm
    let F : Submonoid C → Prop := fun t ↦ Smooth R (Localization t) ∧
      Module.Free (Localization t) (KaehlerDifferential R (Localization t))
    have hF : F (Algebra.algebraMapSubmonoid C (Submonoid.powers a)) := ⟨hsm, hfree⟩
    have hpowers : Algebra.algebraMapSubmonoid C (Submonoid.powers a) =
        Submonoid.powers (algebraMap A C a) := Algebra.algebraMapSubmonoid_powers (S := C) a
    have hF' : F (Submonoid.powers (algebraMap A C a)) :=
      Eq.mp (congrArg F hpowers) hF
    exact hF'

/-- Stacks Project, Lemma 07CE, smooth case
(blueprint: lem-weil-pbc-improve-presentation).

Proof: Mathlib's `Presentation.exists_presentation_fin` supplies a finite polynomial
presentation `P`. Apply `Presentation.symmetricAlgebra_improves` to its explicitly
constructed symmetric algebra, taking the retraction to be `SymmetricAlgebra.lift 0`.
The symmetric algebra lives in `Type (max u v)`, as required. -/
theorem exists_finiteType_retract_smooth_free_differentials
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C),
      letI : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
      FiniteType A C ∧ ∃ ρ : C →ₐ[A] A,
        (∀ x : A, ρ (algebraMap A C x) = x) ∧
        ∀ a : A, Smooth R (Localization.Away a) →
          Smooth R (Localization.Away (algebraMap A C a)) ∧
          Module.Free (Localization.Away (algebraMap A C a))
            (KaehlerDifferential R (Localization.Away (algebraMap A C a))) := by
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin R A
  let C := SymmetricAlgebra A P.toExtension.Cotangent
  refine ⟨C, inferInstance, inferInstance, ?_⟩
  have h := P.symmetricAlgebra_improves
  exact ⟨h.1, SymmetricAlgebra.lift (0 : P.toExtension.Cotangent →ₗ[A] A), h.2⟩

end Algebra
