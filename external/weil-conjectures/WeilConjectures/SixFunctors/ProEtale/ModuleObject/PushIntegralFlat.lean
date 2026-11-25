/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-!
# Flatness of `𝒪_{E,X}` and `E_X` over `ℤ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X`
a scheme. The coefficient ring objects `𝒪_{E,X} = p_X^* 𝒪̲_E` and `E_X = p_X^* E̲` on `X_proét`
are flat abelian sheaves: tensoring with them is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_tensorLeft_padicIntegersRingObj` and
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_tensorLeft_continuousMapRingObj`). The same
holds for `E_X` with `E` any finite extension of `ℚ_ℓ`
(`preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional`) and for `𝒪_{E,X}`
with `E` any subfield of `ℚ̄_ℓ`
(`preservesFiniteLimits_tensorLeft_padicIntegersRingObj_of_algebra`).

Indeed, `T_X ≅ C(-, T)_X` for `T = 𝒪_E, E`
(`AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`),
and the sections `C(U, T)` of the latter are torsion-free, hence flat, abelian groups, so that
tensoring with it preserves monomorphisms
(`CategoryTheory.Sheaf.preservesMonomorphisms_tensorLeft_of_flat`), and it is right exact.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

/-- Continuous maps into a torsion-free topological additive monoid form a torsion-free
additive monoid. -/
lemma ULift.isAddTorsionFree_continuousMap (S T : Type*) [TopologicalSpace S] [TopologicalSpace T]
    [AddMonoid T] [ContinuousAdd T] [IsAddTorsionFree T] :
    IsAddTorsionFree (ULift.{w} C(S, T)) :=
  ⟨fun _ hn _ _ hab h ↦ ULift.ext (ContinuousMap.ext fun s ↦
    eq_of_nsmul_eq_nsmul_of_addCommute hn
      (congrArg (fun z : ULift.{w} C(S, T) ↦ z.down s) hab)
      (congrArg (fun z : ULift.{w} C(S, T) ↦ z.down s) h))⟩

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

/-- For a Hausdorff, totally disconnected topological ring `T` which is torsion-free as an abelian
group, tensoring with the coefficient ring object `T_X = p_X^* T̲` preserves monomorphisms:
`T_X ≅ C(-, T)_X`, whose sections are torsion-free, hence flat, abelian groups. -/
lemma preservesMonomorphisms_tensorLeft_continuousMapComparison (T : Type) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] [T2Space T] [TotallyDisconnectedSpace T] [IsAddTorsionFree T] :
    (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj T) X)
      ).PreservesMonomorphisms := by
  have hflat (U : X.ProEtᵒᵖ) : Module.Flat ℤ (((sheafCompose (ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)).obj.obj U) := by
    have := ULift.isAddTorsionFree_continuousMap.{u + 1} U.unop.left T
    have : HasUniqueDiv (ULift.{u + 1} C(U.unop.left, T)) :=
      ⟨fun _ hn _ _ h ↦ eq_of_nsmul_eq_nsmul_of_addCommute hn (add_comm _ _) h⟩
    have : Module.IsTorsionFree ℤ (ULift.{u + 1} C(U.unop.left, T)) := inferInstance
    exact inferInstanceAs (Module.Flat ℤ (ULift.{u + 1} C(U.unop.left, T)))
  have := Sheaf.preservesMonomorphisms_tensorLeft_of_flat (ProEt.topology X) _ hflat
  have := isIso_continuousMapComparison X T
  exact Functor.PreservesMonomorphisms.of_iso
    ((tensoringLeft _).mapIso (asIso (continuousMapComparison X T)).symm)

/-- Tensoring with an abelian sheaf on `X_proét` is exact as soon as it preserves monomorphisms,
being right exact. -/
lemma preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [(tensorLeft A).PreservesMonomorphisms] :
    PreservesFiniteLimits (tensorLeft A) := by
  have : (tensorLeft A).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact (tensorLeft A).preservesFiniteLimits_of_preservesHomology

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- **`𝒪_{E,X}` is flat over `ℤ`**: tensoring with `𝒪_{E,X} = p_X^* 𝒪̲_E` is exact. -/
instance preservesFiniteLimits_tensorLeft_padicIntegersRingObj :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :=
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have := PadicAlgCl.isUltrametricDist_ofAlgebra ℓ E
  have : CharZero E := (algebraMap E (PadicAlgCl ℓ)).charZero
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X (PadicAlgCl.integers ℓ E)
  preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

end Integers

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- **`E_X` is flat over `ℤ`**: tensoring with `E_X = p_X^* E̲` is exact. -/
instance preservesFiniteLimits_tensorLeft_continuousMapRingObj :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :=
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X E.1
  preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

namespace CondensedRing

/-- For a finite extension `E` of `ℚ_ℓ`, `E_X = p_X^* E̲` is flat over `ℤ`. -/
theorem preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X E
  exact preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

/-- For a subfield `E` of `ℚ̄_ℓ`, `𝒪_{E,X} = p_X^* 𝒪̲_E` is flat over `ℤ`. -/
theorem preservesFiniteLimits_tensorLeft_padicIntegersRingObj_of_algebra (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    (X : Scheme.{u}) :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  have : IsAddTorsionFree E := inferInstance
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X (PadicAlgCl.integers ℓ E)
  exact preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

end CondensedRing

end AlgebraicGeometry.ProEtale
