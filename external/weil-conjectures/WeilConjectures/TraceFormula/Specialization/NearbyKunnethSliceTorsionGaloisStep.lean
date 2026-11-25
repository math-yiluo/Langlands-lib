/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionSquares
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionProduct
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionDescent

/-!

# The Galois descent step of Gabber's Künneth formula modulo `ϖ`

Step 2 of the generic-slicing step modulo `ϖ` (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, identification (2) and projection formula
(3)): for a generic slice trait `S'`, if the Künneth map of the configuration `M_{S'} ⟵ P_{S'} ⟶ N`
of the slices over `S'` is invertible, so is the pullback of the Künneth map of the geometric
generic fibres to the special fibre of the slice of `P`
(`NearbyCyclesModel.isIso_map_kunnethMap_toGeneric_of_isIso_coordinateSliceTrait`). This is
`NearbyCyclesModel.isIso_map_kunnethMap_of_galoisSlice` applied to the Galois-layer models of
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionGalois` and
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionProduct`.

The pullback exchanges of the morphisms `ρ` to the Galois layers are proved invertible directly
against the instantiated goals, rather than by
`NearbyCyclesModel.isIso_pullbackExchange_coordinateSliceToGaloisLayer`: the two statements differ
by the `HasPullback` proofs inside the special fibres, and unifying them unfolds the pullback
exchanges.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k' : Type u}
  [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)

attribute [local instance] GenericSliceTrait.algebraR GenericSliceTrait.algebraΩ
  GenericSliceTrait.algebraBaseΩ GenericSliceTrait.algebraRΩ

omit [IsSepClosed k'] in
/-- The powers of the characteristic of `k'` are invertible in `𝔽_E`, as `char k' ≠ ℓ`. -/
theorem isUnit_ringChar_pow_integersResidueField (n : ℕ) :
    IsUnit (((ringChar k' ^ n : ℕ)) : PadicAlgCl.integersResidueField ℓ E.1) := by
  rw [Nat.cast_pow]
  refine IsUnit.pow n ?_
  rw [isUnit_iff_ne_zero]
  intro h
  have hℓ : ℓ ∣ ringChar k' := by
    rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _
      ((ringChar.spec _ ℓ).1 (PadicAlgCl.natCast_eq_zero_integersResidueField ℓ E.1)) with h₁ | h₁
    · exact absurd h₁ CharP.ringChar_ne_one
    · exact h₁ ▸ (ringChar.spec _ _).1 h
  exact (Fact.out : ringChar k' ≠ ℓ)
    ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 hℓ).symm

-- the instantiation of the descent lemma at the Galois-layer models is a large term
/-- **Galois descent along a generic slice trait** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, identification (2) and projection formula (3),
coefficients `𝔽_E`): if the Künneth map of the configuration `M_{S'} ⟵ P_{S'} ⟶ N` of the slices
over a generic slice trait `S'` is invertible at `Lσ^* A`, `B`, then so is the pullback of the
Künneth map of the geometric generic fibres to the special fibre of the slice of `P`. -/
theorem isIso_map_kunnethMap_toGeneric_of_isIso_coordinateSliceTrait
    (hM : M.IsTraitModelOver qM gM)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM) (D : GenericSliceTrait k')
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj 𝔽 M.generic))}
    (hA : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj 𝔽 N.generic))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj B))
    (a : ℤ) (hBa : B.IsGE a)
    (hS : IsIso (kunnethMap 𝔽 (coordinateSliceTraitMap φ₁ b D)
      (coordinateSliceTraitSnd hP hb D (φ₂ := φ₂))
      ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj A) B)) :
    IsIso (L((𝟙 _ ≫ coordinateSliceTraitSpecial hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
      D)^*⟦𝔽⟧).map (kunnethMap 𝔽 φ₁.toGeneric φ₂.toGeneric A B)) := by
  refine isIso_map_kunnethMap_of_galoisSlice
    (PadicAlgCl.integersResidueField ℓ E.1)
    φ₁.toGeneric φ₂.toGeneric (coordinateSliceGaloisMap φ₁ hM hP b hb D)
    (coordinateSliceGaloisModelHom hM b hb D)
    (coordinateSliceGaloisModelHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D)
    (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)
    (coordinateSliceGaloisMap_generic_comp_residue φ₁ hM hP b hb D)
    (coordinateSliceToGaloisLayer hM b hb D)
    (coordinateSliceToGaloisLayer hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D)
    (coordinateSliceTraitMap φ₁ b D) (coordinateSliceTraitSnd hP hb D (φ₂ := φ₂))
    ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20
    ?a21 ?a22
  case a1 => exact Category.comp_id _
  case a2 => exact Category.comp_id _
  case a3 => exact coordinateSliceGaloisMap_total_comp_galoisModelHom_total φ₁ hM hP b hb D
  case a4 => exact coordinateSliceGaloisMap_generic_comp_galoisModelHom_generic φ₁ hM hP b hb D
  case a5 =>
    rw [Category.id_comp, Category.id_comp]
    exact coordinateSliceTraitMapSpecial_comp φ₁ hM hP b hb D
  case a6 => exact isIso_pullbackExchange_coordinateSliceGaloisModelHom hM b hb D 𝔽
  case a7 =>
    exact isIso_pullbackExchange_coordinateSliceGaloisModelHom hP (φ₁.total ≫ b)
      (comp_coordinate_fst hb) D 𝔽
  case a8 => simp
  case a9 => exact coordinateSliceTraitMapGeneric_comp_toGaloisLayer_generic φ₁ hM hP b hb D
  case a10 => exact coordinateSliceTraitMapGeneric_comp φ₁ hM hP b hb D
  case a11 => simp
  case a12 =>
    rw [Hom.comp_generic, ← coordinateSliceToGaloisLayer_generic_comp_galoisModelHom_generic hP
      (φ₁.total ≫ b) (comp_coordinate_fst hb) D]
    simp only [Category.assoc]
  case a13 => simp
  case a14 => simp
  case a15 =>
    intro C
    refine @Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq 𝔽 _ _ _ _ ?G _ _ ?r
      ?inst ?ε _ _ ?hM _ ?ht ?hg C
    case G => exact (coordinateSliceTraitModel b D).generic
    case r => exact (coordinateSliceToGaloisLayer hM b hb D).generic
    case ε => exact (coordinateSliceTraitModel b D).ε
    case inst =>
      exact (coordinateSliceTraitHom hM b hb D).isUniversalHomeomorphism_traitChangeInsepMap
        (coordinateSliceTraitHom_total_comp hM b hb D) (IsPullback.of_hasPullback _ _)
        hM.isPullback_j (IsPullback.lift_snd _ _ _ _)
    case hg => exact HEq.rfl
    case ht => exact HEq.rfl
    case hM =>
      have hj : (coordinateSliceTraitModel b D).j =
          (coordinateSliceToGaloisLayer hM b hb D).generic ≫
            ((coordinateSliceGaloisModel hM b hb D).galoisLayer
              (coordinateSliceGaloisResidue hM b hb D)
              (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)).j := by
        simpa using (coordinateSliceToGaloisLayer hM b hb D).comm_j.symm
      rw [← hj]
      rfl
  case a16 =>
    intro C
    refine @Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq 𝔽 _ _ _ _ ?G _ _ ?r
      ?inst ?ε _ _ ?hM _ ?ht ?hg C
    case G => exact (coordinateSliceTraitModel (φ₁.total ≫ b) D).generic
    case r =>
      exact (coordinateSliceToGaloisLayer hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).generic
    case ε => exact (coordinateSliceTraitModel (φ₁.total ≫ b) D).ε
    case inst =>
      exact (coordinateSliceTraitHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        D).isUniversalHomeomorphism_traitChangeInsepMap
        (coordinateSliceTraitHom_total_comp hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D)
        (IsPullback.of_hasPullback _ _) hP.isPullback_j (IsPullback.lift_snd _ _ _ _)
    case hg => exact HEq.rfl
    case ht => exact HEq.rfl
    case hM =>
      have hj : (coordinateSliceTraitModel (φ₁.total ≫ b) D).j =
          (coordinateSliceToGaloisLayer hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).generic ≫
            ((coordinateSliceGaloisModel hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D).galoisLayer
              (coordinateSliceGaloisResidue hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D)
              (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)).j := by
        simpa using (coordinateSliceToGaloisLayer hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          D).comm_j.symm
      rw [← hj]
      rfl
  case a17 =>
    intro L'
    obtain ⟨n, hn⟩ := D.exists_finrank_eq_pow L'
    rw [hn]
    exact isUnit_ringChar_pow_integersResidueField E n
  case a18 => exact hA
  case a19 => exact hB
  case a20 => exact a
  case a21 => exact hBa
  case a22 => exact hS

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
