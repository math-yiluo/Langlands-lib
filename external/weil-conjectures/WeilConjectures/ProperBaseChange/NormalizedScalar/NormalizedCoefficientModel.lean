/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.Analysis.Normed.Field.TransferInstance
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Small presentations of finite normed coefficient fields

The presentations below retain the actual norm and its closed unit ball. They are
used only to transport the existing continuous coefficient theorems across universes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite

namespace WeilConjectures.NormalizedScalar

/-- The ring of integers in the given norm, in the scheme universe.
Source: Bhatt--Scholze, Section 6.8.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def integers (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] : Subring E :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  (NormedField.valuation (K := E)).integer

/-- A small normed presentation, with an isometric algebra isomorphism to the
original coefficient field. Source: finite-dimensional linear algebra.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
structure FieldModel (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] where
  carrier : Type
  [normedField : NormedField carrier]
  [normedAlgebra : NormedAlgebra ℚ_[l] carrier]
  [finiteDimensional : FiniteDimensional ℚ_[l] carrier]
  equiv : carrier ≃ₐ[ℚ_[l]] E
  isometry : Isometry equiv

attribute [instance] FieldModel.normedField FieldModel.normedAlgebra
  FieldModel.finiteDimensional

/-- Every finite normed extension admits a small presentation preserving the norm.
Source: finite-dimensional coordinates and transfer of normed-field structure.
(blueprint: lem-weil-pbc-normalized-coefficient-model).

Proof: a finite basis embeds the underlying set in a finite power of Q_l, so it
is small. Transfer the field, norm, and scalar action along the shrink equivalence.
The transferred norm makes this equivalence an isometry by definition. -/
theorem fieldModel_nonempty (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : Nonempty (FieldModel l E) := by
  classical
  have : Small.{0} E := small_of_injective (Module.finBasis ℚ_[l] E).equivFun.injective
  let e : Shrink.{0} E ≃ E := (equivShrink E).symm
  let : NormedField (Shrink.{0} E) := e.normedField
  let : NormedAlgebra ℚ_[l] (Shrink.{0} E) :=
    { toAlgebra := e.algebra ℚ_[l]
      norm_smul_le := fun a x ↦ by
        change ‖e (a • x)‖ ≤ ‖a‖ * ‖e x‖
        rw [show e (a • x) = a • e x from
          (e.algEquiv ℚ_[l]).toLinearEquiv.map_smul a x]
        exact norm_smul_le a (e x) }
  let es : Shrink.{0} E ≃ₐ[ℚ_[l]] E := e.algEquiv ℚ_[l]
  have : FiniteDimensional ℚ_[l] (Shrink.{0} E) :=
    FiniteDimensional.of_injective es.toLinearMap es.injective
  exact ⟨{ carrier := Shrink.{0} E, equiv := es, isometry := fun _ _ ↦ rfl }⟩

variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E] [NormedAlgebra ℚ_[l] E]

/-- The presentation identifies the closed unit balls by the same coefficient map.
Source: invariance of the unit ball under an isometry.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def FieldModel.integerEquiv (m : FieldModel l E) :
    AlgebraicGeometry.ProEtale.CondensedRing.continuousIntegers l m.carrier ≃+*
      integers l E where
  toFun a := ⟨m.equiv a, by
    change ‖m.equiv a‖₊ ≤ 1
    rw [m.isometry.nnnorm_map_of_map_zero m.equiv.map_zero]
    exact a.property⟩
  invFun a := ⟨m.equiv.symm a, by
    change ‖m.equiv.symm a‖₊ ≤ 1
    have h := m.isometry.nnnorm_map_of_map_zero m.equiv.map_zero (m.equiv.symm a)
    rw [m.equiv.apply_symm_apply] at h
    rw [← h]
    exact a.property⟩
  left_inv a := Subtype.ext (m.equiv.symm_apply_apply a)
  right_inv a := Subtype.ext (m.equiv.apply_symm_apply a)
  map_mul' a b := Subtype.ext (m.equiv.map_mul a b)
  map_add' a b := Subtype.ext (m.equiv.map_add a b)

/-- Continuity on the unit balls is restriction of the presentation isometry.
Source: the subspace topology of the valuation ring.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
theorem FieldModel.integerEquiv_continuous (m : FieldModel l E) :
    Continuous m.integerEquiv :=
  (m.isometry.continuous.comp continuous_subtype_val).subtype_mk _

/-- The inverse presentation is continuous on the unit balls as well.
Source: inverse of an isometry.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
theorem FieldModel.integerEquiv_symm_continuous (m : FieldModel l E) :
    Continuous m.integerEquiv.symm := by
  have hi : Isometry m.equiv.symm := fun x y ↦ by
    simpa only [m.equiv.apply_symm_apply] using
      (m.isometry (m.equiv.symm x) (m.equiv.symm y)).symm
  exact (hi.continuous.comp continuous_subtype_val).subtype_mk _

/-- Postcomposition by a continuous ring equivalence identifies the actual
continuous-function sheaves, including their universe lifts.
Source: functoriality of C(S,-).
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def pointRingIso {A : Type} {B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf B :=
  { hom := ⟨
      { app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous _ he).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
    inv := ⟨
      { app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous _ hei).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
    hom_inv_id := by
      ext S f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      exact e.symm_apply_apply (f.down x)
    inv_hom_id := by
      ext S f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      exact e.apply_symm_apply (f.down x) }

/-- The field presentation induces its specified pointwise coefficient isomorphism.
Source: functoriality of continuous coefficient rings.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def FieldModel.pointFieldIso (m : FieldModel l E) :
    Profinite.continuousMapRingSheaf.{u} m.carrier ≅
      Profinite.continuousCoefficientRingSheaf E := by
  have hi : Isometry m.equiv.symm := fun x y ↦ by
    simpa only [m.equiv.apply_symm_apply] using
      (m.isometry (m.equiv.symm x) (m.equiv.symm y)).symm
  exact pointRingIso m.equiv.toRingEquiv m.isometry.continuous hi.continuous

/-- The integral coefficient isomorphism uses the restriction of the same field map.
Source: invariance of the unit ball under an isometry.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def FieldModel.pointIntegerIso (m : FieldModel l E) :
    Profinite.continuousMapRingSheaf.{u}
      (AlgebraicGeometry.ProEtale.CondensedRing.continuousIntegers l m.carrier) ≅
      Profinite.continuousCoefficientRingSheaf (integers l E) :=
  pointRingIso m.integerEquiv m.integerEquiv_continuous m.integerEquiv_symm_continuous

/-- The actual inclusion of the unit ball, as a map of condensed coefficient rings.
Source: the inclusion of the ring of integers in the field.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def scalarRingMap : Profinite.continuousCoefficientRingSheaf (integers l E) ⟶
    Profinite.continuousCoefficientRingSheaf E :=
  ⟨
    { app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((integers l E).subtype.compLeftContinuous _ continuous_subtype_val).comp
            ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩

/-- The underlying internal ring map of the integral inclusion.
Source: the actual continuous inclusion.
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
def scalarMap : Profinite.continuousCoefficientRingObj (integers l E) ⟶
    Profinite.continuousCoefficientRingObj E :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (scalarRingMap (l := l) (E := E))

instance : IsMonHom (scalarMap (l := l) (E := E)) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (scalarRingMap (l := l) (E := E))))

/-- The two coefficient comparisons commute with the actual integral inclusion.
This is a pointwise identity, not a choice of an isomorphism of scalar functors.
Source: restriction of a field isomorphism to its valuation ring.
(blueprint: lem-weil-pbc-normalized-coefficient-model).

Proof: both composites send a continuous integral function f to e ∘ f, viewed
as a field-valued function. Extensionality on profinite tests proves the square. -/
theorem FieldModel.scalar_square (m : FieldModel l E) :
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map m.pointIntegerIso.hom ≫
        scalarMap (l := l) (E := E) =
      AlgebraicGeometry.ProEtale.CondensedRing.integralScalarMap l m.carrier ≫
        (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map m.pointFieldIso.hom := by
  ext S f
  rfl

section
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E]

/-- E is obtained from its valuation ring by inverting ℓ. Clear the norm of an
element by a sufficiently large power of ℓ, using ‖ℓ‖ < 1.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-weil-pbc-normalized-coefficient-model). -/
instance integers_isLocalization :
    IsLocalization.Away (ℓ : integers ℓ E) E := by
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have hnorm : ‖(ℓ : E)‖ < 1 := by
    have h : ‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (ℓ : ℚ_[ℓ]))
    rw [h]
    exact Padic.norm_p_lt_one
  apply IsLocalization.Away.mk
  · change IsUnit (ℓ : E)
    exact isUnit_iff_ne_zero.mpr hp
  · intro s
    by_cases hs : s = 0
    · subst s
      exact ⟨0, 0, by simp⟩
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (inv_pos.mpr (norm_pos_iff.mpr hs)) hnorm
    have hmem : s * (ℓ : E) ^ n ∈ integers ℓ E := by
      change ‖s * (ℓ : E) ^ n‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_mul, norm_pow]
      calc
        ‖s‖ * ‖(ℓ : E)‖ ^ n ≤ ‖s‖ * ‖s‖⁻¹ :=
          (mul_lt_mul_of_pos_left hn (norm_pos_iff.mpr hs)).le
        _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hs)
    exact ⟨n, ⟨_, hmem⟩, rfl⟩
  · intro a b hab
    have h : a = b := Subtype.ext hab
    subst b
    exact ⟨0, rfl⟩

end

end WeilConjectures.NormalizedScalar
