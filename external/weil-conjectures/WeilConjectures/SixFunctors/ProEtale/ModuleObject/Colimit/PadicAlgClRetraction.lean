/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRetraction
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!

# An `E_X`-linear retraction of `E_X ⟶ ℚ̄_ℓ,X`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` and `X` a scheme. This file
constructs a retraction `ρ : ℚ̄_ℓ,X ⟶ E_X` of the inclusion `E_X ⟶ ℚ̄_ℓ,X` which is `E_X`-linear
on both sides (`AlgebraicGeometry.ProEtale.padicAlgClRetraction`).

* Linear algebra: `E` being a field, the inclusion `E ⟶ ℚ̄_ℓ` has an `E`-linear left inverse
  `p : ℚ̄_ℓ → E` (`PadicAlgCl.FiniteIntermediateField.linearRetraction`). Its restriction to a
  finite subextension `F` is a `ℚ_ℓ`-linear map out of a finite dimensional normed
  `ℚ_ℓ`-space, hence continuous.
* Condensed level: `s ↦ p ∘ s` is a morphism of condensed abelian groups `ℚ̲̄_ℓ ⟶ E̲`
  (`Profinite.padicAlgClRetraction`), since a section `s` of `ℚ̲̄_ℓ` takes values in a finite
  subextension. It is a retraction of the inclusion `E̲ ⟶ ℚ̲̄_ℓ` and is `E̲`-linear; the
  linearity is checked on presheaves through the lax monoidal structure of `sheafToPresheaf`.
* The lax monoidal functor `p_X^*` carries these statements to `X_proét`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- An `E`-linear left inverse `ℚ̄_ℓ → E` of the inclusion of a finite subextension `E`. -/
noncomputable def FiniteIntermediateField.linearRetraction (E : FiniteIntermediateField ℓ) :
    PadicAlgCl ℓ →ₗ[E.1] E.1 :=
  (LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E.1 (PadicAlgCl ℓ))
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)).choose

/-- The `E`-linear map `ℚ̄_ℓ → E` is a left inverse of the inclusion `E ⊆ ℚ̄_ℓ`. -/
@[simp]
lemma FiniteIntermediateField.linearRetraction_algebraMap (E : FiniteIntermediateField ℓ)
    (x : E.1) : FiniteIntermediateField.linearRetraction E (algebraMap E.1 (PadicAlgCl ℓ) x) = x :=
  LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective
    (Algebra.linearMap E.1 (PadicAlgCl ℓ))
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)).choose_spec x

/-- The restriction of the `E`-linear map `ℚ̄_ℓ → E` to a finite subextension `F` is
continuous: it is `ℚ_ℓ`-linear out of the finite dimensional normed `ℚ_ℓ`-space `F`. -/
lemma FiniteIntermediateField.continuous_linearRetraction_comp_val
    (E : FiniteIntermediateField ℓ) (F : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] F] :
    Continuous fun x : F ↦ FiniteIntermediateField.linearRetraction E (x : PadicAlgCl ℓ) :=
  LinearMap.continuous_of_finiteDimensional
    (((FiniteIntermediateField.linearRetraction E).restrictScalars ℚ_[ℓ]).comp
      F.val.toLinearMap)

/-- The `E`-linear map `ℚ̄_ℓ → E` sends a continuous map `S → ℚ̄_ℓ` with values in a finite
subextension to a continuous map `S → E`. -/
lemma FiniteIntermediateField.continuous_linearRetraction_comp (E : FiniteIntermediateField ℓ)
    {S : Type*} [TopologicalSpace S] (f : finiteIntermediateFieldValued ℓ S) :
    Continuous fun s ↦ FiniteIntermediateField.linearRetraction E (f.1 s) := by
  obtain ⟨F, hF, hf⟩ := f.2
  exact (FiniteIntermediateField.continuous_linearRetraction_comp_val E F).comp
    (f.1.continuous.subtype_mk hf)

end PadicAlgCl

namespace Profinite

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The retraction `ℚ̲̄_ℓ ⟶ E̲` of condensed abelian groups, postcomposition with the `E`-linear
left inverse `ℚ̄_ℓ → E` of the inclusion `E ⊆ ℚ̄_ℓ`. -/
noncomputable def padicAlgClRetraction : padicAlgClRingObj.{u} ℓ ⟶ continuousMapRingObj E :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun a := ULift.up ⟨fun s ↦ FiniteIntermediateField.linearRetraction E (a.down.1 s),
            FiniteIntermediateField.continuous_linearRetraction_comp E a.down⟩
          map_zero' := ULift.ext (ContinuousMap.ext fun _ ↦
            map_zero (FiniteIntermediateField.linearRetraction E))
          map_add' _ _ := ULift.ext (ContinuousMap.ext fun _ ↦
            map_add (FiniteIntermediateField.linearRetraction E) _ _) }
     naturality _ _ _ := rfl }⟩

/-- The retraction `ℚ̲̄_ℓ ⟶ E̲` is a retraction of the inclusion `E̲ ⟶ ℚ̲̄_ℓ`. -/
@[reassoc (attr := simp)]
lemma padicSubfieldRingObjToPadicAlgCl_comp_padicAlgClRetraction :
    padicSubfieldRingObjToPadicAlgCl.{u} ℓ E ≫ padicAlgClRetraction ℓ E = 𝟙 _ := by
  ext S a
  exact ULift.ext (ContinuousMap.ext fun s ↦
    FiniteIntermediateField.linearRetraction_algebraMap E (a.down s))

/-- The retraction `ℚ̲̄_ℓ ⟶ E̲` is `E̲`-linear: `ρ(a s) = a ρ(s)`. -/
lemma padicSubfieldRingObjToPadicAlgCl_whiskerRight_comp_mul_comp_padicAlgClRetraction :
    padicSubfieldRingObjToPadicAlgCl.{u} ℓ E ▷ padicAlgClRingObj ℓ ≫ μ[padicAlgClRingObj ℓ] ≫
      padicAlgClRetraction ℓ E =
    continuousMapRingObj E ◁ padicAlgClRetraction ℓ E ≫ μ[continuousMapRingObj E] := by
  refine Sheaf.hom_ext_of_μ_comp ?_
  have h₁ := Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose (coherentTopology Profinite.{u})
    (padicAlgClCondensedRing.{u} ℓ)
  have h₂ := Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose (coherentTopology Profinite.{u})
    (continuousMapRingSheaf.{u} E)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, reassoc_of% h₁,
    ← Functor.LaxMonoidal.μ_natural_right_assoc, h₂]
  ext S : 2
  refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a b ↦ ?_)
  exact ULift.ext (ContinuousMap.ext fun s ↦
    (FiniteIntermediateField.linearRetraction E).map_smul (a.down s) (b.down.1 s))

/-- The retraction `ℚ̲̄_ℓ ⟶ E̲` is `E̲`-linear on the right: `ρ(s a) = ρ(s) a`. -/
lemma whiskerLeft_padicSubfieldRingObjToPadicAlgCl_comp_mul_comp_padicAlgClRetraction :
    padicAlgClRingObj ℓ ◁ padicSubfieldRingObjToPadicAlgCl.{u} ℓ E ≫ μ[padicAlgClRingObj ℓ] ≫
      padicAlgClRetraction ℓ E =
    padicAlgClRetraction ℓ E ▷ continuousMapRingObj E ≫ μ[continuousMapRingObj E] := by
  refine Sheaf.hom_ext_of_μ_comp ?_
  have h₁ := Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose (coherentTopology Profinite.{u})
    (padicAlgClCondensedRing.{u} ℓ)
  have h₂ := Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose (coherentTopology Profinite.{u})
    (continuousMapRingSheaf.{u} E)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_right_assoc, reassoc_of% h₁,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, h₂]
  ext S : 2
  refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a b ↦ ?_)
  exact ULift.ext (ContinuousMap.ext fun s ↦
    (congrArg (FiniteIntermediateField.linearRetraction E)
      (mul_comm (a.down.1 s) (b.down s : PadicAlgCl ℓ))).trans
      (((FiniteIntermediateField.linearRetraction E).map_smul (b.down s) (a.down.1 s)).trans
        (mul_comm _ _)))

end Profinite
