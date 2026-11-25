/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethIntegralProper
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethRational
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethRationalSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegralStep
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Gabber's Künneth formula with integral coefficients: the induction

Gabber's Künneth formula with `𝒪_E`-coefficients (blueprint
`proposition-external-kunneth-formula-nearby-cycles`) holds in every chart dimension
(`NearbyCyclesModel.integralKunnethFormula`). The proof is by induction on the chart dimension,
simultaneously for all separably closed fields `k'`:

* the generic-slicing step with `𝒪_E`-coefficients over `Spec k'⟦t⟧` follows from the induction
  hypothesis over `Spec K⟦t⟧`, `K = k'(x)^alg`
  (`NearbyCyclesModel.sliceKunnethFormula_padicIntegers`);
* the reduction to proper models (`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`)
  and the proper case (`NearbyCyclesModel.isIso_kunnethMap_padicIntegers_of_isProper`) conclude,
  with the `ℚ̄_ℓ` slices obtained from the `𝒪_E` ones
  (`NearbyCyclesModel.sliceKunnethFormula_padicAlgCl`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Gabber's Künneth formula with `𝒪_E`-coefficients in chart dimension `n`**, for every finite
subextension `E ⊆ ℚ̄_ℓ` (`NearbyCyclesModel.KunnethFormula` for `Λ = 𝒪_E`). -/
def IntegralKunnethFormula (k' : Type u) [Field k'] (n : ℕ) : Prop :=
  ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    KunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n

variable {ℓ} {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- **The generic-slicing step with `𝒪_E`-coefficients** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support"): if Gabber's Künneth formula
with `𝒪_E`-coefficients holds in chart dimension `n` over the trait `Spec K⟦t⟧`, `K = k'(x)^alg`, so
does the generic-slicing step over `Spec k'⟦t⟧`. The induction hypothesis applies to the
geometric slice of the product (`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`), and
`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst_padicIntegers` concludes. -/
theorem sliceKunnethFormula_padicIntegers {n : ℕ}
    (hIH : IntegralKunnethFormula ℓ (traitSliceField k') n)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n := by
  refine ⟨fun {X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂'} φ₁ φ₂ {qM gM qN gN} hM hN hpb hP hgen hX hY hZ
    {b} hb {m₁ m₂} hle h₁ h₂ {eM} heM {eN} heN {A B} hA hB ↦ ?_⟩
  refine isIso_map_kunnethMap_of_isIso_sliceFst_padicIntegers E hM hN hpb hP hgen hb hA hB ?_
  have hP'' := IsTraitModelOver.baseChange hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
    (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))
  exact hIH E (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
    (IsTraitModelOver.baseChange hM b hb _ (traitSlice_over (traitSliceCoord k')))
    (IsTraitModelOver.baseChange hN qN (Category.comp_id qN) _ (Category.comp_id _))
    (isPullback_baseChange_product hpb b hb _ (traitSlice_over (traitSliceCoord k')))
    (by convert hP'' using 1 <;> simp) (by simp) hle h₁
    (h₂.of_isPullback (IsPullback.of_hasPullback qN (traitMap k' (traitSliceField k'))))
    (eM := pullback.fst _ _ ≫ eM) (by simp [← heM]) (eN := pullback.fst _ _ ≫ eN)
    (by simp [← heN]) hA hB


variable (ℓ) in
omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Gabber's Künneth formula with `𝒪_E`-coefficients in every chart dimension**, by induction
on the chart dimension `n`, simultaneously for all separably closed fields `k'`
(`NearbyCyclesModel.IntegralKunnethFormula`). By the reduction to proper models
(`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`), this is
`NearbyCyclesModel.isIso_kunnethMap_padicIntegers_of_isProper`, whose generic-slicing inputs
come from the induction hypothesis over the trait `Spec K⟦t⟧`, `K = k'(x)^alg`
(`NearbyCyclesModel.sliceKunnethFormula_padicIntegers`). -/
theorem integralKunnethFormula (n : ℕ) :
    ∀ (k' : Type u) [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
      [Fact (ringChar k' ≠ ℓ)], IntegralKunnethFormula ℓ k' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k' _ _ _ _ E X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂' φ₁ φ₂ qM gM qN gN hM hN hpb hP hgen m₁ m₂
    hle h₁ h₂ eM heM eN heN A B hA hB
  refine isIso_kunnethMap_of_properKunnethFormula (n := n)
    (fun {X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂'} φ₁ φ₂ {qM gM qN gN} hM hN hpb hP hgen hqM hqN hX hY hZ
      {m₁ m₂} hle h₁ h₂ {eM} heM {eN} heN {A B} hA hB ↦ ?_) hM hN hpb hP hgen hle h₁ h₂ heM heN
    hA hB
  have hslice : 0 < m₁ + m₂ → ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' (m₁ + m₂ - 1) :=
    fun hpos E ↦ by
      have : Fact (ringChar (traitSliceField k')).Prime :=
        ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
      have : Fact (ringChar (traitSliceField k') ≠ ℓ) :=
        ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
      have hIH : IntegralKunnethFormula ℓ (traitSliceField k') (m₁ + m₂ - 1) :=
        @ih (m₁ + m₂ - 1) (by omega) (traitSliceField k') _ _ _ _
      have h := sliceKunnethFormula_padicIntegers (k' := k') hIH E
      exact h
  have := hqM
  have := hqN
  have := hX
  have := hY
  have := hZ
  exact isIso_kunnethMap_padicIntegers_of_isProper hM hN hpb hP hgen h₁ h₂ hslice
    (fun hpos ↦ sliceKunnethFormula_padicAlgCl (hslice hpos)) heM heN E hA hB

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
