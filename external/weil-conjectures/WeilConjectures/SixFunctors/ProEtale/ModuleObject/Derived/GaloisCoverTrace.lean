/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisCoverTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear

/-!
# The derived trace of a finite étale Galois covering

Let `Λ` be a commutative condensed ring and `g : Y ⟶ X` a finite étale morphism with a Galois
action of a finite group `Γ` (`AlgebraicGeometry.ProEtale.IsGaloisAction`). The pushforward
`g_*` of module objects is exact, so the derived adjunction `Lg^* ⊣ Rg_*`
(`AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`) carries the
derived trace `Lg^* ⋙ Rg_* ⟶ 𝟭` and the derived action of `Γ`
(`AlgebraicGeometry.ProEtale.CondensedRing.derivedGaloisTrace`,
`AlgebraicGeometry.ProEtale.CondensedRing.derivedGaloisAction`), with

* `u ≫ t = |Γ| • 𝟙`
  (`AlgebraicGeometry.ProEtale.CondensedRing.derivedUnit_comp_derivedGaloisTrace`),
* `t ≫ u = ∑ a, ρ a`
  (`AlgebraicGeometry.ProEtale.CondensedRing.derivedGaloisTrace_comp_derivedUnit`).

Hence, when multiplication by `|Γ|` is invertible on `G ∈ D(Mod_{Λ_X})`, the derived unit
`G ⟶ Rg_* Lg^* G` is a split monomorphism, split by the normalized trace, and its idempotent is
the average of the action of `Γ`
(`AlgebraicGeometry.ProEtale.CondensedRing.derivedUnit_comp_normalizedTrace`,
`AlgebraicGeometry.ProEtale.CondensedRing.nsmul_normalizedTrace_comp_derivedUnit`). Multiplication
by `|Γ|` is invertible as soon as `|Γ|` is a unit in a ring of constants of `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_nsmul_id_of_isUnit`); this covers `ℚ̄_ℓ`, finite
extensions `E` of `ℚ_ℓ`, `𝒪_E` and finite rings `Λ` when `|Γ|` is a power of `p ≠ ℓ`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_nsmul_id_padicAlgCl`,
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_nsmul_id_padicSubfield`).
-/

@[expose] public section

universe u

open CategoryTheory Category Abelian Limits MonoidalCategory MonObj

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] [Etale g] [Surjective g]
  {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
  [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

instance : PreservesFiniteColimits (g)_*⟦Λ⟧ := preservesFiniteColimits_lowerStar_of_isFinite Λ g

/-- **The derived trace of a finite étale Galois covering** `Lg^* ⋙ Rg_* ⟶ 𝟭`. -/
noncomputable def derivedGaloisTrace : L((g)^*⟦Λ⟧) ⋙ R((g)_*⟦Λ⟧) ⟶ 𝟭 _ :=
  Adjunction.derivedTrace (galoisTrace Λ g hρ hmul hgal)

/-- **The derived action of `a : Γ`** on `Lg^* ⋙ Rg_*`. -/
noncomputable def derivedGaloisAction (a : Γ) :
    L((g)^*⟦Λ⟧) ⋙ R((g)_*⟦Λ⟧) ⟶ L((g)^*⟦Λ⟧) ⋙ R((g)_*⟦Λ⟧) :=
  Adjunction.derivedEndo (galoisAction Λ g hρ a)

/-- **The derived unit followed by the derived trace is the degree** `|Γ|`. -/
theorem derivedUnit_comp_derivedGaloisTrace :
    (derivedUpperStarLowerStarAdjunction Λ g).unit ≫ derivedGaloisTrace Λ g hρ hmul hgal =
      Fintype.card Γ • 𝟙 _ :=
  (upperStarLowerStarAdjunction Λ g).unit_comp_derivedTrace
    (unit_comp_galoisTrace Λ g hρ hmul hgal)

/-- **The derived trace followed by the derived unit is the norm** `∑ a, ρ a`. -/
theorem derivedGaloisTrace_comp_derivedUnit :
    derivedGaloisTrace Λ g hρ hmul hgal ≫ (derivedUpperStarLowerStarAdjunction Λ g).unit =
      ∑ a, derivedGaloisAction Λ g hρ a :=
  (upperStarLowerStarAdjunction Λ g).derivedTrace_comp_unit
    (galoisTrace_comp_unit Λ g hρ hmul hgal)


/-- **The pro-`p` trace splitting at a finite level**: if multiplication by `|Γ|` is invertible
on `G`, the derived unit `G ⟶ Rg_* Lg^* G` is split by the normalized derived trace. -/
theorem derivedUnit_comp_normalizedTrace
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) [IsIso (Fintype.card Γ • 𝟙 G)] :
    (derivedUpperStarLowerStarAdjunction Λ g).unit.app G ≫
      normalizedTrace (show _ ⟶ G from (derivedGaloisTrace Λ g hρ hmul hgal).app G)
        (Fintype.card Γ) = 𝟙 G := by
  have : IsIso (Fintype.card Γ • 𝟙 ((𝟭 _).obj G)) :=
    inferInstanceAs (IsIso (Fintype.card Γ • 𝟙 G))
  refine comp_normalizedTrace ?_
  have h := congr_app (derivedUnit_comp_derivedGaloisTrace Λ g hρ hmul hgal) G
  simpa only [NatTrans.comp_app, NatTrans.app_nsmul, NatTrans.id_app] using h

/-- **The idempotent of the splitting is the average of the action of `Γ`**:
`|Γ| • (r ≫ u) = ∑ a, ρ a` for the normalized derived trace `r`. -/
theorem nsmul_normalizedTrace_comp_derivedUnit
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) [IsIso (Fintype.card Γ • 𝟙 G)] :
    Fintype.card Γ • (normalizedTrace (show _ ⟶ G from (derivedGaloisTrace Λ g hρ hmul hgal).app G)
      (Fintype.card Γ) ≫ (derivedUpperStarLowerStarAdjunction Λ g).unit.app G) =
      ∑ a, (derivedGaloisAction Λ g hρ a).app G := by
  refine nsmul_normalizedTrace_comp_eq_sum _ ?_
  have h := congr_app (derivedGaloisTrace_comp_derivedUnit Λ g hρ hmul hgal) G
  simpa only [NatTrans.comp_app, NatTrans.app_sum] using h

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Invertibility of the degree, for any coefficient ring**: if a natural number `n` is a unit
in a ring `K` of constants of `Λ` (a ring homomorphism `K →+* Γ Λ`), then multiplication by `n`
is invertible on every object of `D(Mod_{Λ_X})`. -/
lemma isIso_nsmul_id_of_isUnit {K : Type*} [CommRing K] (φ : K →+* Γ Λ)
    {X : Scheme.{u}} {n : ℕ} (hn : IsUnit (n : K))
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (n • 𝟙 G) := by
  let := modLinear Λ φ X
  obtain ⟨v, hv⟩ := hn
  have e : n • 𝟙 G = (v : K) • 𝟙 G := by rw [hv, Nat.cast_smul_eq_nsmul]
  rw [e]
  refine ⟨⟨(↑v⁻¹ : K) • 𝟙 G, ?_, ?_⟩⟩ <;>
    simp only [Linear.smul_comp, Linear.comp_smul, id_comp, smul_smul, Units.mul_inv,
      Units.inv_mul, one_smul]

/-- Multiplication by a nonzero natural number is invertible on `D(Mod_{ℚ̄_ℓ,X})`. -/
lemma isIso_nsmul_id_padicAlgCl (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}} {n : ℕ} (hn : n ≠ 0)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :
    IsIso (n • 𝟙 G) :=
  isIso_nsmul_id_of_isUnit _ (Profinite.PadicAlgCl.constRingHom.{u} ℓ)
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) G

/-- Multiplication by a nonzero natural number is invertible on `D(Mod_{E_X})` for a finite
extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
lemma isIso_nsmul_id_padicSubfield (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
    {X : Scheme.{u}} {n : ℕ} (hn : n ≠ 0)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :
    IsIso (n • 𝟙 G) :=
  isIso_nsmul_id_of_isUnit _ (Profinite.continuousMapConstRingHom.{u} E)
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) G


/-- A natural number prime to `ℓ` is a unit of the ring of integers `𝒪_E` of a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`: it has absolute value `1`. -/
lemma isUnit_natCast_integers (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {n : ℕ}
    (hn : ℓ.Coprime n) : IsUnit (n : integers ℓ E.1) := by
  have h1 : ‖algebraMap E.1 (PadicAlgCl ℓ) (n : E.1)‖₊ = 1 := by
    rw [map_natCast, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one,
      show ((n : PadicAlgCl ℓ)) = ((n : ℚ_[ℓ]) : PadicAlgCl ℓ) by simp, PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact hn
  have hne : (n : E.1) ≠ 0 := by
    intro h
    rw [h, map_zero, nnnorm_zero] at h1
    exact zero_ne_one h1
  refine ⟨⟨n, ⟨(n : E.1)⁻¹, ?_⟩, ?_, ?_⟩, rfl⟩
  · change ‖algebraMap E.1 (PadicAlgCl ℓ) (n : E.1)⁻¹‖₊ ≤ 1
    rw [map_inv₀, nnnorm_inv, h1, inv_one]
  · exact Subtype.ext (mul_inv_cancel₀ hne)
  · exact Subtype.ext (inv_mul_cancel₀ hne)

/-- Multiplication by a natural number prime to `ℓ` is invertible on `D(Mod_{𝒪_E,X})` for the
ring of integers `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
lemma isIso_nsmul_id_padicIntegers (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
    {X : Scheme.{u}} {n : ℕ} (hn : ℓ.Coprime n)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    IsIso (n • 𝟙 G) :=
  letI := normedFieldOfAlgebra ℓ E.1
  isIso_nsmul_id_of_isUnit _ (Profinite.continuousMapConstRingHom.{u} (integers ℓ E.1))
    (isUnit_natCast_integers ℓ E hn) G

end AlgebraicGeometry.ProEtale.CondensedRing
