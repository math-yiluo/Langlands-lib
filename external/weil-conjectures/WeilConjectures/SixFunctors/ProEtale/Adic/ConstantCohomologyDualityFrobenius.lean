/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.PadicTorsionLinear
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CupProduct
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDuality
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicFrobenius

/-!
# Frobenius-compatible duality for `Hⁱ(S, ℚ̄_ℓ)` from finite-level étale dualities

Let `S` be a connected quasi-compact quasi-separated scheme and `e : S ≅ S` an automorphism (the
geometric Galois Frobenius of `X̄ = X ×_{k₀} k̄`). The explicit comparison
`Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ/ℓᵐ)`, `Λ = ℤ/ℓᵐ`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), intertwines the Frobenius operator
`x ↦ ε⁻¹ ≫ Le^* x ≫ ε[n]` of the canonical Weil datum `ε : Le^* Λ_S ≅ Λ_S` with the pullback `e^*`
of pro-étale cohomology
(`AlgebraicGeometry.ProEtale.finiteAdicHPullback_unitShiftAddEquivFiniteAdicH`).

Consequently, nondegenerate finite-level pairings on `Hom(Λ_S, Λ_S[i]) × Hom(Λ_S, Λ_S[j])` which
are similitudes for the étale Frobenius operators give the finite-level Frobenius similitudes
`hQF` of `AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH`, for the pullbacks `e^*` on
the integral cohomology `Hⁿ(S, ℤ_ℓ)`; hence a perfect pairing on `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ)`
which is a similitude for any endomorphisms extending `e^*`
(`AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH_of_unitPairing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]

/-- **Finite-level pro-étale cohomology is étale `Ext`, explicitly.** On a quasi-compact
quasi-separated scheme `S`, `Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)`,
`Λ = ℤ/ℓᵐ`. -/
noncomputable def unitShiftAddEquivFiniteAdicH (n : ℕ) :
    (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(n : ℤ)⟧) ≃+
      FiniteAdicH S l m n :=
  (Etale.unitShiftAddEquivExt _ S n).trans (extAddEquivFiniteAdicH l m S n)

/-- **The comparison `Hom(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ/ℓᵐ)` is Frobenius equivariant.** For an
automorphism `e` of a connected quasi-compact quasi-separated scheme `S`, it intertwines the
Frobenius operator of the canonical Weil datum `ε : Le^* Λ_S ≅ Λ_S` with the pullback `e^*` of
pro-étale cohomology. -/
theorem finiteAdicHPullback_unitShiftAddEquivFiniteAdicH [ConnectedSpace S] (e : S ≅ S) (n : ℕ)
    (x : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(n : ℤ)⟧) :
    finiteAdicHPullback e l m n (unitShiftAddEquivFiniteAdicH l m S n x) =
      unitShiftAddEquivFiniteAdicH l m S n (Etale.frobeniusOperator e.hom
        (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom n) x) := by
  rw [unitShiftAddEquivFiniteAdicH, AddEquiv.trans_apply, AddEquiv.trans_apply,
    finiteAdicHPullback_extAddEquivFiniteAdicH]
  congr 1
  exact (Etale.unitShiftAddEquivExt_leftDerivedUpperStar _ e.hom n x).symm

/-- **Duality for `ℚ̄_ℓ`-cohomology from Frobenius-similitude finite-level étale dualities.** Let
`S` be connected, quasi-compact and quasi-separated with finite cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`,
and `e : S ≅ S`. Suppose that for every `m` there is a biadditive pairing
`Hom(Λ_S, Λ_S[i]) × Hom(Λ_S, Λ_S[j]) ⟶ Λ`, `Λ = ℤ/ℓᵐ`, nondegenerate on both sides, which is a
`c`-similitude for the Frobenius operators of the canonical Weil datum of `Λ_S`. Then for all
endomorphisms `F_V`, `F_W` of `Hⁱ(S, ℚ̄_ℓ)`, `Hʲ(S, ℚ̄_ℓ)` extending the pullbacks `e^*` of the
integral cohomology, there is a perfect pairing `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` which is a
`c`-similitude for `F_V`, `F_W`. -/
theorem exists_isPerfPair_adicConstantH_of_unitPairing [ConnectedSpace S] (e : S ≅ S)
    (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) (i j c : ℕ)
    (P : ∀ m : ℕ,
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(i : ℤ)⟧) →+
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(j : ℤ)⟧) →+
      ULift.{u + 1} (ZMod (l ^ m)))
    (hPl : ∀ m x, (∀ y, P m x y = 0) → x = 0) (hPr : ∀ m y, (∀ x, P m x y = 0) → y = 0)
    (hPF : ∀ m x y, P m
      (Etale.frobeniusOperator e.hom
        (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom i) x)
      (Etale.frobeniusOperator e.hom
        (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom j) y) =
        c • P m x y)
    (FV : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S i)
    (FW : AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S j)
    (hFV : ∀ a, FV (integralToAdicConstantH l S i a) =
      integralToAdicConstantH l S i (integralAdicHPullback e l i a))
    (hFW : ∀ b, FW (integralToAdicConstantH l S j b) =
      integralToAdicConstantH l S j (integralAdicHPullback e l j b)) :
    ∃ P' : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
        PadicAlgCl l,
      P'.IsPerfPair ∧ ∀ x y, P' (FV x) (FW y) = algebraMap ℤ_[l] (PadicAlgCl l) c * P' x y := by
  let eΛ (m : ℕ) : ULift.{u + 1} (ZMod (l ^ m)) ≃+ ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ m} :=
    AddEquiv.ulift.trans (PadicInt.quotientSpanPowRingEquiv m).symm.toAddEquiv
  let P' (m : ℕ) : FiniteAdicH S l m i →+ FiniteAdicH S l m j →+
      ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ m} :=
    AddMonoidHom.mk' (fun x ↦ ((eΛ m).toAddMonoidHom.comp
      (P m ((unitShiftAddEquivFiniteAdicH l m S i).symm x))).comp
        (unitShiftAddEquivFiniteAdicH l m S j).symm.toAddMonoidHom) fun x x' ↦ by ext y; simp
  let Q (m : ℕ) := PadicInt.bilinearOfPowSMulEqZero (pow_smul_finiteAdicH S l m i)
    (pow_smul_finiteAdicH S l m j) PadicInt.pow_smul_quotient_eq_zero (P' m)
  have hsymm (m n : ℕ) (x : FiniteAdicH S l m n) :
      (unitShiftAddEquivFiniteAdicH l m S n).symm (finiteAdicHPullback e l m n x) =
        Etale.frobeniusOperator e.hom (Etale.shiftWeilDatum e.hom
          (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom n)
            ((unitShiftAddEquivFiniteAdicH l m S n).symm x) := by
    rw [AddEquiv.symm_apply_eq, ← finiteAdicHPullback_unitShiftAddEquivFiniteAdicH,
      AddEquiv.apply_symm_apply]
  refine exists_isPerfPair_adicConstantH l S hfin i j (integralAdicHPullback e l i)
    (integralAdicHPullback e l j) c Q (fun m ↦ ?_) (fun m ↦ ?_) (fun m a b ↦ ?_) FV FW hFV hFW
  · refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    refine (unitShiftAddEquivFiniteAdicH l m S i).symm.injective ((hPl m _ fun y' ↦ ?_).trans
      (map_zero _).symm)
    obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).symm.surjective y'
    simpa [Q, P'] using LinearMap.congr_fun hx y
  · refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
    refine (unitShiftAddEquivFiniteAdicH l m S j).symm.injective ((hPr m _ fun x' ↦ ?_).trans
      (map_zero _).symm)
    obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).symm.surjective x'
    simpa [Q, P'] using LinearMap.congr_fun hy x
  · rw [reduction_integralAdicHPullback, reduction_integralAdicHPullback]
    simp only [Q, P', PadicInt.bilinearOfPowSMulEqZero_apply, AddMonoidHom.mk'_apply,
      AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, hsymm]
    rw [hPF, map_nsmul]
    exact (Nat.cast_smul_eq_nsmul ℤ_[l] c _).symm

/-- **Frobenius-equivariant duality for `ℚ̄_ℓ`-cohomology from finite-level étale dualities.**
Let `S` be connected, quasi-compact and quasi-separated with finite cohomology groups
`Hᵏ(S, ℤ/ℓᵐ)`, and `e : S ≅ S`. If for every `m` there is a biadditive pairing
`Hom(Λ_S, Λ_S[i]) × Hom(Λ_S, Λ_S[j]) ⟶ Λ`, `Λ = ℤ/ℓᵐ`, nondegenerate on both sides, which is a
`c`-similitude for the Frobenius operators of the canonical Weil datum of `Λ_S`, then there is a
perfect pairing `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` which is a `c`-similitude for the pullbacks
`e^*` (`AlgebraicGeometry.ProEtale.adicConstantHPullback`). -/
theorem exists_isPerfPair_adicConstantH_adicConstantHPullback [ConnectedSpace S] (e : S ≅ S)
    (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) (i j c : ℕ)
    (P : ∀ m : ℕ,
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(i : ℤ)⟧) →+
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(j : ℤ)⟧) →+
      ULift.{u + 1} (ZMod (l ^ m)))
    (hPl : ∀ m x, (∀ y, P m x y = 0) → x = 0) (hPr : ∀ m y, (∀ x, P m x y = 0) → y = 0)
    (hPF : ∀ m x y, P m
      (Etale.frobeniusOperator e.hom
        (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom i) x)
      (Etale.frobeniusOperator e.hom
        (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom j) y) =
        c • P m x y) :
    ∃ P' : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
        PadicAlgCl l,
      P'.IsPerfPair ∧ ∀ x y, P' (adicConstantHPullback l e i x) (adicConstantHPullback l e j y) =
        algebraMap ℤ_[l] (PadicAlgCl l) c * P' x y :=
  exists_isPerfPair_adicConstantH_of_unitPairing l S e hfin i j c P hPl hPr hPF _ _
    (adicConstantHPullback_integralToAdicConstantH l e i)
    (adicConstantHPullback_integralToAdicConstantH l e j)

/-- **Frobenius-equivariant duality for `ℚ̄_ℓ`-cohomology from cup product and trace.** Let `S`
be connected, quasi-compact and quasi-separated with finite cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`, and
`e : S ≅ S`. Suppose that for every `m` there is an additive map
`T : Hom(Λ_S, Λ_S[i + j]) ⟶ Λ`, `Λ = ℤ/ℓᵐ`, such that the cup–trace pairing
`(x, y) ↦ T(x ⌣ y)` is nondegenerate on both sides and `T ∘ F = c • T` for the Frobenius operator
`F` of the canonical Weil datum. Then there is a perfect pairing
`Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` which is a `c`-similitude for the pullbacks `e^*`. -/
theorem exists_isPerfPair_adicConstantH_of_cupProduct [ConnectedSpace S] (e : S ≅ S)
    (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) (i j c : ℕ)
    (T : ∀ m : ℕ,
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(i : ℤ) + j⟧) →+
      ULift.{u + 1} (ZMod (l ^ m)))
    (hTl : ∀ m x, (∀ y, T m (Etale.cupProduct _ i j x y) = 0) → x = 0)
    (hTr : ∀ m y, (∀ x, T m (Etale.cupProduct _ i j x y) = 0) → y = 0)
    (hTF : ∀ m z, T m (Etale.frobeniusOperator e.hom
      (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom ((i : ℤ) + j))
        z) = c • T m z) :
    ∃ P' : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
        PadicAlgCl l,
      P'.IsPerfPair ∧ ∀ x y, P' (adicConstantHPullback l e i x) (adicConstantHPullback l e j y) =
        algebraMap ℤ_[l] (PadicAlgCl l) c * P' x y :=
  exists_isPerfPair_adicConstantH_adicConstantHPullback l S e hfin i j c
    (fun m ↦ (AddMonoidHom.compHom (T m)).comp (Etale.cupProduct _ i j)) hTl hTr
    fun m x y ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.compHom_apply_apply]
      rw [← Etale.frobeniusOperator_cupProduct, hTF]

end AlgebraicGeometry.ProEtale
