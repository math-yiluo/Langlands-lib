/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDualityFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantIntLowerStar
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantExt

/-!
# The geometric Frobenius of `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` is the pullback along the Galois Frobenius

Through the identification `Hʳ(Y ⊗ k̄, ℚ̄_ℓ) ≅ Hʳ(Ȳ_proét, ℚ̄_ℓ)` of the cohomology of the constant
Weil sheaf with pro-étale cohomology, the geometric Frobenius is the pullback
`Fr^* : Hʳ(Ȳ, ℚ̄_ℓ) ⟶ Hʳ(Ȳ, ℚ̄_ℓ)` along the geometric Galois Frobenius `Fr : Ȳ ≅ Ȳ`
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback`).
In particular it preserves the image of the integral cohomology `Hʳ(Ȳ, ℤ_ℓ)`, on which it is the
pullback `Fr^*` of integral cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian MonoidalCategory

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius on `Ext(ℤ, ℚ̄_ℓ)` computed with an injective resolution of the constant
pro-étale Weil sheaf is the pullback along the geometric Galois Frobenius. -/
theorem extFrobenius_eq_adicConstantHPullback
    (I : InjectiveResolution (ProEtaleWeilSheaf.adicConstant k₀ l Y)) (r : ℕ)
    (x : Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj (ProEtaleWeilSheaf.adicConstant k₀ l Y))
      r) :
    extFrobenius I r x =
      adicConstantHPullback l
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso r x := by
  rw [extFrobenius_eq_extFrobeniusOfResolution, extFrobeniusOfResolution_eq,
    adicConstantHPullback_apply, Ext.mk₀CompMk₀,
    ← constantIntSheafToLowerStar_eq_constantIntIsoLowerStar_hom]
  rfl

end ProEtaleWeilSheaf

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

set_option maxRecDepth 4000 in
/-- **The geometric Frobenius of `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` is the pullback along the Galois Frobenius.**
`Hʳ(Y ⊗ k̄, ℚ̄_ℓ) ≅ Hʳ(Ȳ_proét, ℚ̄_ℓ)` as `ℚ̄_ℓ`-vector spaces, the geometric Frobenius of the
constant Weil sheaf corresponding to the pullback `Fr^*` along the geometric Galois Frobenius
`Fr : Ȳ ≅ Ȳ` (`AlgebraicGeometry.ProEtale.adicConstantHPullback`). -/
theorem exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback (r : ℕ) :
    ∃ Θ : AdicConstantH l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber r ≃ₗ[PadicAlgCl l]
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).carrier,
      ∀ x, Θ (adicConstantHPullback l
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso r x) =
        ((WeilSheaf.adicConstant k₀ l Y).cohomology r).frobenius (Θ x) := by
  obtain ⟨Θ, hΘ⟩ := exists_linearEquiv_adicConstantH_cohomology
    (injectiveResolution (WeilSheaf.adicConstant k₀ l Y).obj) r
  refine ⟨Θ, fun x ↦ ?_⟩
  refine (congrArg Θ (ProEtaleWeilSheaf.extFrobenius_eq_adicConstantHPullback
    (injectiveResolution (WeilSheaf.adicConstant k₀ l Y).obj) r x)).symm.trans ?_
  exact hΘ x

/-- **Frobenius-equivariant Poincaré duality for `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` from finite-level dualities**
(the transport step of blueprint `theorem-poincare-duality--6`, for the constant Weil
sheaf). Let the geometric fiber `Ȳ` be connected, with finite cohomology groups
`Hᵏ(Ȳ, ℤ/ℓᵐ)`. If for every `m` there is a pairing `Hⁱ(Ȳ, ℤ/ℓᵐ) × Hʲ(Ȳ, ℤ/ℓᵐ) ⟶ ℤ/ℓᵐ` in
`D(Ȳ_ét, ℤ/ℓᵐ)`, nondegenerate on both sides and a `c`-similitude for the étale Frobenius
operators of the Galois Frobenius, then there is a perfect pairing
`Hⁱ(Y ⊗ k̄, ℚ̄_ℓ) × Hʲ(Y ⊗ k̄, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = c ⟨x, y⟩` for the geometric
Frobenius `F` of the constant Weil sheaf. -/
theorem exists_isPerfPair_cohomology_adicConstant_of_unitPairing
    [CompactSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [QuasiSeparatedSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [ConnectedSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (hfin : ∀ m k, Finite (FiniteAdicH (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber l m k))
    (i j c : ℕ)
    (P : ∀ m : ℕ,
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber))⟦(i : ℤ)⟧) →+
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber))⟦(j : ℤ)⟧) →+
      ULift.{u + 1} (ZMod (l ^ m)))
    (hPl : ∀ m x, (∀ y, P m x y = 0) → x = 0) (hPr : ∀ m y, (∀ x, P m x y = 0) → y = 0)
    (hPF : ∀ m x y, P m
      (Etale.frobeniusOperator (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
        (Etale.shiftWeilDatum (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (Etale.leftDerivedUpperStarUnitIso _
            (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom i) x)
      (Etale.frobeniusOperator (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
        (Etale.shiftWeilDatum (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
          (Etale.leftDerivedUpperStarUnitIso _
            (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom j) y) =
        c • P m x y) :
    ∃ P' : ((WeilSheaf.adicConstant k₀ l Y).cohomology i).carrier →ₗ[PadicAlgCl l]
        ((WeilSheaf.adicConstant k₀ l Y).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P'.IsPerfPair ∧ ∀ x y, P' (((WeilSheaf.adicConstant k₀ l Y).cohomology i).frobenius x)
        (((WeilSheaf.adicConstant k₀ l Y).cohomology j).frobenius y) =
          algebraMap ℤ_[l] (PadicAlgCl l) c * P' x y := by
  obtain ⟨P₀, hP₀, hP₀F⟩ := exists_isPerfPair_adicConstantH_adicConstantHPullback l _
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso hfin i j c P hPl hPr hPF
  obtain ⟨Θi, hΘi⟩ := exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback
    (k₀ := k₀) (l := l) (Y := Y) i
  obtain ⟨Θj, hΘj⟩ := exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback
    (k₀ := k₀) (l := l) (Y := Y) j
  refine ⟨P₀.compl₁₂ Θi.symm.toLinearMap Θj.symm.toLinearMap, inferInstance, fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Θi.surjective x
  obtain ⟨y, rfl⟩ := Θj.surjective y
  rw [← hΘi, ← hΘj]
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact hP₀F x y

end WeilSheaf

end AlgebraicGeometry
