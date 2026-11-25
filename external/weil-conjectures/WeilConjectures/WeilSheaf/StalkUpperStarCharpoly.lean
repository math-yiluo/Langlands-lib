/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Characteristic polynomials of the stalks of a pullback

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, a Weil sheaf `F` on `Y` and a closed point `z` of
`X` over `x = φ z`, the local Frobenius of `φ^* F` at `z` has the characteristic polynomial of
the `r`-th power of the local Frobenius of `F` at `x`, `r = [κ(z) : κ(x)]`
(`AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar`). In particular, when
`φ` induces an isomorphism of residue fields at `z`, for instance for an immersion, the two local
Frobenius have the same characteristic polynomial.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y)

/-- At a closed point `z` of `X` over `x = φ z`, the local Frobenius of `φ^* F` has the
characteristic polynomial of the `r`-th power of the local Frobenius of `F` at `x`, with
`r = [κ(z) : k₀] / [κ(x) : k₀]`. -/
theorem charpoly_frobeniusEnd_stalk_upperStar (z : X.finitePoints) :
    (((upperStar φ).obj F).stalk z).frobeniusEnd.charpoly =
      ((F.stalk ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩).frobeniusEnd ^
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
          (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z.1))).charpoly := by
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  set x : Y.finitePoints := ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩
  have hdvd : (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    have := Scheme.Hom.degreeOver_dvd_degreeOver_comp φ (Y ↘ Spec (CommRingCat.of k₀)) z.2
    rwa [hφ] at this
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) z
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X ⟶ ((WeilSheaf.upperStar φ).obj F).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X)))
  obtain ⟨e₁⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (WeilSheaf.upperStar φ).obj F) (θ := 𝟙 _)
    (upperStar_frobeniusStr_compatible (φ := φ) F) s _ ht ht'
  have hbase : (((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x
  have hss' : (((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg φ.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hc := F.charpoly_frobeniusEnd_stalkAt_of_dvd _ _ hss' (hbase ▸ x.2) hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ x) ht'
  exact e₁.charpoly_frobeniusEnd.trans hc

end AlgebraicGeometry.WeilSheaf
