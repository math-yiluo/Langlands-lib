/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Stalks of the direct image along an open immersion at points of the open

Let `j : U₀ ⟶ X₀` be a quasi-compact open immersion of `k₀`-schemes locally of finite type and
`F` a Weil sheaf on `U₀`. The counit `j^* j_* F ⟶ F` is an isomorphism, so at a closed point `y`
of `U₀` the stalk of `j_* F` at `j y` is the stalk of `F` at `y`, with the same local Frobenius.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage`: the stalk of `j_* F` at a
  point of `U₀`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The stalk with its Frobenius relative to `𝔽_{qᵐ}` only depends on `m`, not on the proof of
the fixed-point property. -/
theorem nonempty_equiv_stalkAt_of_eq {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {m m' : ℕ} (h : m = m')
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m').asIso.hom =
      (specGeometricFrobenius k₀ ^ m').asIso.hom ≫ s) :
    Nonempty ((G.stalkAt s m hs).Equiv (G.stalkAt s m' hs')) := by
  subst h
  exact ⟨.refl _⟩

/-- **The direct image along an open immersion does not change the stalks on the open.** For a
quasi-compact open immersion `j : U₀ ⟶ X₀` of `k₀`-schemes locally of finite type, a Weil sheaf
`F` on `U₀` and a closed point `y` of `U₀`, the stalk of `j_* F` at `j y` is the stalk of `F`
at `y`, Frobenius-equivariantly: the counit `j^* j_* F ⟶ F` is an isomorphism, and the stalk of
`j^* j_* F` at `y` is that of `j_* F` at `j y`. -/
theorem nonempty_equiv_stalk_directImage {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (y : U.finitePoints) (x : X.finitePoints) (hxy : j.base y.1 = x.1) :
    Nonempty ((((directImage j).obj F).stalk x).Equiv (F.stalk y)) := by
  have hj := comp_over j (Spec (CommRingCat.of k₀))
  -- the counit `j^* j_* F ≅ F`
  let e : (upperStar j).obj ((lowerStar j).obj F) ≅ F :=
    eqToIso (Functor.comp_obj _ _ F).symm ≪≫
      asIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit.app F) ≪≫
        eqToIso (Functor.id_obj F)
  -- the closed points `y` and `x = j y` have the same degree over `k₀`
  have hdeg : (U ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 =
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 := by
    rw [← hxy, ← Scheme.Hom.degreeOver_comp_of_isIso j (X ↘ Spec (CommRingCat.of k₀)) y.1, hj]
  set s := (U ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (U ↘ Spec (CommRingCat.of k₀)) y
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap j hj) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (U ↘ Spec (CommRingCat.of k₀)).degreeOver y.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (U ↘ Spec (CommRingCat.of k₀)).degreeOver y.1).asIso.hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap j hj) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have ht'' : (s ≫ Scheme.Hom.geometricFiberMap j hj) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap j hj) := hdeg ▸ ht'
  -- the stalk of `j^* j_* F` at `y` is the stalk of `j_* F` at `s ≫ j̄`
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap j hj)^*[WeilCoefficients.{u} l].obj
      ((lowerStar j).obj F).obj.carrier.X ⟶
        ((upperStar j).obj ((lowerStar j).obj F)).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap j hj)^*[WeilCoefficients.{u} l].obj
      ((lowerStar j).obj F).obj.carrier.X)))
  obtain ⟨e₂⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (upperStar j).obj ((lowerStar j).obj F))
    (θ := 𝟙 _) (upperStar_frobeniusStr_compatible (φ := j) ((lowerStar j).obj F)) s _ ht ht'
  -- the geometric points over `x`: the chosen one and `s ≫ j̄`
  have hx₁ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (X ↘ Spec (CommRingCat.of k₀)) x
  have hss' : ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ Scheme.Hom.geometricFiberMap j hj) ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hx₁, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, Scheme.Hom.comp_base, TopCat.comp_app,
      Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base, hxy]
  obtain ⟨e₃⟩ := ((lowerStar j).obj F).nonempty_equiv_stalkAt _ _ hss' (hx₁ ▸ x.2) _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x) ht''
  obtain ⟨e₄⟩ := ((lowerStar j).obj F).nonempty_equiv_stalkAt_of_eq _ hdeg.symm ht'' ht'
  obtain ⟨e₅⟩ := nonempty_equiv_stalk_of_iso e y
  exact ⟨((e₃.trans e₄).trans e₂).trans e₅⟩

end AlgebraicGeometry.WeilSheaf
