/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve.Boundary
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZero
public import WeilConjectures.WeilSheaf.CohomologicalRange
public import WeilConjectures.WeilSheaf.LFunction

/-!
# Compactly supported cohomology of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀` over a finite field, a lisse Weil sheaf
has no compactly supported cohomology in degree zero: a compactly supported global section of a
lisse sheaf is locally constant, so its support is open and closed, hence empty or all of the
connected curve `U`, which is not proper.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`: `H_c⁰ = 0`.
- `AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_eq`: the Euler product of the
  `L`-function is `det (1 - F T ∣ H_c¹) / det (1 - F T ∣ H_c²)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

open ProEtale

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

attribute [local instance] Compactification.over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology `H_c⁰(U ⊗ k̄, F)` vanishes as soon as the global sections
`Γ(Z̄, ī_! F)` of the extension by zero of `F` to the chosen compactification `ī : Ū ⟶ Z̄` vanish:
`H_c⁰ = Γ(Spec k̄, 𝓗⁰(Rḡ_* ī_! F)) ≅ Γ(Spec k̄, ḡ_* ī_! F) ≅ Γ(Z̄, ī_! F)`. -/
theorem subsingleton_compactlySupportedCohomology_zero_of_isZero (F : WeilSheaf k₀ l U)
    (h : Limits.IsZero ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((Scheme.Hom.geometricFiberMap
        (HasCompactification.compactification (U ↘ Spec (CommRingCat.of k₀))
          (hf := hasCompactification_of_over (k₀ := k₀) (U ↘ Spec (CommRingCat.of k₀)))).i
        (comp_over _ _))_!ᵃ[l].obj F.obj.carrier).X)) :
    Subsingleton (F.compactlySupportedCohomology 0).carrier := by
  set c := HasCompactification.compactification (U ↘ Spec (CommRingCat.of k₀))
      (hf := hasCompactification_of_over (k₀ := k₀) (U ↘ Spec (CommRingCat.of k₀)))
  let P := ProEtaleWeilSheaf.lowerStar k₀ l c.g
  let E := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
  let e₁ : (_root_.DerivedCategory.homologyFunctor _ 0).obj
      (P.rightDerivedFunctor.obj (E.mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj))) ≅ P.obj (E.obj F.obj) :=
    (_root_.DerivedCategory.homologyFunctor _ 0).mapIso
      (P.rightDerivedFunctor.mapIso ((E.mapDerivedCategorySingleFunctor 0).app F.obj)) ≪≫
      P.homologyRightDerivedFunctorObjSingleFunctorIso (E.obj F.obj) 0 ≪≫
      P.rightDerivedZeroIsoSelf.app _
  let G : ProEtaleWeilSheaf k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilCoefficients.{u} l :=
    Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l)
  let e : G.obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj
      (P.rightDerivedFunctor.obj (E.mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)))) ≅
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((Scheme.Hom.geometricFiberMap c.i (comp_over _ _))_!ᵃ[l].obj F.obj.carrier).X :=
    G.mapIso e₁ ≪≫ (ProEtale.globalSectionsLowerStarIso _
      (Scheme.Hom.geometricFiberMap c.g (comp_over _ _))).app _
  exact ModuleCat.subsingleton_of_isZero
    ((WeilCoefficients.toModuleCat l).map_isZero (h.of_iso e))

/-- **Vanishing of `H_c⁰` on a nonproper curve.**

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`.
Then `H_c⁰ (U, ℱ) = 0`.

`H_c⁰` is the space of global sections of `ī_! ℱ` on the compactification `ī : U ⟶ Z`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isZero`). The
affine curve `U` is not proper, so a boundary point `z ∈ Z ∖ U` is a specialization of a point of
`U` (`AlgebraicGeometry.exists_specializes_notMem_range_of_isProper`). A global section of
`ī_! ℱ` vanishes near `z`, hence has a vanishing stalk at a geometric point of `U`; by lissity it
vanishes on the connected curve `U`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek`).
-/
theorem subsingleton_compactlySupportedCohomology_zero [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Subsingleton (F.compactlySupportedCohomology 0).carrier := by
  refine subsingleton_compactlySupportedCohomology_zero_of_isZero F ?_
  set c := HasCompactification.compactification (U ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) (U ↘ Spec (CommRingCat.of k₀)))
  set p := (U ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set q := (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set i := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  have : IsProper c.g := c.isProper
  have : IsProper (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    change IsProper (c.g ≫ _)
    infer_instance
  have : IsProper q := inferInstanceAs (IsProper (Limits.pullback.snd _ _))
  have : GeometricallyConnected p :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd _ _))
  have : ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IsAffineHom p := inferInstanceAs (IsAffineHom (Limits.pullback.snd _ _))
  have : IsAffine (U ↘ Spec (CommRingCat.of k₀)).geometricFiber := isAffine_of_isAffineHom p
  have : SmoothOfRelativeDimension (0 + 1) (i ≫ q) := by
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
    exact inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd _ _))
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian (U ↘ Spec (CommRingCat.of k₀)).geometricFiber := ⟨⟩
  obtain ⟨x, z, hz, hxz⟩ := exists_specializes_notMem_range_of_isProper i q 0
  exact ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek i hF hz hxz

/-- The compactly supported cohomology of a lisse Weil sheaf on a smooth geometrically
connected affine curve vanishes outside degrees `1` and `2`. -/
theorem subsingleton_compactlySupportedCohomology_of_notMem [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) {i : ℤ} (hi : i ∉ ({1, 2} : Finset ℤ)) :
    Subsingleton (F.compactlySupportedCohomology i).carrier := by
  rw [Finset.mem_insert, Finset.mem_singleton] at hi
  obtain rfl | hi' : i = 0 ∨ i < 0 ∨ 2 < i := by omega
  · exact subsingleton_compactlySupportedCohomology_zero F hF
  · rcases hi' with hi' | hi'
    · exact subsingleton_compactlySupportedCohomology_of_neg F hi'
    · exact subsingleton_compactlySupportedCohomology_of_isLisse hF hi'

open PowerSeries in
/-- **Euler product of the `L`-function of a lisse sheaf.**

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`.
Then, as power series in `T`,

`∏_{x ∈ |U₀|} det (1 - F_x T ^ {e_x} ∣ ℱ_x̄)⁻¹ = det (1 - F T ∣ H_c¹) / det (1 - F T ∣ H_c²)`,

the product over the closed points being locally finite: for every `n`, the coefficient of
`T ^ n` of the finite product over any finite set `s` of closed points containing those of
degree at most `n` is the coefficient of `T ^ n` of the right-hand side. This is the
Euler-product form of the trace formula for `ℱ` placed in degree zero, whose compactly supported
cohomology is concentrated in degrees `0, 1, 2`, together with `H_c⁰ (U, ℱ) = 0`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`). -/
theorem coeff_prod_inv_localPolynomial_stalk_eq [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) (n : ℕ) (s : Finset U.finitePoints)
    (hs : ∀ x : U.finitePoints, (U ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (((F.stalk x).localPolynomial.comp
        (Polynomial.X ^ (U ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial _) :
          (PadicAlgCl l)⟦X⟧)⁻¹) =
      coeff n (((F.compactlySupportedCohomology 1).localPolynomial : (PadicAlgCl l)⟦X⟧) *
        ((F.compactlySupportedCohomology 2).localPolynomial : (PadicAlgCl l)⟦X⟧)⁻¹) := by
  rw [coeff_prod_inv_localPolynomial_stalk F
    (fun i hi ↦ subsingleton_compactlySupportedCohomology_of_notMem F hF hi) n s hs,
    LinearMap.alternatingCharpolyRevProd, Finset.prod_pair (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide), pow_one, Polynomial.comp_X, Polynomial.comp_X]
  congr 1
  simp only [FrobeniusModule.localPolynomial]
  have h₁ : constantCoeff
      ((F.compactlySupportedCohomology 1).frobeniusEnd.charpolyRev : (PadicAlgCl l)⟦X⟧) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      LinearMap.coeff_zero_charpolyRev]
    exact one_ne_zero
  have h₂ : constantCoeff
      ((F.compactlySupportedCohomology 2).frobeniusEnd.charpolyRev : (PadicAlgCl l)⟦X⟧) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      LinearMap.coeff_zero_charpolyRev]
    exact one_ne_zero
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp), mul_mul_mul_comm,
    PowerSeries.mul_inv_cancel _ h₁, PowerSeries.inv_mul_cancel _ h₂, one_mul]

end WeilSheaf

end AlgebraicGeometry
