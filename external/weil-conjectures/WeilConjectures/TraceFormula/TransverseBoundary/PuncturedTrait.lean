/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.AlgebraicGeometry.Sites.HenselianTraitCohomology
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.TraceFormula.TransverseBoundary.PuncturedTraitChart

/-!
# The cohomology of the punctured trait at a transverse corner

Let `S` be the strict localization of the surface of a transverse corner at a geometric point
`z̄` over the corner point (with `Ω` separably closed), and `X_S - z ⟶ S - Y_S` the
punctured trait. For a prime `ℓ` invertible in the algebraically closed base field `k`:

- `H^q(X_S - z, ℤ/ℓ) = 0` for `q ≥ 2` and `H^q(X_S - z, ℤ/ℓ) ≅ ℤ/ℓ` for `q ≤ 1`: the punctured
  trait is the spectrum of the fraction field `K` of a strictly henselian discrete valuation ring
  (`AlgebraicGeometry.Scheme.TransverseCorner.exists_puncturedTrait_iso_spec_fractionRing`), and
  the étale cohomology of `Spec K` is the Galois cohomology of `K`;
- the restriction `H⁰(S - Y_S, ℤ/ℓ) ⟶ H⁰(X_S - z, ℤ/ℓ)` is bijective, both schemes being
  connected;
- the restriction `H¹(S - Y_S, ℤ/ℓ) ⟶ H¹(X_S - z, ℤ/ℓ)` is nonzero: the Kummer class of a local
  equation of `Y_S` restricts to the Kummer class of a uniformizer of `X_S`, which is not an
  `ℓ`-th power in `K`.

These are the parts "the punctured trait" and "the restriction" of the proof of blueprint
`lemma-punctured-surface-punctured-curve--1`.

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.subsingleton_sheafH_puncturedTrait`
- `AlgebraicGeometry.Scheme.TransverseCorner.nonempty_addEquiv_sheafH_puncturedTrait`
- `AlgebraicGeometry.Scheme.TransverseCorner.bijective_cohomologyMap_zero_puncturedTraitι`
- `AlgebraicGeometry.Scheme.TransverseCorner.cohomologyMap_one_puncturedTraitι_ne_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- Isomorphic schemes have isomorphic étale cohomology with coefficients in `ℤ/n`. -/
noncomputable def sheafHConstantZModAddEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) (n q : ℕ) :
    Sheaf.H (X.constantZMod n) q ≃+ Sheaf.H (Y.constantZMod n) q :=
  let c := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} e.hom).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))
  ((Etale.cohomologyEquiv e.hom (Y.constantZMod n) q).trans
    { toFun := Sheaf.H.map c.hom q
      invFun := Sheaf.H.map c.inv q
      left_inv x := by rw [← Sheaf.H.map_comp_apply, c.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv x := by rw [← Sheaf.H.map_comp_apply, c.inv_hom_id, Sheaf.H.map_id_apply]
      map_add' := map_add _ }).symm

/-- **Kummer classes detect nonvanishing of `H¹` restriction maps.** Let `g : X ⟶ Y` be a
morphism of schemes, `f : Y ⟶ Spec k` a structure map to a field in which `n` is nonzero and
which contains a primitive `n`-th root of unity, and `a` a unit on `Y` whose pullback to `X` is
not an `n`-th power. Then the restriction `H¹(Y, ℤ/n) ⟶ H¹(X, g^* ℤ/n)` is nonzero: through
`ℤ/n ≅ μₙ`, the Kummer class of `a` restricts to the Kummer class of `g^* a`, which is nonzero
(blueprint `lemma-punctured-surface-punctured-curve--1`). -/
theorem Etale.cohomologyMap_one_constantZMod_ne_zero_of_forall_pow_ne {k : Type u} [Field k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) {n : ℕ} [NeZero n]
    (hn : (n : k) ≠ 0) {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a : Γ(Y, ⊤)ˣ)
    (ha : ∀ v : Γ(X, ⊤), v ^ n ≠ g.appTop.hom a) :
    Etale.cohomologyMap g (Y.constantZMod n) 1 ≠ 0 := by
  have hY : IsUnit (n : Γ(Y, ⊤)) := AffineSpace.isUnit_natCast_of_ne_zero f hn
  have hX : IsUnit (n : Γ(X, ⊤)) := AffineSpace.isUnit_natCast_of_ne_zero (g ≫ f) hn
  let θ := Y.constantZModIsoRootsOfUnitySheaf n f hζ
  intro h0
  have hx : Etale.cohomologyMap g (Y.constantZMod n) 1
      (Sheaf.H.map θ.inv 1 (Y.kummerδ₀ n hY (Additive.ofMul a))) = 0 := by
    rw [h0]
    rfl
  rw [Etale.cohomologyMap_map] at hx
  have hx' := congrArg (Sheaf.H.map (((g)^*[AddCommGrpCat.{u + 1}]).map θ.hom) 1) hx
  rw [← Sheaf.H.map_comp_apply, ← Functor.map_comp, θ.inv_hom_id,
    CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply, map_zero] at hx'
  have hδ := Scheme.sheafH_map_cohomologyMap_kummerδ₀ g n hY hX a
  rw [hx', map_zero] at hδ
  have hker : Additive.ofMul (Units.map g.appTop.hom a) ∈ (X.kummerδ₀ n hX).ker := hδ.symm
  rw [(X.exact_sheafH_rootsOfUnitySheaf_one n hX).1] at hker
  obtain ⟨v, hv⟩ := hker
  refine ha ((Additive.toMul v : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ?_
  have := congrArg (fun b ↦ ((Additive.toMul b : Γ(X, ⊤)ˣ) : Γ(X, ⊤))) hv
  simpa using this

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.TransverseCorner

/-- The residue field of a local ring receiving a ring map from a field `k` in which `n` is
nonzero has `n` nonzero. -/
lemma natCast_residueField_ne_zero {k B : Type*} [Field k] [CommRing B] [IsLocalRing B]
    (φ : k →+* B) {n : ℕ} (hn : (n : k) ≠ 0) : (n : ResidueField B) ≠ 0 := by
  have h : IsUnit (n : B) := by
    rw [← map_natCast φ]
    exact (isUnit_iff_ne_zero.2 hn).map φ
  rw [← map_natCast (IsLocalRing.residue B)]
  exact (h.map (IsLocalRing.residue B)).ne_zero

variable {k : Type u} [Field k] (C : TransverseCorner k) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

variable {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hz : Set.range zbar = {C.z})

include hz in
/-- The punctured trait `X_S - z` is connected: it is the spectrum of a field. -/
lemma connectedSpace_puncturedTrait : ConnectedSpace (C.puncturedTrait zbar) := by
  obtain ⟨B, _, _, _, _, -, -, -, e, -, -, -⟩ :=
    C.exists_puncturedTrait_iso_spec_fractionRing zbar hz
  have : ConnectedSpace (Spec (.of (FractionRing B))) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (FractionRing B)))
  exact (ConcreteCategory.bijective_of_isIso e.inv.base).2.connectedSpace
    e.inv.base.hom.continuous

include hz in
/-- The punctured strict localization `S - Y_S` is connected. -/
lemma connectedSpace_puncturedStrictLocalization :
    ConnectedSpace (C.puncturedStrictLocalization zbar) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    C.exists_puncturedTrait_iso_spec_fractionRing zbar hz
  exact h

include hℓ hz

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`: `H^q(X_S - z, ℤ/ℓ) = 0` for `q ≥ 2`. -/
theorem subsingleton_sheafH_puncturedTrait (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H ((C.puncturedTrait zbar).constantZMod ℓ) q) := by
  obtain ⟨B, _, _, _, _, φ, -, -, e, -, -, -⟩ :=
    C.exists_puncturedTrait_iso_spec_fractionRing zbar hz
  have := IsDiscreteValuationRing.subsingleton_sheafH_constantZMod_spec_of_isFractionRing
    (FractionRing B) (natCast_residueField_ne_zero φ hℓ) q hq
  exact (sheafHConstantZModAddEquivOfIso e ℓ q).toEquiv.subsingleton

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`: `H^0(X_S - z, ℤ/ℓ)` and
`H^1(X_S - z, ℤ/ℓ) ≅ 𝔽_ℓ(-1)` are free of rank one over `𝔽_ℓ`. -/
theorem nonempty_addEquiv_sheafH_puncturedTrait (q : ℕ) (hq : q ≤ 1) :
    Nonempty (Sheaf.H ((C.puncturedTrait zbar).constantZMod ℓ) q ≃+ ZMod ℓ) := by
  interval_cases q
  · have := C.connectedSpace_puncturedTrait zbar hz
    exact (C.puncturedTrait zbar).nonempty_addEquiv_sheafH_zero_constantZMod ℓ
  · obtain ⟨B, _, _, _, _, φ, -, -, e, -, -, -⟩ :=
      C.exists_puncturedTrait_iso_spec_fractionRing zbar hz
    obtain ⟨f⟩ :=
      IsDiscreteValuationRing.nonempty_addEquiv_sheafH_one_constantZMod_spec_of_isFractionRing
        (FractionRing B) (natCast_residueField_ne_zero φ hℓ)
    exact ⟨(sheafHConstantZModAddEquivOfIso e ℓ 1).trans f⟩

omit hℓ in
/-- Blueprint `lemma-punctured-surface-punctured-curve--1`, *the restriction* in degree `0`: both
`S - Y_S` and `X_S - z` are connected, so the restriction of the constants is bijective. -/
theorem bijective_cohomologyMap_zero_puncturedTraitι :
    Function.Bijective
      (Etale.cohomologyMap (C.puncturedTraitι zbar)
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ) 0) := by
  have := C.connectedSpace_puncturedTrait zbar hz
  have := C.connectedSpace_puncturedStrictLocalization zbar hz
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact bijective_cohomologyMap_zero_constantZMod _ ℓ

/-- Blueprint `lemma-punctured-surface-punctured-curve--1`, *the restriction* in degree `1`: the
Kummer class of a local equation of `Y_S` restricts to the Kummer class of a uniformizer of `X_S`,
which is nonzero, so the restriction map is nonzero. -/
theorem cohomologyMap_one_puncturedTraitι_ne_zero [IsAlgClosed k] :
    Etale.cohomologyMap (C.puncturedTraitι zbar)
      ((C.puncturedStrictLocalization zbar).constantZMod ℓ) 1 ≠ 0 := by
  obtain ⟨B, _, _, _, _, -, π, hπ, e, u, hu, -⟩ :=
    C.exists_puncturedTrait_iso_spec_fractionRing zbar hz
  have : NeZero (ℓ : k) := ⟨hℓ⟩
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k ℓ
  refine Etale.cohomologyMap_one_constantZMod_ne_zero_of_forall_pow_ne (n := ℓ)
    (C.puncturedTraitι zbar) (pullback.fst _ _ ≫ C.j ≫ C.aZ) hℓ hζ u fun v hv ↦ ?_
  rw [hu] at hv
  refine IsDiscreteValuationRing.not_exists_pow_eq_algebraMap (F := FractionRing B) (ℓ := ℓ) hπ
    ⟨(Scheme.ΓSpecIso (.of (FractionRing B))).hom (e.inv.appTop v), ?_⟩
  have hinv (a : Γ(Spec (.of (FractionRing B)), ⊤)) : e.inv.appTop (e.hom.appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
  rw [← map_pow, ← map_pow, hv, hinv, Iso.inv_hom_id_apply]

end AlgebraicGeometry.Scheme.TransverseCorner
