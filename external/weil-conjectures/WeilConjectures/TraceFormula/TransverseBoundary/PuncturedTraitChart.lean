/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineChartBaseChange
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersionStalk
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartPresentation
public import WeilConjectures.AlgebraicGeometry.StrictLocalizationFieldExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.StrictHenselizationTrait
public import WeilConjectures.RingTheory.StrictlyHenselianQuotient
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerConstant

/-!
# The punctured trait of a transverse corner

Let `S` be the strict localization of the surface `Z` of a transverse corner at a geometric
point `z̄` over the corner point `z` (with `Ω` separably closed), `X_S, Y_S` the two
divisors and `X_S - z = X_S ∩ (S - Y_S)` the punctured trait. Through an affine chart
`W = Spec R` of `Z` around `z` on which `Y` is cut out by `t ∈ R`, the strict localization is
`Spec A` with `A` the strict henselization of `R_z` (Stacks, Tag 04HX), and

- `S - Y_S = Spec A_t`,
- `X_S = Spec B` with `B = A ⧸ I_X A` the strict henselization of the local ring of `X` at `z`
  (Stacks, Tag 05WS): a strictly henselian discrete valuation ring, with uniformizer `t` since
  `X` and `Y` meet transversely,
- `X_S - z = Spec B_t = Spec K`, with `K` the fraction field of `B`.

This is the part "the punctured trait" of the proof of blueprint
`lemma-punctured-surface-punctured-curve--1`.

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.exists_puncturedTrait_iso_spec_fractionRing`
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k)

/-- An affine chart around the corner point on which the divisor `Y` is principal. -/
lemma exists_affineOpen_ker_iY_eq_span :
    ∃ (W : C.Z.affineOpens) (t : Γ(C.Z, W.1)), C.z ∈ W.1 ∧
      C.iY.ker.ideal W = Ideal.span {t} := by
  obtain ⟨W, hzW, r, hr, -, hI⟩ :=
    IsRegularImmersion.exists_isWeaklyRegular_generators (c := 1) (i := C.iY) C.z
  obtain ⟨t, rfl⟩ := List.length_eq_one_iff.1 hr
  refine ⟨W, t, hzW, ?_⟩
  rw [← hI]
  simp [Ideal.ofList]

/-- On an affine chart `W` on which `Y` is cut out by `t`, the complement `Z - Y` meets `W` in
the basic open of `t`. -/
lemma range_j_inter_eq_basicOpen (W : C.Z.affineOpens) (t : Γ(C.Z, W.1))
    (ht : C.iY.ker.ideal W = Ideal.span {t}) :
    Set.range C.j ∩ (W : Set C.Z) = C.Z.basicOpen t := by
  ext x
  rw [C.range_j]
  constructor
  · rintro ⟨hxY, hxW⟩
    rw [Set.mem_compl_iff, IsClosedImmersion.mem_range_iff_mem_zeroLocus C.iY W hxW, ht,
      Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at hxY
    simpa using hxY
  · intro hx
    have hxW : x ∈ (W : Set C.Z) := C.Z.basicOpen_le t hx
    refine ⟨?_, hxW⟩
    rw [Set.mem_compl_iff, IsClosedImmersion.mem_range_iff_mem_zeroLocus C.iY W hxW, ht,
      Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    simpa using hx

/-- In `WithBot ℕ∞`, `d + 1 = 2` forces `d = 1`. -/
lemma _root_.WithBot.ENat.eq_one_of_add_one_eq_two {d : WithBot ℕ∞} (h : d + 1 = 2) : d = 1 := by
  induction d with
  | bot => simp at h
  | coe n =>
    have h' : n + 1 = 2 := by
      have h2 : ((n + 1 : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        exact h
      exact WithBot.coe_injective h2
    have hn : n ≠ ⊤ := by
      rintro rfl
      simp at h'
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hn
    have : m + 1 = 2 := by exact_mod_cast h'
    have hm : m = 1 := by omega
    subst hm
    rfl

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (zbar : Spec (.of Ω) ⟶ C.Z)

-- The computation of the iterated pullbacks through the chart is a long chain of rewrites.
/-- **The punctured trait is the spectrum of the fraction field of a strictly henselian
trait** (blueprint `lemma-punctured-surface-punctured-curve--1`, the punctured trait). For a
geometric point `z̄` over the corner point (with `Ω` algebraically closed) there are a strictly
henselian discrete valuation ring `B` with a ring map `k →+* B`, a uniformizer `π` of `B`, an
isomorphism `X_S - z ≅ Spec K` with `K` the fraction field of `B`, and a unit `u` on `S - Y_S` (a
local equation of `Y`) whose restriction to `X_S - z` is `π`. Moreover `S - Y_S` is connected. -/
theorem exists_puncturedTrait_iso_spec_fractionRing_of_isAlgClosed
    (hz : Set.range zbar = {C.z}) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : IsStrictlyHenselianLocalRing B) (_ : k →+* B) (π : B) (_ : Irreducible π)
      (e : C.puncturedTrait zbar ≅ Spec (.of (FractionRing B)))
      (u : Γ(C.puncturedStrictLocalization zbar, ⊤)ˣ),
      (C.puncturedTraitι zbar).appTop.hom u = e.hom.appTop.hom
        ((Scheme.ΓSpecIso (.of (FractionRing B))).inv.hom (algebraMap B (FractionRing B) π)) ∧
      ConnectedSpace (C.puncturedStrictLocalization zbar) := by
  classical
  obtain ⟨W, t, hzW, hYt⟩ := C.exists_affineOpen_ker_iY_eq_span
  have hzbar : Set.range zbar ⊆ Set.range W.2.fromSpec := by
    rw [hz, W.2.range_fromSpec, Set.singleton_subset_iff]
    exact hzW
  obtain ⟨xR, rfl⟩ : ∃ xR, xR ≫ W.2.fromSpec = zbar :=
    ⟨_, IsOpenImmersion.lift_fac W.2.fromSpec zbar hzbar⟩
  obtain ⟨q, hq, K', _, _, _, _, _, _, ρ, hρ, hbase, hH, hqx⟩ :=
    strictHenselizationRing_chart_presentation Γ(C.Z, W.1) W.2.fromSpec xR
  subst hqx
  -- the base change of `X` to `S`
  set J : Ideal (strictHenselization (xR ≫ W.2.fromSpec)) := (C.iX.ker.ideal W).map ρ.hom
  have hX := IsClosedImmersion.isPullback_specMap_fromSpec C.iX W ρ
  rw [hρ] at hX
  -- the base change of `Z - Y` to `S`
  obtain ⟨gU, hU⟩ := IsOpenImmersion.isPullback_specMap_away_fromSpec C.j W t
    (C.range_j_inter_eq_basicOpen W t hYt) ρ
  rw [hρ] at hU
  -- the affine model of the punctured trait
  set π : strictHenselization (xR ≫ W.2.fromSpec) ⧸ J := Ideal.Quotient.mk J (ρ.hom t)
  set Sm := Localization.Away π
  have hSm : IsLocalization ((Submonoid.powers (ρ.hom t)).map (Ideal.Quotient.mk J)) Sm := by
    rw [Submonoid.map_powers]
    infer_instance
  let fm : Localization.Away (ρ.hom t) →+* Sm :=
    IsLocalization.map Sm (Ideal.Quotient.mk J)
      (Submonoid.le_comap_map (Submonoid.powers (ρ.hom t)))
  have hfm : fm.comp (algebraMap _ (Localization.Away (ρ.hom t))) =
      (algebraMap (_ ⧸ J) Sm).comp (Ideal.Quotient.mk J) := IsLocalization.map_comp _
  have hK := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Ideal.Quotient.mk J) fm hfm
      (Submonoid.powers (ρ.hom t)))
  have hP := hX.pullback_snd_pullback_fst hU hK
  -- the points over the corner
  have hyz : W.2.fromSpec (xR (closedPoint Ω)) = C.z := by
    have h : (xR ≫ W.2.fromSpec) (closedPoint Ω) ∈ Set.range (xR ≫ W.2.fromSpec) := ⟨_, rfl⟩
    rw [hz] at h
    exact h
  have hzXY : C.z ∈ Set.range C.iX ∩ Set.range C.iY := by
    rw [C.range_inter]
    rfl
  obtain ⟨x, hx⟩ := hzXY.1
  obtain ⟨x', hx'⟩ := hzXY.2
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' (hx.trans hx'.symm)
  have : IsRegularImmersion 2 (pullback.fst C.iX C.iY ≫ C.iX) := C.isRegularImmersion_inter
  have hcw : (pullback.fst C.iX C.iY ≫ C.iX) w = C.iX x := by
    rw [Scheme.Hom.comp_apply, hw]
  -- the local ring of `X` at the corner
  obtain ⟨EX⟩ := IsClosedImmersion.nonempty_ringEquiv_stalk C.iX W _ x (hyz.trans hx.symm)
  obtain ⟨Ec⟩ := IsClosedImmersion.nonempty_ringEquiv_stalk (pullback.fst C.iX C.iY ≫ C.iX) W _ w
    ((hyz.trans hx.symm).trans hcw.symm)
  have : IsRegularLocalRing (Localization.AtPrime (xR (closedPoint Ω)).asIdeal ⧸
      (C.iX.ker.ideal W).map (algebraMap _ (Localization.AtPrime (xR (closedPoint Ω)).asIdeal))) :=
    IsRegularLocalRing.of_ringEquiv EX.symm
  have : Subsingleton ↥(pullback C.iX C.iY) := by
    refine ⟨fun p p' ↦ (pullback.fst C.iX C.iY ≫ C.iX).isClosedEmbedding.injective ?_⟩
    have hmem (p : ↥(pullback C.iX C.iY)) : (pullback.fst C.iX C.iY ≫ C.iX) p = C.z := by
      have h : (pullback.fst C.iX C.iY ≫ C.iX) p ∈ Set.range C.iX ∩ Set.range C.iY :=
        ⟨⟨_, rfl⟩, ⟨(pullback.snd C.iX C.iY : pullback C.iX C.iY ⟶ C.Y) p, by
          rw [← Scheme.Hom.comp_apply,
          ← pullback.condition]⟩⟩
      rw [C.range_inter] at h
      exact h
    rw [hmem p, hmem p']
  have hfield : IsField ((pullback C.iX C.iY).presheaf.stalk w) := by
    have : Ring.KrullDimLE 0 ((pullback C.iX C.iY).presheaf.stalk w) :=
      Scheme.krullDimLE_zero_stalk_of_subsingleton w
    exact Ring.KrullDimLE.isField_of_isDomain
  have hdim : ringKrullDim (Localization.AtPrime (xR (closedPoint Ω)).asIdeal ⧸
      (C.iX.ker.ideal W).map (algebraMap _ (Localization.AtPrime (xR (closedPoint Ω)).asIdeal)))
      = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv EX]
    have h₁ := (IsRegularImmersion.exists_isRegular_stalk_and_ringKrullDim 1 C.iX x).2
    have h₂ := (IsRegularImmersion.exists_isRegular_stalk_and_ringKrullDim 2
      (pullback.fst C.iX C.iY ≫ C.iX) w).2
    rw [hcw, h₁, ringKrullDim_eq_zero_of_isField hfield, zero_add] at h₂
    exact WithBot.ENat.eq_one_of_add_one_eq_two (by exact_mod_cast h₂)
  -- transversality: the maximal ideal of the local ring of `X` is generated by `t`
  have hker : (pullback.fst C.iX C.iY ≫ C.iX).ker.ideal W =
      C.iX.ker.ideal W ⊔ Ideal.span {t} := by
    rw [Scheme.Hom.ker_pullback_fst_comp, Scheme.IdealSheafData.ideal_sup, ← hYt]
    rfl
  have hmaxO :
      (C.iX.ker.ideal W).map (algebraMap _ (Localization.AtPrime (xR (closedPoint Ω)).asIdeal))
      ⊔ Ideal.span {algebraMap _ (Localization.AtPrime (xR (closedPoint Ω)).asIdeal) t} =
      maximalIdeal (Localization.AtPrime (xR (closedPoint Ω)).asIdeal) := by
    have hmax := Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hfield Ec.toMulEquiv)
    rw [hker, Ideal.map_sup, Ideal.map_span, Set.image_singleton] at hmax
    exact IsLocalRing.eq_maximalIdeal hmax
  have hJ : ((C.iX.ker.ideal W).map
      (algebraMap _ (Localization.AtPrime (xR (closedPoint Ω)).asIdeal))).map
      (algebraMap (Localization.AtPrime (xR (closedPoint Ω)).asIdeal)
        (strictHenselization (xR ≫ W.2.fromSpec))) = J := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact hbase r
  obtain ⟨_, _, hπ⟩ := hH.isDiscreteValuationRing_quotient _ hdim _
    (IsLocalRing.maximalIdeal_quotient_eq_span_singleton hmaxO) J hJ (ρ.hom t) (hbase t)
  have := ‹IsDomain (_ ⧸ J)›
  have hJle : J ≤ maximalIdeal (strictHenselization (xR ≫ W.2.fromSpec)) := by
    refine IsLocalRing.le_maximalIdeal fun h ↦ ?_
    have : Subsingleton (_ ⧸ J) := Ideal.Quotient.subsingleton_iff.2 h
    exact not_subsingleton _ this
  obtain ⟨_, -, -, hsh, -⟩ := isStrictlyHenselianLocalRing_quotient.{u, u} _ inferInstance J hJle
  have : IsFractionRing (_ ⧸ J) Sm :=
    IsDiscreteValuationRing.isFractionRing_of_isLocalization_away hπ
  let eK : Sm ≃ₐ[_ ⧸ J] FractionRing (_ ⧸ J) :=
    IsLocalization.algEquiv (nonZeroDivisors (_ ⧸ J)) Sm (FractionRing (_ ⧸ J))
  let eP := hP.isoPullback
  let φk : k →+* (_ ⧸ J) := (Ideal.Quotient.mk J).comp (ρ.hom.comp
    ((C.Z.presheaf.map (homOfLE le_top).op).hom.comp
      (C.aZ.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)))
  have hu₀ : IsUnit (algebraMap _ (Localization.Away (ρ.hom t)) (ρ.hom t)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let u : Γ(C.puncturedStrictLocalization (xR ≫ W.2.fromSpec), ⊤)ˣ :=
    ((hu₀.map (Scheme.ΓSpecIso (.of (Localization.Away (ρ.hom t)))).inv.hom).map
      hU.isoPullback.inv.appTop.hom).unit
  refine ⟨_ ⧸ J, inferInstance, inferInstance, inferInstance, hsh, φk, π, hπ,
    eP.symm ≪≫ Scheme.Spec.mapIso eK.symm.toRingEquiv.toCommRingCatIso.op, u, ?_, ?_⟩
  · have hnat {R S : CommRingCat.{u}} (f : R ⟶ S) (a : R) :
        (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv a) = (Scheme.ΓSpecIso S).inv (f a) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    have hι : C.puncturedTraitι (xR ≫ W.2.fromSpec) =
        eP.inv ≫ Spec.map (CommRingCat.ofHom fm) ≫ hU.isoPullback.hom := by
      rw [← hP.isoPullback_hom_snd, Iso.inv_hom_id_assoc]
    have hcancel {X Y : Scheme.{u}} (e : X ≅ Y) (a : Γ(X, ⊤)) :
        e.hom.appTop (e.inv.appTop a) = a := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id,
        Scheme.Hom.id_appTop, CommRingCat.id_apply]
    simp only [u, IsUnit.unit_spec, hι, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    simp only [hcancel]
    have hnat_fm := hnat (CommRingCat.ofHom fm)
    simp only [hnat_fm]
    have hnat_eK := hnat eK.symm.toRingEquiv.toCommRingCatIso.hom
    simp only [hnat_eK]
    congr 2
    exact (IsLocalization.map_eq (S := Localization.Away (ρ.hom t)) (Q := Sm)
      (Submonoid.le_comap_map _) (ρ.hom t)).trans (eK.symm.commutes π).symm
  · have hO : IsRegularLocalRing (Localization.AtPrime (xR (closedPoint Ω)).asIdeal) :=
      W.2.isRegularLocalRing_localization (fun _ _ ↦ inferInstance) _
    have := hH.isDomain_of_isRegularLocalRing hO
    have ht0 : ρ.hom t ≠ 0 := fun h ↦ hπ.ne_zero (by simp [h])
    have : IsDomain (Localization.Away (ρ.hom t)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _
        (Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero ht0))
    have : ConnectedSpace (Spec (.of (Localization.Away (ρ.hom t)))) :=
      inferInstanceAs (ConnectedSpace (PrimeSpectrum (Localization.Away (ρ.hom t))))
    exact (ConcreteCategory.bijective_of_isIso hU.isoPullback.hom.base).2.connectedSpace
      hU.isoPullback.hom.base.hom.continuous

omit [IsAlgClosed Ω] in
/-- **The punctured trait is the spectrum of the fraction field of a strictly henselian
trait** (blueprint `lemma-punctured-surface-punctured-curve--1`, the punctured trait). For a
geometric point `z̄` over the corner point (with `Ω` separably closed) there are a strictly
henselian discrete valuation ring `B` with a ring map `k →+* B`, a uniformizer `π` of `B`, an
isomorphism `X_S - z ≅ Spec K` with `K` the fraction field of `B`, and a unit `u` on `S - Y_S` (a
local equation of `Y`) whose restriction to `X_S - z` is `π`. Moreover `S - Y_S` is connected.

This reduces to the case of an algebraically closed `Ω`
(`exists_puncturedTrait_iso_spec_fractionRing_of_isAlgClosed`):
the strict localization does not change when `Ω` is replaced by its algebraic closure
(`AlgebraicGeometry.Scheme.exists_strictLocalization_iso_of_precomp`). -/
theorem exists_puncturedTrait_iso_spec_fractionRing [IsSepClosed Ω]
    (hz : Set.range zbar = {C.z}) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : IsStrictlyHenselianLocalRing B) (_ : k →+* B) (π : B) (_ : Irreducible π)
      (e : C.puncturedTrait zbar ≅ Spec (.of (FractionRing B)))
      (u : Γ(C.puncturedStrictLocalization zbar, ⊤)ˣ),
      (C.puncturedTraitι zbar).appTop.hom u = e.hom.appTop.hom
        ((Scheme.ΓSpecIso (.of (FractionRing B))).inv.hom (algebraMap B (FractionRing B) π)) ∧
      ConnectedSpace (C.puncturedStrictLocalization zbar) := by
  let a : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  obtain ⟨σ, hσ⟩ := exists_strictLocalization_iso_of_precomp zbar a
  have hz' : Set.range (a ≫ zbar) = {C.z} := by
    have hpt : Set.range a.base = Set.univ := Set.eq_univ_of_forall fun x ↦
      ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hpt, Set.image_univ, hz]
  obtain ⟨B, _, _, _, hsh, φ, π, hπ, e, u, hu, hconn⟩ :=
    C.exists_puncturedTrait_iso_spec_fractionRing_of_isAlgClosed (a ≫ zbar) hz'
  let mU : C.puncturedStrictLocalization (a ≫ zbar) ≅ C.puncturedStrictLocalization zbar :=
    asIso (pullback.map C.j (strictLocalizationToBase (a ≫ zbar)) C.j
      (strictLocalizationToBase zbar) (𝟙 _) σ.hom (𝟙 _) (by simp) (by simp [hσ]))
  let mP : C.puncturedTrait (a ≫ zbar) ≅ C.puncturedTrait zbar :=
    asIso (pullback.map (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase
      (a ≫ zbar))) (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar))
      (𝟙 _) mU.hom (𝟙 _) (by simp) (by simp [mU]))
  have hmι : C.puncturedTraitι zbar ≫ mU.inv = mP.inv ≫ C.puncturedTraitι (a ≫ zbar) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact pullback.lift_snd _ _ _
  refine ⟨B, inferInstance, inferInstance, inferInstance, hsh, φ, π, hπ, mP.symm ≪≫ e,
    Units.map (mU.inv.appTop.hom : _ →* _) u, ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply, ← hu, Units.coe_map, MonoidHom.coe_ofClass, ← RingHom.comp_apply,
      ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hmι, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply]
  · exact (ConcreteCategory.bijective_of_isIso mU.hom.base).2.connectedSpace
      mU.hom.base.hom.continuous

end AlgebraicGeometry.Scheme.TransverseCorner
