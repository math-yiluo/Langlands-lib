/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BlowupRestriction
public import WeilConjectures.TraceFormula.BlowupRestrictionCurve
public import WeilConjectures.RingTheory.BlowupChartData
public import WeilConjectures.RingTheory.BlowupChartRegularity
public import WeilConjectures.AlgebraicGeometry.RegularDivisorSpec
public import WeilConjectures.AlgebraicGeometry.RegularImmersionSpecQuotient
public import WeilConjectures.RingTheory.FiniteOverStrictlyHenselian

/-!
# The blown-up configuration in a chart

Let `R` be a local ring with a chart `R[T]/(xT - y)` of the blow-up of `T = Spec R` at its closed
point as in `AlgebraicGeometry.BlowupChartData` (`f = x^d f'`, `h = x h'`). Put
`Z = Spec (R[T]/(xT - y))[1/f']`, `Y = V(x) ⊆ Z` (the exceptional divisor off the strict transform
`D'` of `D = V(f)`) and `X = V(h') ⊆ Z` (the strict transform of `H = V(h)`). This file constructs
the transverse configuration of blueprint `lemma-vanishing-restrictions-after-blowing-up--1`, in the
chart:

* `X`, `Y` are regular divisors of `Z` meeting transversely at one point, `Y` is connected
  (`lemma-vanishing-restrictions-after-blowing-up--1` (1));
* the blow-up map restricts to `φ : Z - Y ⟶ T - D` with `φ⁻¹(T - (D ∪ H)) = Z - (X ∪ Y)`
  (`lemma-vanishing-restrictions-after-blowing-up--1` (2), (3); in the chart, `φ` is an isomorphism
  onto `T - (D ∪ V(x))`).

## Main definitions

- `AlgebraicGeometry.BlowupChartData.φ`: the blow-up map `Z - Y ⟶ T - D`.
- `AlgebraicGeometry.BlowupChartData.φU`: its restriction `Z - (X ∪ Y) ⟶ T - (D ∪ H)`.

## Main results

- `AlgebraicGeometry.BlowupChartData.isPullback_φ`: `φ⁻¹(T - (D ∪ H)) = Z - (X ∪ Y)`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.BlowupChartData

variable {R : Type u} [CommRing R] [IsLocalRing R] {f g h x₀ y₀ : R} {K : Type v} {c : K → R}
  (D : BlowupChartData f g h x₀ y₀ c)

/-- A point `y` of `V` lies in the image of `U ⊆ V` iff it lies in `U`. -/
lemma mem_range_homOfLE {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V) (y : V) :
    y ∈ Set.range (X.homOfLE e) ↔ y.1 ∈ U :=
  ⟨by rintro ⟨x, rfl⟩; simp, fun hy ↦ ⟨⟨y.1, hy⟩, Subtype.ext (by simp)⟩⟩

/-- The parameter `x = x₀ + c i y₀` of the chart. -/
abbrev x : R := x₀ + c D.i * y₀

/-- The coordinate ring `(R[T]/(xT - y))[1/f']` of `Z`, the chart minus the strict transform of
`D`. -/
abbrev Rx : Type u := Localization.Away D.f'

/-- The equation `x` of the exceptional divisor `Y` on `Z`. -/
noncomputable abbrev xx : D.Rx := algebraMap R D.Rx D.x

/-- The equation `h'` of the strict transform `X` of `H` on `Z`. -/
noncomputable abbrev hh : D.Rx := algebraMap (blowupChart D.x y₀) D.Rx D.h'

/-- `Z - Y`, the basic open of `x`. -/
noncomputable abbrev UY : (Spec (.of D.Rx)).Opens := PrimeSpectrum.basicOpen D.xx

/-- `Z - (X ∪ Y)`, the basic open of `x h'`. -/
noncomputable abbrev UXY : (Spec (.of D.Rx)).Opens := PrimeSpectrum.basicOpen (D.xx * D.hh)

lemma UXY_le_UY : D.UXY ≤ D.UY := PrimeSpectrum.basicOpen_mul_le_left _ _

/-- The image of `f` on `Z` is `x^d` times a unit. -/
lemma algebraMap_f_eq : algebraMap R D.Rx f = D.xx ^ D.d * algebraMap _ D.Rx D.f' := by
  rw [IsScalarTower.algebraMap_apply R (blowupChart D.x y₀) D.Rx, D.algebraMap_f, map_mul,
    map_pow, ← IsScalarTower.algebraMap_apply]

/-- The image of `h` on `Z` is `x h'`. -/
lemma algebraMap_h_eq : algebraMap R D.Rx h = D.xx * D.hh := by
  rw [IsScalarTower.algebraMap_apply R (blowupChart D.x y₀) D.Rx, D.algebraMap_h, map_mul,
    ← IsScalarTower.algebraMap_apply]

lemma isUnit_f' : IsUnit (algebraMap (blowupChart D.x y₀) D.Rx D.f') :=
  IsLocalization.Away.algebraMap_isUnit _

/-- The blow-up map sends `Z - Y` into `T - D`. -/
lemma range_subset_basicOpen_f :
    Set.range (D.UY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx))) ⊆
      Set.range (Scheme.specBasicOpen (R := .of R) f).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f ∉ Ideal.comap (algebraMap R D.Rx) p.val.asIdeal
  rw [Ideal.mem_comap, D.algebraMap_f_eq]
  intro hp
  rcases p.val.isPrime.mem_or_mem hp with hx | hu
  · exact p.2 (p.val.isPrime.mem_of_pow_mem _ hx)
  · exact p.val.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu D.isUnit_f')

/-- The blow-up map `φ : Z - Y ⟶ T - D`. -/
noncomputable def φ : D.UY.toScheme ⟶ (Scheme.specBasicOpen (R := .of R) f).toScheme :=
  IsOpenImmersion.lift _ _ D.range_subset_basicOpen_f

@[reassoc (attr := simp)]
lemma φ_ι : D.φ ≫ (Scheme.specBasicOpen (R := .of R) f).ι =
    D.UY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The blow-up map sends `Z - (X ∪ Y)` into `T - (D ∪ H)`. -/
lemma range_subset_basicOpen_fh :
    Set.range (D.UXY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx))) ⊆
      Set.range (Scheme.specBasicOpen (R := .of R) (f * h)).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f * h ∉ Ideal.comap (algebraMap R D.Rx) p.val.asIdeal
  rw [Ideal.mem_comap, map_mul, D.algebraMap_f_eq, D.algebraMap_h_eq]
  intro hp
  have hxh : D.xx * D.hh ∉ p.val.asIdeal := p.2
  rcases p.val.isPrime.mem_or_mem hp with hp | hp
  · rcases p.val.isPrime.mem_or_mem hp with hx | hu
    · exact hxh (Ideal.mul_mem_right _ _ (p.val.isPrime.mem_of_pow_mem _ hx))
    · exact p.val.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu D.isUnit_f')
  · exact hxh hp

/-- The restriction `φU : Z - (X ∪ Y) ⟶ T - (D ∪ H)` of the blow-up map. -/
noncomputable def φU : D.UXY.toScheme ⟶ (Scheme.specBasicOpen (R := .of R) (f * h)).toScheme :=
  IsOpenImmersion.lift _ _ D.range_subset_basicOpen_fh

@[reassoc (attr := simp)]
lemma φU_ι : D.φU ≫ (Scheme.specBasicOpen (R := .of R) (f * h)).ι =
    D.UXY.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.Rx)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- `φ⁻¹(T - (D ∪ H)) = Z - (X ∪ Y)` (blueprint `lemma-vanishing-restrictions-after-blowing-up--1`
(2)). -/
lemma isPullback_φ :
    IsPullback D.φU ((Spec (.of D.Rx)).homOfLE D.UXY_le_UY)
      ((Spec (.of R)).homOfLE (PrimeSpectrum.basicOpen_mul_le_left f h)) D.φ := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · have hle : (Spec (.of R)).homOfLE (PrimeSpectrum.basicOpen_mul_le_left f h) ≫
        (Scheme.specBasicOpen (R := .of R) f).ι = (Scheme.specBasicOpen (R := .of R) (f * h)).ι :=
      Scheme.homOfLE_ι _ _
    rw [← cancel_mono (Scheme.specBasicOpen (R := .of R) f).ι]
    simp [hle]
  · ext p
    change D.φ p ∈ Set.range ((Spec (.of R)).homOfLE _) ↔
      p ∈ Set.range ((Spec (.of D.Rx)).homOfLE D.UXY_le_UY)
    rw [mem_range_homOfLE, mem_range_homOfLE]
    have hφp : (D.φ p).1 = Spec.map (CommRingCat.ofHom (algebraMap R D.Rx)) p.1 := by
      rw [← Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, D.φ_ι, Scheme.Hom.comp_apply]
      rfl
    rw [hφp]
    change f * h ∉ Ideal.comap (algebraMap R D.Rx) p.val.asIdeal ↔ D.xx * D.hh ∉ p.val.asIdeal
    have hx : D.xx ∉ p.val.asIdeal := p.2
    rw [Ideal.mem_comap, map_mul, D.algebraMap_f_eq, D.algebraMap_h_eq, not_iff_not]
    constructor
    · intro hp
      rcases p.val.isPrime.mem_or_mem hp with hp | hp
      · rcases p.val.isPrime.mem_or_mem hp with hx' | hu
        · exact absurd (p.val.isPrime.mem_of_pow_mem _ hx') hx
        · exact absurd (Ideal.eq_top_of_isUnit_mem _ hu D.isUnit_f') p.val.isPrime.ne_top
      · exact hp
    · intro hp
      exact Ideal.mul_mem_left _ _ hp

section StrictTransform

variable [Fact (g ∈ maximalIdeal R)]

/-- The image `x̄` of the parameter `x` in the coordinate ring `A = R/(g)` of the curve `B`. -/
noncomputable abbrev xA : R ⧸ Ideal.span {g} := Ideal.Quotient.mk _ D.x

/-- Since `B ∩ V(x) = {t}`, the punctured curve `B - t` is the basic open `D(x̄)` of `B`. -/
lemma range_puncturedSpec_eq (hx : D.x ∈ maximalIdeal R) :
    Set.range (Scheme.puncturedSpec (R ⧸ Ideal.span {g})).ι =
      Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ Ideal.span {g}) (Localization.Away D.xA)))) := by
  rw [Scheme.Opens.range_ι]
  change _ = Set.range (PrimeSpectrum.comap (algebraMap (R ⧸ Ideal.span {g})
    (Localization.Away D.xA)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away D.xA) D.xA]
  ext p
  change p ≠ IsLocalRing.closedPoint _ ↔ D.xA ∉ p.asIdeal
  constructor
  · intro hp hxp
    apply hp
    have hg : g ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {g})) p.asIdeal := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self g)]
      exact zero_mem _
    have hspan :
        Ideal.span {D.x, g} ≤ Ideal.comap (Ideal.Quotient.mk (Ideal.span {g})) p.asIdeal := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hxp, hg⟩
    have hm : maximalIdeal R ≤ Ideal.comap (Ideal.Quotient.mk (Ideal.span {g})) p.asIdeal :=
      D.maximalIdeal_le_radical.trans ((Ideal.radical_mono hspan).trans
        (Ideal.IsPrime.comap _).radical.le)
    refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) ?_)
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hm ((mem_maximalIdeal r).2 fun hu ↦ ((mem_maximalIdeal _).1 ha) (hu.map _))
  · rintro hxp rfl
    have := (Ideal.Quotient.mk_surjective (I := Ideal.span {g})).isLocalHom
    exact hxp ((mem_maximalIdeal _).2 fun hu ↦ (mem_maximalIdeal _).1 hx
      (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu))

/-- The isomorphism `B - t ≅ Spec A[1/x̄]`. -/
noncomputable def puncturedSpecIso (hx : D.x ∈ maximalIdeal R) :
    (Scheme.puncturedSpec (R ⧸ Ideal.span {g})).toScheme ≅
      Spec (.of (Localization.Away D.xA)) :=
  IsOpenImmersion.isoOfRangeEq _ _ (D.range_puncturedSpec_eq hx)

end StrictTransform


end AlgebraicGeometry.BlowupChartData

namespace AlgebraicGeometry.Etale

open BlowupChartData

/-- **The blowup restriction vanishing in a separating chart** (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1`, with
`lemma-vanishing-restrictions-after-blowing-up--1` and
`lemma-vanishing-restrictions-after-blowing-up--1` carried out in the chart `D` of the blow-up of
`T = Spec R` at its closed point). Let `R` be a henselian local `k`-algebra with algebraically
closed residue field, with a separating chart `D` whose open part `Z = Spec (R[T]/(xT - y))[1/f']`
is an étale limit of smooth `k`-surfaces. Then for every complex `E` with finite `ℓ`-group monodromy
on `T - (D ∪ H) = D(fh)`, the restriction map `RΓ(T - D, i_! E) ⟶ RΓ(B - t, (i_! E)|_{B - t})` is
zero.

The configuration `(Z, X, Y)` with the blow-up map `φ : Z - Y ⟶ T - D` is a transverse boundary
configuration (`lemma-vanishing-restrictions-after-blowing-up--1`), and the map `B - t ⟶ T - D`
factors through `Z - Y` and, inside `Z`, through the strict transform `B' = Spec A'` of `B`, a
finite disjoint union of strictly local schemes centred on `Y`
(`lemma-vanishing-restrictions-after-blowing-up--1`); so the restriction vanishes by
`AlgebraicGeometry.Etale.globalSectionsRestriction_eq_zero_of_transverse`. -/
theorem blowupRestriction_eq_zero_of_chartData {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (hΛ : IsNilpotent (ℓ : Λ)) {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsRegularLocalRing R] [IsAlgClosed (ResidueField R)] [Algebra k R] {f g h x₀ y₀ : R}
    [Fact (g ∈ maximalIdeal R)]
    (hfg : maximalIdeal R ≤ (Ideal.span {f, g}).radical)
    (D : BlowupChartData f g h x₀ y₀ (algebraMap k R)) (hx : D.x ∈ maximalIdeal R)
    (hm : maximalIdeal R = Ideal.span {D.x, y₀})
    (hlim : IsEtaleLimitOfSmoothSurfaces
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k D.Rx)))))
    (E : DerivedCategory (Sheaf
      (Scheme.specBasicOpen (R := .of R) (f * h)).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) :
    globalSectionsRestriction (Scheme.puncturedCurveMap hfg)
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        ((Spec (.of R)).homOfLE (PrimeSpectrum.basicOpen_mul_le_left f h))).mapDerivedCategory.obj
          E) = 0 := by
  classical
  have := D.isRegularRing_quotient_x
  have := D.isRegularRing_quotient_h'
  have := D.isDomain_quotient_x
  let Z : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k D.Rx)))
  let iY : Spec (.of (D.Rx ⧸ Ideal.span {D.xx})) ⟶ Z.left :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
  let iX : Spec (.of (D.Rx ⧸ Ideal.span {D.hh})) ⟶ Z.left :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
  have hY : IsRegularDivisor iY := isRegularDivisor_specMap_quotient D.x_mem_nonZeroDivisors
  have hX : IsRegularDivisor iX := isRegularDivisor_specMap_quotient D.h'_mem_nonZeroDivisors
  have hfield : IsField (D.Rx ⧸ Ideal.span {D.hh, D.xx}) := by
    rw [Set.pair_comm]
    exact D.isField_quotient
  let z : Spec (.of D.Rx) :=
    ⟨Ideal.span {D.hh, D.xx}, (Ideal.Quotient.maximal_of_isField _ hfield).isPrime⟩
  have hz : MeetTransverselyAt iX iY z := meetTransverselyAt_specMap_quotient hfield z rfl
  have : IsRegularRing D.Rx := D.isRegularRing_localization
  have : IsRegular Z.left := isRegular_spec (S := D.Rx)
  have : IsLocallyNoetherian Z.left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of D.Rx)))
  have hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX) :=
    isRegularImmersion_pullback_fst_specMap_quotient (D.isWeaklyRegular hm)
  have hUY : (D.UY : Set (Spec (.of D.Rx))) = (Set.range iY)ᶜ := by
    simp only [iY]
    erw [Etale.range_specMap_quotientMk]
    rw [PrimeSpectrum.zeroLocus_span]
    exact PrimeSpectrum.basicOpen_eq_zeroLocus_compl _
  have hUXY : (D.UXY : Set (Spec (.of D.Rx))) = (Set.range iX ∪ Set.range iY)ᶜ := by
    simp only [iX, iY]
    erw [Etale.range_specMap_quotientMk, Etale.range_specMap_quotientMk]
    rw [PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.zeroLocus_span, Set.union_comm, ← PrimeSpectrum.zeroLocus_singleton_mul]
    exact PrimeSpectrum.basicOpen_eq_zeroLocus_compl _
  let : Algebra R D.A' :=
    ((algebraMap (R ⧸ Ideal.span {g}) D.A').comp (Ideal.Quotient.mk _)).toAlgebra
  have : IsScalarTower R (R ⧸ Ideal.span {g}) D.A' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R D.A' := Module.Finite.trans (R ⧸ Ideal.span {g}) D.A'
  obtain ⟨J, _, A, _, _, _, hsurj, ⟨e⟩⟩ := exists_algEquiv_pi_isStrictlyHenselianLocalRing R D.A'
  let ρ : D.Rx →+* ∀ j, A j := e.toRingHom.comp D.toA'
  let c : Spec (.of (∀ j, A j)) ⟶ Z.left := Spec.map (CommRingCat.ofHom ρ)
  have hρR : ∀ r : R, ρ (algebraMap R D.Rx r) = algebraMap R (∀ j, A j) r := by
    intro r
    change e (D.toA' (algebraMap R D.Rx r)) = _
    rw [D.toA'_algebraMap]
    exact e.commutes r
  have hρx : ρ D.xx = e (algebraMap (R ⧸ Ideal.span {g}) D.A' D.xA) := by
    change e (D.toA' (algebraMap R D.Rx D.x)) = _
    rw [D.toA'_algebraMap]
  have hevsurj : ∀ j, Function.Surjective ((Pi.evalRingHom A j).comp e.toRingHom) :=
    fun j ↦ (Function.surjective_eval j).comp e.surjective
  have hmem : ∀ j, Pi.evalRingHom A j (ρ D.xx) ∈ maximalIdeal (A j) := by
    intro j
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot]
    intro b
    obtain ⟨b', rfl⟩ := hevsurj j b
    have hb := (Ideal.mem_jacobson_bot.1 D.mem_jacobson) b'
    rw [hρx]
    simpa using hb.map ((Pi.evalRingHom A j).comp e.toRingHom)
  let φj : ∀ j, D.Rx ⧸ Ideal.span {D.xx} →+* ResidueField (A j) := fun j ↦
    Ideal.Quotient.lift _ ((IsLocalRing.residue (A j)).comp ((Pi.evalRingHom A j).comp ρ))
      (fun a ha ↦ by
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
        simp only [RingHom.comp_apply, map_mul]
        rw [(IsLocalRing.residue_eq_zero_iff _).2 (hmem j), mul_zero])
  have hφsurj : ∀ j, Function.Surjective (φj j) := by
    intro j a
    obtain ⟨r, hr⟩ := hsurj j a
    refine ⟨Ideal.Quotient.mk _ (algebraMap R D.Rx r), ?_⟩
    simp only [φj, Ideal.Quotient.lift_mk, RingHom.comp_apply, hρR]
    exact hr
  let s : ∀ j, Spec (.of (D.Rx ⧸ Ideal.span {D.xx})) := fun j ↦
    Spec.map (CommRingCat.ofHom (φj j)) (IsLocalRing.closedPoint (ResidueField (A j)))
  have hs : ∀ j, IsClosed ({s j} : Set (Spec (.of (D.Rx ⧸ Ideal.span {D.xx})))) := by
    intro j
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    change (Ideal.comap (φj j) (maximalIdeal _)).IsMaximal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    exact RingHom.ker_isMaximal_of_surjective _ (hφsurj j)
  have hcs : ∀ j, (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A j)) ≫ c)
      (IsLocalRing.closedPoint (A j)) = iY (s j) := by
    intro j
    rw [← Scheme.closedGeometricPoint_apply (IsLocalRing.closedPoint (ResidueField (A j))),
      ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp only [iY, c, Scheme.closedGeometricPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have := D.isLocalization_A'
  let ε : Localization.Away D.xA ≃ₐ[R ⧸ Ideal.span {g}]
      Localization.Away (algebraMap (R ⧸ Ideal.span {g}) D.A' D.xA) :=
    IsLocalization.algEquiv (Submonoid.powers D.xA) _ _
  let θ : (∀ j, A j) →+* Localization.Away D.xA := ε.symm.toRingHom.comp
    ((algebraMap D.A' (Localization.Away (algebraMap (R ⧸ Ideal.span {g}) D.A' D.xA))).comp
      e.symm.toRingHom)
  have hθρ : ∀ r : R, θ (ρ (algebraMap R D.Rx r)) =
      algebraMap (R ⧸ Ideal.span {g}) (Localization.Away D.xA) (Ideal.Quotient.mk _ r) := by
    intro r
    change ε.symm (algebraMap _ _ (e.symm (e (D.toA' (algebraMap R D.Rx r))))) = _
    rw [AlgEquiv.symm_apply_apply, D.toA'_algebraMap, ← IsScalarTower.algebraMap_apply]
    exact ε.symm.commutes _
  have hθx : IsUnit (θ (ρ D.xx)) := by
    rw [hθρ]
    exact IsLocalization.Away.algebraMap_isUnit _
  let jW := (D.puncturedSpecIso hx).hom ≫ Spec.map (CommRingCat.ofHom θ)
  have hrange : Set.range (jW ≫ c) ⊆ Set.range D.UY.ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    change D.xx ∉ Ideal.comap ρ (Ideal.comap θ (((D.puncturedSpecIso hx).hom q).asIdeal))
    rw [Ideal.mem_comap, Ideal.mem_comap]
    exact fun hq ↦ (((D.puncturedSpecIso hx).hom q).isPrime).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hq hθx)
  let ι : (Scheme.puncturedSpec (R ⧸ Ideal.span {g})).toScheme ⟶ D.UY.toScheme :=
    IsOpenImmersion.lift _ _ hrange
  have hι : ι ≫ D.UY.ι = jW ≫ c := IsOpenImmersion.lift_fac _ _ _
  have hψ : Scheme.puncturedCurveMap hfg = ι ≫ D.φ := by
    rw [← cancel_mono (Scheme.specBasicOpen (R := .of R) f).ι, Category.assoc, D.φ_ι,
      reassoc_of% hι, Scheme.puncturedCurveMap, IsOpenImmersion.lift_fac]
    simp only [jW, c, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (Scheme.puncturedSpec _).ι
      (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {g}) (Localization.Away D.xA))))
      (D.range_puncturedSpec_eq hx), Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext r
    exact (hθρ r).symm
  exact globalSectionsRestriction_eq_zero_of_transverse hℓ hΛ hlim hX hY z hz hXY hUY hUXY
    D.UXY_le_UY _ E hE D.φ D.φU D.isPullback_φ _ A c s hs hcs ι jW hι hψ

end AlgebraicGeometry.Etale
