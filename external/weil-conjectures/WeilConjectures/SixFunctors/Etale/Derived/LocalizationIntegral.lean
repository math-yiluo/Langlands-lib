/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-!
# The closed-support triangle on `Dᵇc(-, 𝒪_E)`

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on a field `k`: the integral stage `Λ = 𝒪_E`, `I = 𝔪_E` of the `ℓ`-adic
formalism. The category `Dᵇc(X, Λ)` is
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral I X`: the objects of
`D(X_ét, Λ)` which are derived complete for `I` and whose reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` are bounded
constructible of Tor amplitude in one common interval.

This file proves the ingredients of clauses (1)–(4) and (1')–(4') of blueprint
`lemma-local-cohomology-right-adjoint--2` at the integral stage, for a closed immersion `i : Z ⟶ X`
and the complementary quasi-compact open immersion `j : U ⟶ X` of schemes of finite type over `k`:
the stability of `Dᵇc(-, Λ)` under the operations, its triangulated structure, the supported
localization triangle on `D(X_ét, Λ)`, and the closed-support triangle on `Dᵇc(-, Λ)` under the
hypotheses providing an exceptional adjunction `Ri_! ⊣ Ri^!` on `D(X_ét, Λ)`. The right adjoint
of `i_*` on `Dᵇc(-, Λ)` without those hypotheses is constructed in
`WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isTriangulated_boundedConstructibleIntegral`:
  `Dᵇc(X, Λ)` is a triangulated subcategory of `D(X_ét, Λ)`.
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerStar_obj`: `Rf_*`
  preserves `Dᵇc(-, Λ)` (clause (1)).
- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_of_rightDerivedLowerStar_obj`: `Ri_*`
  detects `Dᵇc(-, Λ)`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_reductionModIdeal_of_distTriang`: the Tor amplitude
  bound of clause (2').
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_localizationIntegral
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ}

/-! ### Tor amplitude and closure properties -/

section Triangulated

section TorAmplitude

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- Tor amplitude is closed under extensions, with the interval widened: if `T` is distinguished
and `T.obj₁`, `T.obj₃` have Tor amplitude in `[a, b]` and `[c, d]`, then `T.obj₂` has Tor
amplitude in `[min a c, max b d]`. -/
lemma DerivedCategory.torAmplitudeIn_obj₂
    {T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))} (hT : T ∈ distTriang _)
    {a b c d : ℤ} (h₁ : DerivedCategory.torAmplitudeIn A X a b T.obj₁)
    (h₃ : DerivedCategory.torAmplitudeIn A X c d T.obj₃) :
    DerivedCategory.torAmplitudeIn A X (min a c) (max b d) T.obj₂ :=
  fun F ↦ by
    let G := (-⊗ᴸ-(X)[A]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨g₁, l₁⟩ := (h₁ F).mono (min_le_left a c) (le_max_left b d)
    obtain ⟨g₃, l₃⟩ := (h₃ F).mono (min_le_right a c) (le_max_right b d)
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

end TorAmplitude

variable {X : Scheme.{u}}

/-- The reductions of a zero object of `D(X_ét, Λ)` have Tor amplitude in any interval. -/
lemma DerivedCategory.torAmplitudeIn_reductionModIdeal_of_isZero {K : 𝐃(X, Λ)} (hK : IsZero K)
    (J : Ideal Λ) (a b : ℤ) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      ((reductionModIdeal Λ X J).obj K) := fun F ↦
  have hG := isZero_derivedTensor_obj_obj_of_isZero_left ((reductionModIdeal Λ X J).map_isZero hK)
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  ⟨_root_.DerivedCategory.TStructure.t.isGE_of_isZero hG a,
    _root_.DerivedCategory.TStructure.t.isLE_of_isZero hG b⟩

/-- The reductions of a shift: if the reduction of `K` modulo `J` is bounded constructible of
Tor amplitude in `[a, b]`, then that of `K⟦m⟧` is bounded constructible of Tor amplitude in
`[a - m, b - m]`. -/
lemma DerivedCategory.boundedConstructible_and_torAmplitudeIn_reductionModIdeal_shift
    {K : 𝐃(X, Λ)} (J : Ideal Λ) (m : ℤ) {a b : ℤ}
    (h : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X J).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X J).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X J).obj (K⟦m⟧)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - m) (b - m)
        ((reductionModIdeal Λ X J).obj (K⟦m⟧)) := by
  have e := ((reductionModIdeal Λ X J).commShiftIso m).app K
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e.symm
      ((DerivedCategory.boundedConstructible _ X).le_shift m _ h.1),
    (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e.symm
      (DerivedCategory.torAmplitudeIn.shift h.2 m)⟩

/-- Derived completeness for `I = (ϖ)` is stable under the shifts. -/
lemma _root_.DerivedCategory.derivedComplete_shift (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (hI : I = Ideal.span {ϖ}) {K : 𝐃(X, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K) (m : ℤ) :
    _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I (K⟦m⟧) :=
  have := _root_.DerivedCategory.isTriangulated_derivedComplete
    (J := X.smallEtaleTopology) hϖ hI
  (_root_.DerivedCategory.derivedComplete _ I).le_shift m K hK

/-- `Dᵇc(X, Λ)` is stable under the shifts.
Blueprint `lemma-local-cohomology-right-adjoint--2` (integral stage `𝒪_E`). -/
lemma DerivedCategory.isStableUnderShift_boundedConstructibleIntegral
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).IsStableUnderShift ℤ where
  isStableUnderShiftBy m := ⟨fun _ hK ↦
    ⟨_root_.DerivedCategory.derivedComplete_shift hϖ hI hK.1 m, hK.2.choose - m,
      hK.2.choose_spec.choose - m, fun n ↦
        boundedConstructible_and_torAmplitudeIn_reductionModIdeal_shift _ m
          (hK.2.choose_spec.choose_spec n)⟩⟩

open ZeroObject in
/-- `Dᵇc(X, Λ)` contains the zero object.
Blueprint `lemma-local-cohomology-right-adjoint--2` (integral stage `𝒪_E`). -/
lemma DerivedCategory.containsZero_boundedConstructibleIntegral (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).ContainsZero := by
  have := _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete (X := X) hϖ hI
  have := _root_.DerivedCategory.isTriangulated_derivedComplete
    (J := X.smallEtaleTopology) hϖ hI
  exact ⟨⟨0, isZero_zero _, (_root_.DerivedCategory.derivedComplete _ I).prop_of_isZero
    (isZero_zero _), 0, 0, fun _ ↦
      ⟨(DerivedCategory.boundedConstructible _ X).prop_of_isZero
        ((reductionModIdeal Λ X _).map_isZero (isZero_zero _)),
      torAmplitudeIn_reductionModIdeal_of_isZero (isZero_zero _) _ 0 0⟩⟩⟩

variable [IsNoetherianRing Λ] [Finite (Λ ⧸ I)]

/-- `Dᵇc(X, Λ)` is closed under extensions, for `Λ` noetherian and `Λ ⧸ I` finite: the reduction
of a distinguished triangle modulo `Iⁿ⁺¹` is distinguished, its middle vertex is killed by `Iⁿ⁺¹`
and `Λ ⧸ Iⁿ⁺¹` is finite, so it is bounded constructible
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero`); and the
Tor amplitude interval is widened.
Blueprint `lemma-local-cohomology-right-adjoint--2` (integral stage `𝒪_E`). -/
lemma DerivedCategory.isTriangulatedClosed₂_boundedConstructibleIntegral
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).IsTriangulatedClosed₂ := by
  have := _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete (X := X) hϖ hI
  have := DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral (X := X) hϖ hI
  have := _root_.DerivedCategory.isTriangulated_derivedComplete
    (J := X.smallEtaleTopology) hϖ hI
  refine .mk' fun T hT ⟨hc₁, a, b, h₁⟩ ⟨hc₃, c, d, h₃⟩ ↦
    ⟨(_root_.DerivedCategory.derivedComplete _ I).ext_of_isTriangulatedClosed₂ T hT hc₁ hc₃,
      min a c, max b d, fun n ↦ ?_⟩
  have hT' := (reductionModIdeal Λ X (I ^ (n + 1))).map_distinguished T hT
  have : Finite (Λ ⧸ I ^ (n + 1)) := Ideal.finite_quotient_pow (IsNoetherian.noetherian I) _
  exact ⟨DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero hT' (h₁ n).1 (h₃ n).1
      fun r hr ↦ smul_id_reductionModIdeal hr _,
    DerivedCategory.torAmplitudeIn_obj₂ _ hT' (h₁ n).2 (h₃ n).2⟩

/-- `Dᵇc(X, Λ)` is a triangulated subcategory of `D(X_ét, Λ)`, for `I = (ϖ)` with `ϖ` a
nonzerodivisor, `Λ` noetherian and `Λ ⧸ I` finite: derived complete objects form a triangulated
subcategory (`DerivedCategory.isTriangulated_derivedComplete`), the reductions are triangulated
functors whose values are killed by `Iⁿ⁺¹`, bounded constructible complexes are closed under such
extensions, and Tor amplitude is stable under shifts and, with the interval widened, under
extensions.
Blueprint `lemma-local-cohomology-right-adjoint--2` (integral stage `𝒪_E`). -/
lemma DerivedCategory.isTriangulated_boundedConstructibleIntegral_of_eq_span
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).IsTriangulated :=
  have := DerivedCategory.containsZero_boundedConstructibleIntegral (X := X) hϖ hI
  have := DerivedCategory.isStableUnderShift_boundedConstructibleIntegral (X := X) hϖ hI
  have := DerivedCategory.isTriangulatedClosed₂_boundedConstructibleIntegral (X := X) hϖ hI
  {}

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, integral stage `𝒪_E`: `Dᵇc(X, Λ)` is a
triangulated subcategory of `D(X_ét, Λ)` when `I = (ϖ)` for a nonzerodivisor `ϖ`
(`DerivedCategory.isTriangulated_boundedConstructibleIntegral_of_eq_span`). The hypothesis on `I`
is recorded as a `Fact`, so that this is an instance. -/
instance DerivedCategory.isTriangulated_boundedConstructibleIntegral
    [h : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})] :
    (DerivedCategory.boundedConstructibleIntegral I X).IsTriangulated :=
  have ⟨_, hϖ, hI⟩ := h.out
  DerivedCategory.isTriangulated_boundedConstructibleIntegral_of_eq_span hϖ hI

end Triangulated

/-! ### Derived completeness through adjunctions

An object is derived complete for `I = (ϖ)` exactly when it receives no nonzero map from an
object on which `ϖ` acts invertibly (`DerivedCategory.derivedComplete_iff_rightOrthogonal`). A
right adjoint of a `Λ`-linear functor therefore preserves derived completeness. -/

section DerivedComplete

variable {X Y : Scheme.{u}} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

/-- A right adjoint `G` of a `Λ`-linear functor `F` between the derived categories of étale
sheaves of `Λ`-modules preserves derived completeness: a map `L ⟶ G K` from an object on which
`ϖ` acts invertibly corresponds to a map `F L ⟶ K`, and `ϖ` acts invertibly on `F L`. -/
lemma derivedComplete_obj_of_adjunction {F : 𝐃(Y, Λ) ⥤ 𝐃(X, Λ)} {G : 𝐃(X, Λ) ⥤ 𝐃(Y, Λ)}
    (adj : F ⊣ G) [F.Additive] [F.Linear Λ] {K : 𝐃(X, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I (G.obj K) := by
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI] at hK ⊢
  intro L f (hL : IsIso (ϖ • 𝟙 L))
  have : IsIso (ϖ • 𝟙 (F.obj L)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  have h₀ : (adj.homEquiv L K).symm f = 0 := hK _ this
  have : G.Additive := adj.right_adjoint_additive
  rw [← (adj.homEquiv L K).apply_symm_apply f, h₀, adj.homEquiv_apply, Functor.map_zero,
    Limits.comp_zero]

/-- `Rf_*` preserves derived completeness, being right adjoint to the `Λ`-linear `Lf^*`. -/
lemma derivedComplete_rightDerivedLowerStar_obj (f : X ⟶ Y) {K : 𝐃(X, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  derivedComplete_obj_of_adjunction hϖ hI
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f) hK

/-- `Rf^!` preserves derived completeness, being right adjoint to the `Λ`-linear `Rf_!`. -/
lemma derivedComplete_rightDerivedUpperShriek_obj (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {K : 𝐃(Y, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I
      ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj K) :=
  derivedComplete_obj_of_adjunction hϖ hI
    (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])) hK

/-- For an open immersion `j`, the pullback `Lj^*` preserves derived completeness, being right
adjoint to the `Λ`-linear extension by zero `D(j_!)`. -/
lemma derivedComplete_leftDerivedUpperStar_obj (j : X ⟶ Y) [IsOpenImmersion j] {K : 𝐃(Y, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  derivedComplete_obj_of_adjunction hϖ hI
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm) hK

/-- A faithful `Λ`-linear functor `F` between the derived categories of étale sheaves of
`Λ`-modules reflects derived completeness: a map `f : L ⟶ Q` from an object on which `ϖ` acts
invertibly is sent to a map `F L ⟶ F Q` from an object on which `ϖ` acts invertibly. -/
lemma derivedComplete_of_faithful {F : 𝐃(Y, Λ) ⥤ 𝐃(X, Λ)} [F.Faithful] [F.Additive]
    [F.Linear Λ] {Q : 𝐃(Y, Λ)}
    (hQ : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I (F.obj Q)) :
    _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I Q := by
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI] at hQ ⊢
  intro L f (hL : IsIso (ϖ • 𝟙 L))
  have : IsIso (ϖ • 𝟙 (F.obj L)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  exact F.map_injective (by rw [hQ (F.map f) this, F.map_zero])

end DerivedComplete

/-! ### The reductions of the operations -/

section Reductions

variable {X Y : Scheme.{u}} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the integral stage `𝒪_E`,
for `j^*`: for an open immersion `j`, the pullback `Lj^*` carries `Dᵇc(Y, Λ)` into `Dᵇc(X, Λ)`, and
the reductions keep their Tor amplitude interval. -/
theorem boundedConstructibleIntegral_leftDerivedUpperStar (j : X ⟶ Y) [IsOpenImmersion j]
    {K : 𝐃(Y, Λ)} (hK : DerivedCategory.boundedConstructibleIntegral I Y K) :
    DerivedCategory.boundedConstructibleIntegral I X ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hc, a, b, h⟩ := hK
  exact ⟨derivedComplete_leftDerivedUpperStar_obj hϖ hI j hc, a, b, fun n ↦
    boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar hϖ hI j n
      (h n)⟩

/-- For a closed immersion `i : Z ⟶ X`, an object `Q` of `D(Z_ét, Λ)` lies in `Dᵇc(Z, Λ)` as soon
as `Ri_* Q` lies in `Dᵇc(X, Λ)`: `Ri_*` is faithful and `Λ`-linear, so it reflects derived
completeness, and `Q ≅ i^* Ri_* Q`, whose reductions are the pullbacks of those of `Ri_* Q`.
Blueprint `lemma-local-cohomology-right-adjoint--2` (integral stage `𝒪_E`). -/
theorem boundedConstructibleIntegral_of_rightDerivedLowerStar_obj (i : X ⟶ Y)
    [IsClosedImmersion i] {Q : 𝐃(X, Λ)}
    (hQ : DerivedCategory.boundedConstructibleIntegral I Y
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj Q)) :
    DerivedCategory.boundedConstructibleIntegral I X Q := by
  obtain ⟨hc, a, b, h⟩ := hQ
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  refine ⟨derivedComplete_of_faithful hϖ hI hc, a, b, fun n ↦ ?_⟩
  have e := (reductionModIdeal Λ X (I ^ (n + 1))).mapIso (asIso (adj.counit.app Q))
  have h' := boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar hϖ hI
    i n (h n)
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e h'.1,
    (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e h'.2⟩

variable [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] {k : Type u} [Field k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY]

omit hϖ hI [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [LocallyOfFiniteType aY]
  [QuasiCompact aY] in
include aY in
/-- The reductions modulo `Iⁿ⁺¹` of the objects of `D(X_ét, Λ)` are killed by an integer lying
in `Iⁿ⁺¹` and invertible on `Y`. -/
lemma exists_nsmul_id_reductionModIdeal_eq_zero (n : ℕ) :
    ∃ N : ℕ, NeZero N ∧ (N : Λ) ∈ I ^ (n + 1) ∧ IsUnit (N : Γ(Y, ⊤)) ∧ ∀ K : 𝐃(X, Λ),
      N • 𝟙 ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) = 0 := by
  have : HasInvertibleExponent (Λ ⧸ I) Y := HasInvertibleExponent.of_hom aY
  obtain ⟨m, hm0, hmΛ, hmY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I) (X := Y)
  have hmI : (m : Λ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hmΛ
  refine ⟨m ^ (n + 1), ⟨pow_ne_zero _ hm0.ne'⟩,
    by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _,
    by rw [Nat.cast_pow]; exact hmY.pow _,
    fun K ↦ nsmul_id_reductionModIdeal (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _) K⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clauses (1) and (1') at the integral stage
`𝒪_E`: for a separated morphism `f : X ⟶ Y` of schemes of finite type over `k` with
`dim X ≤ d`, `Rf_*` carries `Dᵇc(X, Λ)` into `Dᵇc(Y, Λ)`, and if the reductions of `K` have Tor
amplitude in `[a, b]`, those of `Rf_* K` have Tor amplitude in `[a, b + 2d]`. The direct image
preserves derived completeness, commutes with the reductions, and the finite-level statements
are the finiteness theorem and the Tor amplitude bound for direct images
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`,
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`). -/
theorem boundedConstructibleIntegral_rightDerivedLowerStar (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ∧
      ∀ a b : ℤ, (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨hc, a₀, b₀, h₀⟩ := hK
  have key : ∀ (n : ℕ) (a b : ℤ),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) →
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
    intro n a b hbc hta
    obtain ⟨N, _, hNI, hNY, hN⟩ := exists_nsmul_id_reductionModIdeal_eq_zero (I := I) (X := X) aY n
    have : Finite (Λ ⧸ I ^ (n + 1)) := Ideal.finite_quotient_pow (IsNoetherian.noetherian I) _
    have hN' := hN K
    subst hI
    obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (R((f)_*[ModuleCat.{u + 1} Λ])) hϖ (n + 1) K
    exact ⟨(DerivedCategory.boundedConstructible _ Y).prop_of_iso e
        (boundedConstructible_rightDerivedLowerStar Λ _ aX aY f hf N hNI hNY
          (fun r hr ↦ smul_id_reductionModIdeal hr K) hbc),
      (DerivedCategory.torAmplitudeIn _ Y _ _).prop_of_iso e
        (torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing _ aX aY f hf d hd a b N hN' hNY
          hbc hta)⟩
  refine ⟨⟨derivedComplete_rightDerivedLowerStar_obj hϖ hI f hc, a₀, b₀ + 2 * (d : ℤ),
    fun n ↦ key n a₀ b₀ (h₀ n).1 (h₀ n).2⟩, fun a b hab n ↦ (key n a b (h₀ n).1 (hab n)).2⟩

end Reductions

/-! ### The ambient recollement data

The facts behind the supported localization triangle on the whole of `D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`), in the form used by
`CategoryTheory.Pretriangulated.Recollement`. -/

section Recollement

variable {U Z X : Scheme.{u}}

variable (Λ) in
/-- Blueprint `lem-exc-open-fully-faithful`, first half: for an open immersion `j`, the counit
`Lj^* Rj_* ⟶ 𝟭` is an isomorphism: `Rj_*` is fully faithful. In the adjoint triple
`D(j_!) ⊣ D(j^*) ⊣ Rj_*` the unit of the first adjunction is invertible, hence so is the counit
of the second. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit := by
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  have : IsIso adj.counit :=
    (Adjunction.Triple.mk
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      adj).isIso_unit_iff_isIso_counit.1 inferInstance
  have hff := adj.fullyFaithfulROfIsIsoCounit
  have := hff.full
  have := hff.faithful
  exact
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit_isIso_of_R_fully_faithful

variable (Λ) in
/-- The adjunction `Ri_* ⊣ Ri^!` for a closed immersion `i`: the exceptional adjunction
`Ri_! ⊣ Ri^!` transported along `Ri_! ≅ Ri_*`. -/
noncomputable def rightDerivedLowerStarUpperShriekAdjunction (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    R((i)_*[ModuleCat.{u + 1} Λ]) ⊣ (R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint :=
  (Adjunction.ofIsLeftAdjoint (R(i)_![ModuleCat.{u + 1} Λ])).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i)

/-- Blueprint `lem-exc-open-fully-faithful`, second half: `j^* i_* = 0` for an open immersion `j`
whose range is disjoint from that of the closed immersion `i`
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerivedLowerShriek`). -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj (i : Z ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) (M : 𝐃(Z, Λ)) :
    IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj M)) :=
  (isZero_upperStar_rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i j hij M).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _ ≪≫
      D((j)^*[ModuleCat.{u + 1} Λ]).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).app M).symm)

/-- An object `K` of `D(X_ét, Λ)` with `j^* K = 0` has invertible unit `K ⟶ Ri_* i^* K`, by the
open–closed triangle `j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶`
(`AlgebraicGeometry.Etale.exists_distTriang_openClosed`). -/
lemma isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {K : 𝐃(X, Λ)}
    (hK : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K) := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij K
  exact (Triangle.isZero₁_iff_isIso₂ _ hw).1 (D((j)_!open[ModuleCat.{u + 1} Λ]).map_isZero
    (hK.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K).symm))

/-- An object `K` of `D(X_ét, Λ)` with `j^* K = 0` lies in the essential image of `Ri_*`. -/
lemma rightDerivedLowerStar_essImage_of_isZero (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ) {K : 𝐃(X, Λ)}
    (hK : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (R((i)_*[ModuleCat.{u + 1} Λ])).essImage K :=
  have := isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero i j hij hK
  ⟨_, ⟨(asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
    K)).symm⟩⟩

end Recollement

/-! ### The exceptional inverse image on `Dᵇc(-, Λ)` -/

section UpperShriek

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}}

include hϖ hI in
/-- `Rf^!` carries `Dᵇc(Y, Λ)` into `Dᵇc(X, Λ)`, for a separated morphism `f` of separated
schemes of finite type over `k`: the image of the derived completion cone of `L` under `Rf^!` is
a homotopy limit of the tower `n ↦ Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)`, whose point lies in `Dᵇc(X, Λ)` by the
construction of the integral exceptional adjoint
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`). -/
theorem boundedConstructibleIntegral_rightDerivedUpperShriek
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.boundedConstructibleIntegral I Y L) :
    DerivedCategory.boundedConstructibleIntegral I X
      ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L) := by
  let adj := Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])
  have := adj.commShift_of_leftAdjoint ℤ
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive := adj.right_adjoint_additive
  exact (boundedConstructibleIntegral_exceptionalAdjoint I hϖ hI aX aY f hf hL
    (hL.1.map (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)).1.1

end UpperShriek

/-! ### The closed-support triangle at the integral stage -/

section Localization

variable {U Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

/-- The direct image `Ri_*` along a closed immersion is fully faithful on `D(Z_ét, Λ)`. -/
noncomputable def fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion :
    (R((i)_*[ModuleCat.{u + 1} Λ])).FullyFaithful :=
  .ofFullyFaithful _

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the integral stage `𝒪_E`, the
vanishing: `Hom((Ri_* Q)[m], Rj_* G) = 0` for all `Q ∈ D(Z_ét, Λ)` and `G ∈ D(U_ét, Λ)`, in
particular for `Q ∈ Dᵇc(Z, Λ)` and `G ∈ Dᵇc(U, Λ)`. -/
lemma subsingleton_hom_shift_rightDerivedLowerStar_rightDerivedLowerStar [HasCompactification i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (Q : 𝐃(Z, Λ)) (G : 𝐃(U, Λ)) (m : ℤ) :
    Subsingleton (((R((i)_*[ModuleCat.{u + 1} Λ])).obj Q)⟦m⟧ ⟶
      (R((j)_*[ModuleCat.{u + 1} Λ])).obj G) :=
  Recollement.subsingleton_hom_shift _ _ (derivedUpperStarLowerStarAdjunction _ j)
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i j (hij ▸ disjoint_compl_left))
    Q G m

variable [HasCompactification i] [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

/-- The supported localization triangle `Ri_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (Ri_* Ri^! K)[1]` on
`D(X_ét, Λ)`, with third map `w`. -/
noncomputable abbrev closedSupportTriangle (K : 𝐃(X, Λ))
    (w : (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj K))⟦(1 : ℤ)⟧) :
    Triangle 𝐃(X, Λ) :=
  Recollement.triangle (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (rightDerivedLowerStarUpperShriekAdjunction Λ i) K w

/-- The supported localization triangle on `D(X_ét, Λ)` exists and has a unique third map
(`CategoryTheory.Pretriangulated.Recollement.existsUnique_distTriang_counit_unit`). -/
theorem existsUnique_distTriang_closedSupportTriangle
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (K : 𝐃(X, Λ)) :
    ∃! w, closedSupportTriangle i j K w ∈ distTriang _ :=
  Recollement.existsUnique_distTriang_counit_unit _ _
    (fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion i)
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i j (hij ▸ disjoint_compl_left))
    (fun _ hK ↦ rightDerivedLowerStar_essImage_of_isZero i j hij hK) K

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the integral stage `𝒪_E`,
functoriality: for `φ : K ⟶ K'` and distinguished closed-support triangles of `K` and `K'`, the
triple `(Ri_* Ri^! φ, φ, Rj_* j^* φ)` is a morphism of triangles. -/
theorem exists_triangleHom_closedSupportTriangle (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K K' : 𝐃(X, Λ)} (φ : K ⟶ K') {w w'} (hw : closedSupportTriangle i j K w ∈ distTriang _)
    (hw' : closedSupportTriangle i j K' w' ∈ distTriang _) :
    ∃ τ : closedSupportTriangle i j K w ⟶ closedSupportTriangle i j K' w',
      τ.hom₁ = (R((i)_*[ModuleCat.{u + 1} Λ])).map
          ((R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map φ) ∧
        τ.hom₂ = φ ∧
        τ.hom₃ = (R((j)_*[ModuleCat.{u + 1} Λ])).map ((L((j)^*[ModuleCat.{u + 1} Λ])).map φ) :=
  Recollement.exists_triangleHom _ _
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i j (hij ▸ disjoint_compl_left))
    φ hw hw'

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the integral stage `𝒪_E`,
functoriality: a morphism of distinguished closed-support triangles is determined by its middle
component. -/
theorem closedSupportTriangle_hom_ext (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K K' : 𝐃(X, Λ)} {w w'} (hw : closedSupportTriangle i j K w ∈ distTriang _)
    (hw' : closedSupportTriangle i j K' w' ∈ distTriang _)
    {τ τ' : closedSupportTriangle i j K w ⟶ closedSupportTriangle i j K' w'}
    (h : τ.hom₂ = τ'.hom₂) : τ = τ' :=
  Recollement.triangleHom_ext _ _
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i j (hij ▸ disjoint_compl_left))
    hw hw' h

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4) at the integral stage `𝒪_E`:
`Ri^! Rj_* G = 0`, as `Hom(Q, Ri^! Rj_* G) = Hom(Ri_* Q, Rj_* G) = 0`. -/
theorem isZero_rightDerivedUpperShriek_obj_rightDerivedLowerStar_obj
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (G : 𝐃(U, Λ)) :
    IsZero ((R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj G)) :=
  Recollement.isZero_obj_obj (derivedUpperStarLowerStarAdjunction _ j)
    (rightDerivedLowerStarUpperShriekAdjunction Λ i)
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i j (hij ▸ disjoint_compl_left))
    G

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4) at the integral stage `𝒪_E`: the
unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism, `Ri_*` being fully faithful. -/
instance isIso_rightDerivedLowerStarUpperShriekAdjunction_unit :
    IsIso (rightDerivedLowerStarUpperShriekAdjunction Λ i).unit :=
  (rightDerivedLowerStarUpperShriekAdjunction Λ i).unit_isIso_of_L_fully_faithful

end Localization

/-! ### `Dᵇc(-, 𝒪_E)` -/

section BoundedConstructible

variable {U Z X Y : Scheme.{u}} [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] {k : Type u} [Field k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clauses (1) and (1') at the integral stage
`𝒪_E`: for a quasi-compact open immersion `j : U ⟶ X` into a scheme of finite type over `k`
with `dim U ≤ d`, `Rj_*` carries `Dᵇc(U, Λ)` into `Dᵇc(X, Λ)`, and Tor amplitude `[a, b]` of
the reductions goes to `[a, b + 2d]`. -/
theorem boundedConstructibleIntegral_rightDerivedLowerStar_of_isOpenImmersion
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {G : 𝐃(U, Λ)} (hG : DerivedCategory.boundedConstructibleIntegral I U G) :
    DerivedCategory.boundedConstructibleIntegral I X ((R((j)_*[ModuleCat.{u + 1} Λ])).obj G) ∧
      ∀ d : ℕ, topologicalKrullDim U ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b
          ((reductionModIdeal Λ U (I ^ (n + 1))).obj G)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj G)) :=
  have ⟨d, hd⟩ := exists_topologicalKrullDim_le (j ≫ aX)
  ⟨(boundedConstructibleIntegral_rightDerivedLowerStar hϖ hI (j ≫ aX) aX j rfl d hd hG).1,
    fun d' hd' ↦ (boundedConstructibleIntegral_rightDerivedLowerStar hϖ hI (j ≫ aX) aX j rfl d'
      hd' hG).2⟩

/-- Blueprint `proposition-direct-image-along-open-immersion--1`: Integral open direct image
preserves constructibility.

For a quasi-compact open immersion `j : U ⟶ X` into a scheme of finite type over `k` and
`K ∈ Dᵇc(U, 𝒪_E)`, the direct image `Rj_* K` is derived complete and lies in `Dᵇc(X, 𝒪_E)`
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral` contains derived
completeness), and its reduction modulo `I = (ϖ)` is the direct image of the reduction:
`(Rj_* K) ⊗ᴸ Λ ⧸ I ≅ Rj_*(K ⊗ᴸ Λ ⧸ I)`, `Rj_*` being a triangulated `Λ`-linear functor. -/
theorem boundedConstructibleIntegral_rightDerivedLowerStar_and_reductionModIdeal_of_isOpenImmersion
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {G : 𝐃(U, Λ)} (hG : DerivedCategory.boundedConstructibleIntegral I U G) :
    DerivedCategory.boundedConstructibleIntegral I X ((R((j)_*[ModuleCat.{u + 1} Λ])).obj G) ∧
      Nonempty ((reductionModIdeal Λ X I).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj G) ≅
        (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((reductionModIdeal Λ U I).obj G)) := by
  refine ⟨(boundedConstructibleIntegral_rightDerivedLowerStar_of_isOpenImmersion hϖ hI aX j
    hG).1, ?_⟩
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (R((j)_*[ModuleCat.{u + 1} Λ])) hϖ 1 G
  subst hI
  rw [pow_one] at e
  exact ⟨e.symm⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3') at the integral stage `𝒪_E`,
for `i_*`: the direct image along a closed immersion `i : Z ⟶ X` of schemes of finite type over `k`
carries `Dᵇc(Z, Λ)` into `Dᵇc(X, Λ)`. -/
theorem boundedConstructibleIntegral_rightDerivedLowerStar_of_isClosedImmersion
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k))
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFiniteType aX] [QuasiCompact aX] {Q : 𝐃(Z, Λ)}
    (hQ : DerivedCategory.boundedConstructibleIntegral I Z Q) :
    DerivedCategory.boundedConstructibleIntegral I X ((R((i)_*[ModuleCat.{u + 1} Λ])).obj Q) :=
  have ⟨d, hd⟩ := exists_topologicalKrullDim_le (i ≫ aX)
  (boundedConstructibleIntegral_rightDerivedLowerStar hϖ hI (i ≫ aX) aX i rfl d hd hQ).1

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (1) at the integral stage `𝒪_E`, for
any separated quasi-compact morphism `f : Y ⟶ X` locally of finite type (an open immersion `j` or a
closed immersion `i`) into a scheme of finite type over `k`: `Rf_*` carries `Dᵇc(Y, Λ)` into
`Dᵇc(X, Λ)` (`AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerStar`). -/
theorem boundedConstructibleIntegral_rightDerivedLowerStar_obj
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (f : Y ⟶ X) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFiniteType f] {G : 𝐃(Y, Λ)}
    (hG : DerivedCategory.boundedConstructibleIntegral I Y G) :
    DerivedCategory.boundedConstructibleIntegral I X ((R((f)_*[ModuleCat.{u + 1} Λ])).obj G) :=
  have ⟨d, hd⟩ := exists_topologicalKrullDim_le (f ≫ aX)
  (boundedConstructibleIntegral_rightDerivedLowerStar hϖ hI (f ≫ aX) aX f rfl d hd hG).1

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2') at the integral stage `𝒪_E`,
the Tor amplitude bound in a closed-support triangle: let `T` be a distinguished triangle of
`D(X_ét, Λ)` with vertices `Ri_* M`, `K` and `Rj_* j^* K`, where `K` and `Ri_* M` lie in
`Dᵇc(X, Λ)`. If the reductions of `K` have Tor amplitude in `[a, b]` and `dim U ≤ d`, the
reductions of `M` have Tor amplitude in `[a, b + 2d + 1]`: the reductions of `T` are
distinguished, those of `Rj_* j^* K` have Tor amplitude in `[a, b + 2d]`, and
`M ≅ i^* Ri_* M`. -/
theorem torAmplitudeIn_reductionModIdeal_of_distTriang (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {K : 𝐃(X, Λ)} (hK : DerivedCategory.boundedConstructibleIntegral I X K) {M : 𝐃(Z, Λ)}
    (hM : DerivedCategory.boundedConstructibleIntegral I X
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj M))
    {T : Triangle 𝐃(X, Λ)} (hT : T ∈ distTriang _)
    (e₁ : T.obj₁ ≅ (R((i)_*[ModuleCat.{u + 1} Λ])).obj M) (e₂ : T.obj₂ ≅ K)
    (e₃ : T.obj₃ ≅ (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))
    (d : ℕ) (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    (hab : ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) (n : ℕ) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * (d : ℤ) + 1)
      ((reductionModIdeal Λ Z (I ^ (n + 1))).obj M) := by
  let R := reductionModIdeal Λ X (I ^ (n + 1))
  have hjK := boundedConstructibleIntegral_leftDerivedUpperStar hϖ hI j hK
  have hjab := fun m ↦
    (boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar hϖ hI j m
      ⟨(hK.2.choose_spec.choose_spec m).1, hab m⟩).2
  have h₃ := (boundedConstructibleIntegral_rightDerivedLowerStar_of_isOpenImmersion hϖ hI aX j
    hjK).2 d hd a b hjab n
  have hT' := R.map_distinguished _ hT
  have h₁ := DerivedCategory.torAmplitudeIn_obj₂ (ModuleCat.{u + 1} Λ)
    (inv_rot_of_distTriang _ hT')
    (DerivedCategory.torAmplitudeIn.shift
      ((DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso (R.mapIso e₃.symm) h₃) (-1))
    ((DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso (R.mapIso e₂.symm) (hab n))
  have h₁' : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a (b + 2 * (d : ℤ) + 1)
      (R.obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj M)) :=
    ((DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso (R.mapIso e₁) h₁).mono (by omega)
      (by omega)
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  exact (DerivedCategory.torAmplitudeIn _ Z _ _).prop_of_iso
    ((reductionModIdeal Λ Z (I ^ (n + 1))).mapIso (asIso (adj.counit.app M)))
    (boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar hϖ hI i n
      ⟨(hM.2.choose_spec.choose_spec n).1, h₁'⟩).2

variable (I) in
/-- The exceptional inverse image `Ri^! : Dᵇc(X, Λ) ⥤ Dᵇc(Z, Λ)` along a closed immersion, the
restriction of `Ri^!`
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedUpperShriek`), under the
hypotheses providing the exceptional adjunction `Ri_! ⊣ Ri^!` on `D(X_ét, Λ)`. -/
noncomputable abbrev boundedConstructibleIntegralRightDerivedUpperShriek [IsAlgClosed k]
    [IsDomain Λ] [IsAdicComplete I Λ] (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k)) (aZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [IsSeparated aX] [IsSeparated aZ] [HasCompactification aX] [HasCompactification aZ]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aZ)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (i : Z ⟶ X) (hi : i ≫ aX = aZ) [IsClosedImmersion i] [HasCompactification i]
    [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleIntegral I Z).FullSubcategory :=
  ObjectProperty.liftFullSubcategory (DerivedCategory.boundedConstructibleIntegral I X) _
    (R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint fun _ hK ↦
      boundedConstructibleIntegral_rightDerivedUpperShriek hϖ hI aZ aX i hi hK

end BoundedConstructible

section Triangle

variable {U Z X : Scheme.{u}} [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ]
  [Finite (Λ ⧸ I)] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  (aX : X ⟶ Spec (.of k)) (aZ : Z ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
  [IsSeparated aX] [IsSeparated aZ] [HasCompactification aX] [HasCompactification aZ]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aZ)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (i : Z ⟶ X) (hi : i ≫ aX = aZ) [IsClosedImmersion i] [HasCompactification i]
  [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI hi in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clauses (3) and (3') at the integral stage
`𝒪_E`, under the hypotheses providing the exceptional adjunction on `D(X_ét, Λ)`: for
`K ∈ Dᵇc(X, Λ)` the counit `Ri_* Ri^! K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a
distinguished triangle `Ri_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (Ri_* Ri^! K)[1]` with a unique third
arrow, and its three vertices lie in `Dᵇc(-, Λ)`. The vanishing of
`Hom((Ri_* Q)[m], Rj_* G)` is
`AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerStar_rightDerivedLowerStar`,
and the functoriality in `K` is
`AlgebraicGeometry.Etale.exists_triangleHom_closedSupportTriangle` and
`AlgebraicGeometry.Etale.closedSupportTriangle_hom_ext`. -/
theorem boundedConstructibleIntegral_closedSupportTriangle (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ) {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I X
        ((R((i)_*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj K)) ∧
      DerivedCategory.boundedConstructibleIntegral I X
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      ∃! w, closedSupportTriangle i j K w ∈ distTriang _ :=
  ⟨boundedConstructibleIntegral_rightDerivedLowerStar_of_isClosedImmersion hϖ hI aX i
      (boundedConstructibleIntegral_rightDerivedUpperShriek hϖ hI aZ aX i hi hK),
    (boundedConstructibleIntegral_rightDerivedLowerStar_of_isOpenImmersion hϖ hI aX j
      (boundedConstructibleIntegral_leftDerivedUpperStar hϖ hI j hK)).1,
    existsUnique_distTriang_closedSupportTriangle i j hij K⟩

include hϖ hI hi in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2') at the integral stage `𝒪_E`,
under the hypotheses providing the exceptional adjunction on `D(X_ét, Λ)`: if the reductions of
`K ∈ Dᵇc(X, Λ)` have Tor amplitude in `[a, b]` and the open complement `U` has dimension `≤ d`,
the reductions of `Ri^! K` have Tor amplitude in `[a, b + 2d + 1]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_reductionModIdeal_of_distTriang`). -/
theorem torAmplitudeIn_reductionModIdeal_rightDerivedUpperShriek (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : 𝐃(X, Λ)} (hK : DerivedCategory.boundedConstructibleIntegral I X K) (d : ℕ)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    (hab : ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) (n : ℕ) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * (d : ℤ) + 1)
      ((reductionModIdeal Λ Z (I ^ (n + 1))).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj K)) := by
  obtain ⟨hM, -, w, hw, -⟩ := boundedConstructibleIntegral_closedSupportTriangle hϖ hI aX aZ i hi
    j hij hK
  exact torAmplitudeIn_reductionModIdeal_of_distTriang hϖ hI aX i j hK hM hw (Iso.refl _)
    (Iso.refl _) (Iso.refl _) d hd a b hab n

end Triangle

end Etale

end AlgebraicGeometry
