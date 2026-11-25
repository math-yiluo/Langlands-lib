/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdicFiniteIntermediateFieldIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProperFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CoefficientIsoTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarEllAdicReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegral

/-!
# Proper direct images of bounded constructible `ℓ`-adic complexes

Let `p : Z ⟶ Y` be a proper morphism to a noetherian scheme. For the `ℓ`-adic coefficient rings
`Λ = 𝒪_E, E, ℚ̄_ℓ`, the derived direct image `Rp_*` maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` as soon as it
does so with the residue field coefficients `𝔽_{E'}` of the finite subextensions `E' ⊆ ℚ̄_ℓ`
(blueprint `proposition-proper-direct-image-constructible-complexes` (1),
`proposition-proper-direct-image-constructible-complexes` (1)):

* `boundedConstructible_rightDerivedLowerStar_padicIntegersRingObj_of_residueField`: for `𝒪_E`,
  the integral case `boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueField`
  transported along an isomorphism `𝒪̲_E ≅ 𝒪̲_{E'}` with `E'` a finite subextension;
* `boundedConstructible_rightDerivedLowerStar_continuousMapRingObj_of_residueField`: for `E`, from
  the integral case and an isomorphism `E̲ ≅ E̲'`;
* `boundedConstructible_rightDerivedLowerStar_padicAlgClRingObj_of_residueField`: for `ℚ̄_ℓ`.

The residue field input holds over a noetherian `k`-scheme with `ℓ` invertible in `k`
(`residueFieldFiniteness_of_isNoetherian`, from the finiteness of proper direct images over a
noetherian base), in particular for `Y` of finite type over such a field `k`, which gives the
theorems `boundedConstructible_rightDerivedLowerStar_of_isProper_*_of_finiteType`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The exponent `ℓ` of the residue field `𝔽_E` is invertible on every scheme over a field `k`
of characteristic different from `ℓ`. -/
lemma hasInvertibleExponent_residueFieldCoeff (E : FiniteIntermediateField ℓ) {k : Type u}
    [Field k] [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) :
    HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) X := by
  have hk : (ℓ : k) ≠ 0 := by
    intro h
    rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h) with h₁ | h₁
    · exact CharP.ringChar_ne_one h₁
    · exact (Fact.out : ringChar k ≠ ℓ) h₁
  have : HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k)) :=
    ⟨ℓ, (Fact.out : ℓ.Prime).pos, natCast_eq_zero_residueFieldCoeff ℓ E,
      by simpa using (Ne.isUnit hk).map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  exact HasInvertibleExponent.of_hom aX

variable {Z Y : Scheme.{u}} [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p]

/-- The residue field input: `Rp_*` preserves `Dᵇc(-, 𝔽_E)` for every finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
def ResidueFieldFiniteness : Prop :=
  ∀ (E : FiniteIntermediateField ℓ)
    (L : _root_.DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)))),
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))
        Z L →
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Y
        ((R((p)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).obj L)

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` (1), from the residue field
input: for `E ⊆ ℚ̄_ℓ` finite over `ℚ_ℓ`, `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_padicIntegersRingObj_of_residueField
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (hp : ResidueFieldFiniteness ℓ p)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicIntegersRingObj.{u} ℓ E⟧).obj K) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  obtain ⟨E', e, _⟩ := Profinite.exists_padicIntegersRingObj_iso.{u} ℓ E
  exact boundedConstructible_rightDerivedLowerStar_of_iso e p
    (fun K hK ↦ boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueField ℓ E' p
      (hp E') K hK) K hK

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` (1) for the finite
subextensions: `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧` for `E ⊆ ℚ̄_ℓ` a finite subextension. -/
lemma boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueFieldFiniteness
    (hp : ResidueFieldFiniteness ℓ p) (E : FiniteIntermediateField ℓ)
    (K₀ : Dᵇc(Z)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)
      ((R((p)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀.obj) :=
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueField ℓ E p (hp E) K₀.obj
    K₀.property

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` (1), from the residue field
input: for a finite extension `E` of `ℚ_ℓ`, `Rp_*` maps `Dᵇc(Z)⟦E⟧` into `Dᵇc(Y)⟦E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_continuousMapRingObj_of_residueField
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hp : ResidueFieldFiniteness ℓ p)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  obtain ⟨E', e, _⟩ := Profinite.exists_continuousMapRingObj_iso.{u} ℓ E
  exact boundedConstructible_rightDerivedLowerStar_of_iso e p
    (fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj_continuousMapRingObj_of_padicIntegers
      ℓ p E' (boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueFieldFiniteness
        ℓ p hp E') ⟨K, hK⟩) K hK

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` for `ℚ̄_ℓ`, from the residue
field input: `Rp_*` maps `Dᵇc(Z)⟦ℚ̄_ℓ⟧` into `Dᵇc(Y)⟦ℚ̄_ℓ⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_padicAlgClRingObj_of_residueField
    (hp : ResidueFieldFiniteness ℓ p)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  exact boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_padicIntegers ℓ p
    (boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueFieldFiniteness ℓ p hp)
    ⟨K, hK⟩

/-- The residue field input over a noetherian `k`-scheme, `ℓ` being invertible in `k`, from the
finiteness of proper direct images over a noetherian base
(`ProEtale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`). -/
lemma residueFieldFiniteness_of_isNoetherian {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (aY : Y ⟶ Spec (.of k)) : ResidueFieldFiniteness ℓ p :=
  fun E _ hL ↦
    have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
      inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E.1)))
    have := hasInvertibleExponent_residueFieldCoeff ℓ E (𝟙 (Spec (.of k)))
    ProEtale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian aY p hL

/-! ### Over a scheme of finite type over a field -/

variable {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)] (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aY] [QuasiCompact aY]

include aY

omit [IsNoetherian Y]

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` (1): for `p : Z ⟶ Y` proper
with `Y` of finite type over a field `k` in which `ℓ` is invertible, `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into
`Dᵇc(Y)⟦𝒪_E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper_padicIntegersRingObj_of_finiteType
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicIntegersRingObj.{u} ℓ E⟧).obj K) :=
  have := isNoetherian_of_locallyOfFiniteType aY
  boundedConstructible_rightDerivedLowerStar_padicIntegersRingObj_of_residueField ℓ p E
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` (1): for `p : Z ⟶ Y` proper
with `Y` of finite type over a field `k` in which `ℓ` is invertible, `Rp_*` maps `Dᵇc(Z)⟦E⟧` into
`Dᵇc(Y)⟦E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper_continuousMapRingObj_of_finiteType
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K) :=
  have := isNoetherian_of_locallyOfFiniteType aY
  boundedConstructible_rightDerivedLowerStar_continuousMapRingObj_of_residueField ℓ p E
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-- Blueprint `proposition-proper-direct-image-constructible-complexes`: for `p : Z ⟶ Y` proper with
`Y` of finite type over a field `k` in which `ℓ` is invertible, `Rp_*` maps `Dᵇc(Z)⟦ℚ̄_ℓ⟧` into
`Dᵇc(Y)⟦ℚ̄_ℓ⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper_padicAlgClRingObj_of_finiteType
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K) :=
  have := isNoetherian_of_locallyOfFiniteType aY
  boundedConstructible_rightDerivedLowerStar_padicAlgClRingObj_of_residueField ℓ p
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

end AlgebraicGeometry.ProEtale.CondensedRing
