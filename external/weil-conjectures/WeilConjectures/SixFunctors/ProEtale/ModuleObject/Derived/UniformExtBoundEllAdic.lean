/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimensionFiniteField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundPadicAlgCl
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundRationalLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundUniversalHomeomorphism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundSubfield

/-!
# The uniform `Ext` bound for the `ℓ`-adic coefficient rings

Blueprints `lemma-uniform-ext-bound` and `sk-lem-int-ext` (2): let `k` be a field which
is finite or separably closed, of characteristic different from `ℓ`, and `X` a separated scheme of
finite type over `k`. For the coefficient rings `𝒪_E`, `E` and `ℚ̄_ℓ`, every constructible sheaf
`C` on `X` admits `d` with `Ext^q(C, N) = 0` for `q > d` and every constructible `N`:

* `ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_locallyOfFiniteType`,
* `ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_locallyOfFiniteType`,
* `ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_locallyOfFiniteType`.

The base field has finite cohomological dimension for `𝔽_E`-coefficients
(`ProEtale.hasFiniteCohomologicalDimension_residueFieldCoeff`, blueprint
`lemma-cohomological-dimension-base-field`), which gives the bound for `𝒪_E` by reduction modulo a
uniformizer
(`hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension`); the
bound for `E` follows by inverting `ℓ`
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj`), over a
perfect base field by dévissage to lisse sheaves on connected regular schemes, which have lattices;
a separably closed base field is replaced by its algebraic closure, the base change being a
universal homeomorphism
(`ProEtale.CondensedRing.HasUniformConstructibleExtBound.of_isUniversalHomeomorphism`). The bound
for `ℚ̄_ℓ` follows from the finite subextensions
(`ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield`). Abstract finite
extensions `E` of `ℚ_ℓ` are reduced to subextensions of `ℚ̄_ℓ` by choosing an embedding
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_finiteIntermediateField`,
`ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_finiteIntermediateField`).
-/

@[expose] public section

universe u

open CategoryTheory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-- Blueprint `lemma-cohomological-dimension-base-field`: a field `k` which is finite or separably
closed has finite étale cohomological dimension for sheaves of modules over the residue field `𝔽_E`
of `𝒪_E`. -/
lemma hasFiniteCohomologicalDimension_residueFieldCoeff (E : FiniteIntermediateField ℓ)
    (hk : Finite k ∨ IsSepClosed k) :
    Etale.HasFiniteCohomologicalDimension (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k)) := by
  rcases hk with hk | hk
  · exact Etale.hasFiniteCohomologicalDimension_of_finite ℓ (natCast_eq_zero_residueFieldCoeff ℓ E)
  · refine Etale.hasFiniteCohomologicalDimension_of_isSepClosed _ (fun x ↦ ?_) (𝟙 _)
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ, (Fact.out : ℓ.Prime).pos, ?_⟩
    rw [nsmul_eq_mul, natCast_eq_zero_residueFieldCoeff, zero_mul]

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX]

include aX

/-- Blueprint `sk-lem-int-ext` (2), for a subfield `E ⊆ ℚ̄_ℓ` finite over `ℚ_ℓ`. -/
theorem hasUniformConstructibleExtBound_padicIntegersRingObj_of_locallyOfFiniteType (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) :=
  hasUniformConstructibleExtBound_padicIntegersRingObj_of_finiteIntermediateField ℓ E X
    (hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension ℓ
      (finiteIntermediateFieldOfAlgebra ℓ E) aX
      (hasFiniteCohomologicalDimension_residueFieldCoeff ℓ _ hk))

/-- Blueprint `lemma-uniform-ext-bound`, for a finite subextension `E ⊆ ℚ̄_ℓ` of
`ℚ_ℓ`, over a perfect base field: the bound for `𝒪_E` and the continuity of `Ext` give the bound
for `E` by dévissage to lisse sheaves on connected regular schemes, which have lattices
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj`). -/
theorem hasUniformConstructibleExtBound_padicSubfieldRingObj_of_perfectField [PerfectField k]
    (E : FiniteIntermediateField ℓ) (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  exact hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj ℓ E aX
    (hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension ℓ E
      aX (hasFiniteCohomologicalDimension_residueFieldCoeff ℓ E hk))
    (CondensedRing.hasConstructibleExtContinuity_padicIntegersRingObj_of_locallyOfFiniteType ℓ
      E.1 aX)

/-- Blueprint `lemma-uniform-ext-bound`, for a finite subextension `E ⊆ ℚ̄_ℓ` of
`ℚ_ℓ`. A finite field is perfect; for `k` separably closed, the base change
`X_{k̄} ⟶ X` to an algebraic closure is a universal homeomorphism, `k̄/k` being purely
inseparable, along which the bound descends
(`ProEtale.CondensedRing.HasUniformConstructibleExtBound.of_isUniversalHomeomorphism`). -/
theorem hasUniformConstructibleExtBound_padicSubfieldRingObj_of_locallyOfFiniteType
    (E : FiniteIntermediateField ℓ) (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X) := by
  rcases hk with hk | hk
  · exact hasUniformConstructibleExtBound_padicSubfieldRingObj_of_perfectField ℓ aX E (Or.inl hk)
  · let φ := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    have : IsUniversalHomeomorphism φ := Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism
    exact CondensedRing.HasUniformConstructibleExtBound.of_isUniversalHomeomorphism _
      (Limits.pullback.fst aX φ)
      (hasUniformConstructibleExtBound_padicSubfieldRingObj_of_perfectField ℓ
        (Limits.pullback.snd aX φ) E (Or.inr inferInstance))

/-- Blueprint `lemma-uniform-ext-bound`, for a finite extension `E` of `ℚ_ℓ`. -/
theorem hasUniformConstructibleExtBound_continuousMapRingObj_of_locallyOfFiniteType (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X) := by
  obtain ⟨E', h⟩ := hasUniformConstructibleExtBound_continuousMapRingObj_of_finiteIntermediateField
    ℓ E
  exact h X (hasUniformConstructibleExtBound_padicSubfieldRingObj_of_locallyOfFiniteType ℓ aX E' hk)

/-- Blueprint `lemma-uniform-ext-bound`, for `ℚ̄_ℓ`. -/
theorem hasUniformConstructibleExtBound_padicAlgClRingObj_of_locallyOfFiniteType
    (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  exact hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield ℓ
    fun E ↦ hasUniformConstructibleExtBound_padicSubfieldRingObj_of_locallyOfFiniteType ℓ aX E hk

end AlgebraicGeometry.ProEtale
