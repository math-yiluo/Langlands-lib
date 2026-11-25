/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.WeilSheaf.FieldCoefficientCohomology

/-!
# Cohomology with Tate twisted integral coefficients `𝒪_E(m)`

Let `k₀` be a finite field with algebraic closure `k̄`, `X` a scheme over `k₀` with geometric
fiber `X̄ = X ×_{k₀} k̄` and geometric Galois Frobenius `Fr_X : X̄ ≅ X̄`, and let `E ⊆ ℚ̄_ℓ` be a
finite extension of `ℚ_ℓ` with ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`. Following
blueprint `def-weil-ordinary-compact-cohomology`, the coefficient object of the stage
`Λ = 𝒪_E` is the completed coefficient sheaf `𝒪̂_{E,X̄} : U ↦ C(U, 𝒪_E)` on the pro-étale site
(`AlgebraicGeometry.ProEtale.FieldSheaf.unit`), and its Tate twist is

`𝒪_E(m)_X̄ = 𝒪̂_{E,X̄} ⊗ 𝒪_E(m)`, `𝒪_E(1) = ℤ_ℓ(1) ⊗_{ℤ_ℓ} 𝒪_E = lim_r μ_{ℓ^r} ⊗_{ℤ_ℓ} 𝒪_E`.

On the geometric fiber the Tate module `ℤ_ℓ(1)(k̄)` is a free `ℤ_ℓ`-module of rank one on which
the geometric Frobenius `σ` of `k̄` acts by the cyclotomic character `χ_ℓ(σ) ∈ ℤ_ℓˣ` (which is
`q⁻¹` for `ℓ ≠ p`). Hence, as for the stages `E`
(`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`) and `ℚ̄_ℓ`
(`WeilConjectures.WeilSheaf.TateTwist`), `𝒪_E(m)_X̄` is the constant sheaf `𝒪̂_{E,X̄}` whose
canonical Weil structure `Fr_X^* 𝒪̂_{E,X̄} ≅ 𝒪̂_{E,X̄}` is multiplied by the unit
`χ_ℓ(σ)ᵐ ∈ 𝒪_Eˣ` (`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.tateTwistConstant`).

Since the constructible `Λ`-sheaves of `WeilConjectures.SixFunctors.ProEtale.FieldCoefficient`
are only available over fields, the `𝒪_E`-Weil structures live on all pro-étale `𝒪_E`-sheaves:
`AlgebraicGeometry.ProEtaleIntegralWeilSheaf` is the category of pairs of a sheaf `F` of
`Λ_X̄`-modules and an isomorphism `θ : Fr_X^* F ≅ F`, for any commutative ring `Λ` with an
ultrametric norm. The cohomology `Hⁱ(X̄, 𝒪_E(m))` and `Hⁱ_c(X̄, 𝒪_E(m))` is then that of the
underlying sheaf `For(𝒪_E(m)_X)`, computed as in
`WeilConjectures.WeilSheaf.FieldCoefficientCohomology`
(`AlgebraicGeometry.ProEtale.fieldCohomology`,
`AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology`).

The twisting unit of the stage `𝒪_E` is sent to that of the stage `E` by the inclusion
`𝒪_E ⊆ E`, so that the `E`-stage twist `E_X(m)` is the constant twist of `E_X` by the image of the
`𝒪_E`-stage twisting unit (`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant_eq_constantTwist`),
and both are `q^{-m}` in `ℚ̄_ℓ` (`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.cyclotomicUnit_eq`).

## Main definitions

- `AlgebraicGeometry.ProEtaleIntegralWeilSheaf`: pro-étale `Λ`-sheaves with a Weil structure.
- `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.constant`,
  `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.constantTwist`: `Λ_X` and its constant twists.
- `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.cyclotomicUnit`: `χ_ℓ(σ) ∈ 𝒪_Eˣ`.
- `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.tateTwist`,
  `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.tateTwistConstant`: `F(m)` and `𝒪_E(m)_X`.
- `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.cohomology`,
  `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.compactlySupportedCohomology`: `Hⁱ(X̄, F)` and
  `Hⁱ_c(X̄, F)`, and their versions for complexes of Weil sheaves.
- `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.cohomologyTateTwist`,
  `AlgebraicGeometry.ProEtaleIntegralWeilSheaf.compactlySupportedCohomologyTateTwist`:
  `Hⁱ(X̄, 𝒪_E(m))` and `Hⁱ_c(X̄, 𝒪_E(m))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Frobenius

variable (k₀ : Type u) [Field k₀] [Finite k₀] (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius pullback `Fr_X^*` of sheaves of `Λ_X̄`-modules on the geometric fiber `X̄`, for
a commutative ring `Λ` with an ultrametric norm (for instance `𝒪_E`), realized as the pushforward
along `Fr_X⁻¹`. -/
noncomputable abbrev ProEtaleIntegralWeilSheaf.frobeniusPullback :
    FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ]

/-- The category of pro-étale `Λ`-sheaves with a Weil structure on a `k₀`-scheme `X`, for a
commutative ring `Λ` with an ultrametric norm, the case of interest being the ring of integers
`𝒪_E` of a finite extension `E` of `ℚ_ℓ`: pairs of a sheaf `F` of `Λ_X̄`-modules on `X̄_proét`
and an isomorphism `θ : Fr_X^* F ≅ F`, with the morphisms of sheaves commuting with the `θ`'s.
For a field `Λ` this is `AlgebraicGeometry.ProEtaleFieldWeilSheaf`. -/
abbrev ProEtaleIntegralWeilSheaf :=
  IsoAlgebra (ProEtaleIntegralWeilSheaf.frobeniusPullback k₀ Λ X)

instance : IsGrothendieckAbelian.{u + 1} (ProEtaleIntegralWeilSheaf k₀ Λ X) :=
  IsoAlgebra.isGrothendieckAbelian _

end Frobenius

namespace ProEtaleIntegralWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ Λ X) in
/-- The constant pro-étale `Λ`-Weil sheaf `Λ_X`: the constant sheaf `Λ_X̄ : U ↦ C(U, Λ)` on the
geometric fiber (for `Λ = 𝒪_E` the completed coefficient sheaf `𝒪̂_{E,X̄}`), with the canonical
Weil structure `Fr_X^* Λ_X̄ = (Fr_X⁻¹)_* Λ_X̄ ≅ Λ_X̄`, pulling back functions. -/
noncomputable def constant : ProEtaleIntegralWeilSheaf k₀ Λ X :=
  .mk (FieldSheaf.unit Λ _)
    (fieldLowerStarUnitIso Λ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)

/-- The constant twist `F ⊗ 𝓑_b` of a pro-étale `Λ`-Weil sheaf by a unit `b` of `Λ`: the same
sheaf, with its Weil structure multiplied by `b`. -/
noncomputable def constantTwist (F : ProEtaleIntegralWeilSheaf k₀ Λ X) (b : Λˣ) :
    ProEtaleIntegralWeilSheaf k₀ Λ X :=
  .mk F.carrier (F.str ≪≫ FieldSheaf.smulIso b F.carrier)

omit [IsUltrametricDist Λ] in
/-- The underlying sheaf of a constant twist is the underlying sheaf. -/
@[simp]
lemma constantTwist_carrier (F : ProEtaleIntegralWeilSheaf k₀ Λ X) (b : Λˣ) :
    (F.constantTwist b).carrier = F.carrier :=
  rfl

omit [IsUltrametricDist Λ] in
/-- Twisting by the unit `1` does not change the Weil structure. -/
lemma constantTwist_one (F : ProEtaleIntegralWeilSheaf k₀ Λ X) : F.constantTwist 1 = F := by
  obtain ⟨⟨A, s⟩, h⟩ := F
  have : FieldSheaf.smul (ULift.up ((1 : Λˣ) : Λ)) A = 𝟙 A := FieldSheaf.smul_one A
  simp only [constantTwist, FieldSheaf.smulIso, this]
  congr 2

omit [IsUltrametricDist Λ] in
/-- Twisting twice by constant units is twisting by their product. -/
lemma constantTwist_constantTwist (F : ProEtaleIntegralWeilSheaf k₀ Λ X) (b c : Λˣ) :
    (F.constantTwist b).constantTwist c = F.constantTwist (b * c) := by
  have hbc : (ULift.up (c : Λ) * ULift.up (b : Λ) : ULift.{u + 1} Λ) =
      ULift.up ((b * c : Λˣ) : Λ) := by
    change ULift.up ((c : Λ) * b) = ULift.up _
    rw [Units.val_mul, mul_comm]
  change IsoAlgebra.mk F.carrier ((F.constantTwist b).str ≪≫ FieldSheaf.smulIso c F.carrier) =
    IsoAlgebra.mk F.carrier (F.str ≪≫ FieldSheaf.smulIso (b * c) F.carrier)
  congr 1
  refine Iso.ext ?_
  change (F.str.hom ≫ FieldSheaf.smul (ULift.up (b : Λ)) _) ≫
      FieldSheaf.smul (ULift.up (c : Λ)) _ =
    F.str.hom ≫ FieldSheaf.smul (ULift.up ((b * c : Λˣ) : Λ)) _
  rw [Category.assoc, FieldSheaf.smul_smul, hbc]
section Integral

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

variable (k₀) in
/-- The value `χ_ℓ(σ) ∈ 𝒪_Eˣ` of the `ℓ`-adic cyclotomic character at the geometric Frobenius
`σ` of the algebraic closure `k̄` of `k₀`, mapped along `ℤ_ℓ ⟶ 𝒪_E`: the scalar by which the
geometric Frobenius acts on `𝒪_E(1)(k̄) = ℤ_ℓ(1)(k̄) ⊗_{ℤ_ℓ} 𝒪_E`. For `ℓ ≠ p` it is `q⁻¹`
(`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.cyclotomicUnit_eq`). -/
noncomputable def cyclotomicUnit [Fact (ringChar k₀ ≠ l)] : (PadicAlgCl.integers l E)ˣ :=
  letI := Fintype.ofFinite k₀
  Units.map (padicIntToIntegers l E).toMonoidHom
    (cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv)

/-- The `𝒪_E`-stage cyclotomic unit is the `ℚ̄_ℓ`-stage one (`WeilSheaf.cyclotomicUnit`) under
`𝒪_E ⊆ E ⊆ ℚ̄_ℓ`. -/
lemma algebraMap_cyclotomicUnit [Fact (ringChar k₀ ≠ l)] :
    algebraMap E (PadicAlgCl l) ((cyclotomicUnit k₀ E : PadicAlgCl.integers l E) : E) =
      (WeilSheaf.cyclotomicUnit k₀ l : PadicAlgCl l) := by
  simp only [cyclotomicUnit, WeilSheaf.cyclotomicUnit, Units.coe_map]
  rfl

variable [Fact (ringChar k₀ ≠ l)]

/-- For `ℓ ≠ p`, the geometric Frobenius acts on `𝒪_E(1)(k̄)` by `q⁻¹`, `q = #k₀`. -/
theorem cyclotomicUnit_eq :
    algebraMap E (PadicAlgCl l) ((cyclotomicUnit k₀ E : PadicAlgCl.integers l E) : E) =
      (Nat.card k₀ : PadicAlgCl l)⁻¹ := by
  rw [algebraMap_cyclotomicUnit, WeilSheaf.cyclotomicUnit_eq]

end Integral

section TateTwist

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {E : IntermediateField ℚ_[l] (PadicAlgCl l)}

/-- The Tate twist `F(m) = F ⊗ 𝒪_E(m)` of a pro-étale `𝒪_E`-Weil sheaf `F`, `m ∈ ℤ`: the
Tate sheaf `𝒪_E(m)` is constant on the geometric fiber, so this is the same sheaf, with its Weil
structure multiplied by `χ_ℓ(σ)ᵐ` (`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.cyclotomicUnit`). -/
noncomputable def tateTwist (F : ProEtaleIntegralWeilSheaf k₀ (PadicAlgCl.integers l E) X)
    (m : ℤ) : ProEtaleIntegralWeilSheaf k₀ (PadicAlgCl.integers l E) X :=
  F.constantTwist (cyclotomicUnit k₀ E ^ m)

/-- `F(0) = F`. -/
lemma tateTwist_zero (F : ProEtaleIntegralWeilSheaf k₀ (PadicAlgCl.integers l E) X) :
    F.tateTwist 0 = F := by
  rw [tateTwist, zpow_zero, constantTwist_one]

/-- `F(m)(m') = F(m + m')`. -/
lemma tateTwist_tateTwist (F : ProEtaleIntegralWeilSheaf k₀ (PadicAlgCl.integers l E) X)
    (m m' : ℤ) : (F.tateTwist m).tateTwist m' = F.tateTwist (m + m') := by
  rw [tateTwist, tateTwist, tateTwist, constantTwist_constantTwist, zpow_add]

variable (k₀ X E) in
/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, stage `Λ = 𝒪_E`, the Tate twisted coefficient object.

The Tate twisted constant coefficient object `𝒪_E(m)_X = 𝒪̂_{E,X} ⊗ 𝒪_E(m)`, `m ∈ ℤ`, for the
ring of integers `𝒪_E` of a subfield `E` of `ℚ̄_ℓ` (for instance a finite extension of `ℚ_ℓ`):
the completed coefficient sheaf `𝒪̂_{E,X̄} : U ↦ C(U, 𝒪_E)` on the geometric fiber, whose
canonical Weil structure is multiplied by `χ_ℓ(σ)ᵐ ∈ 𝒪_Eˣ`, `σ` the geometric Frobenius of `k̄`
and `χ_ℓ` the `ℓ`-adic cyclotomic character: `𝒪_E(1) = ℤ_ℓ(1) ⊗_{ℤ_ℓ} 𝒪_E` is constant on the
geometric fiber, the geometric Frobenius acting on `ℤ_ℓ(1)(k̄) = lim_r μ_{ℓ^r}(k̄)` by `χ_ℓ(σ)`,
which is `q⁻¹` for `ℓ ≠ p`. -/
noncomputable def tateTwistConstant (m : ℤ) :
    ProEtaleIntegralWeilSheaf k₀ (PadicAlgCl.integers l E) X :=
  (constant k₀ (PadicAlgCl.integers l E) X).tateTwist m

/-- `𝒪_E(0)_X = 𝒪_E,X`. -/
lemma tateTwistConstant_zero :
    tateTwistConstant k₀ X E 0 = constant k₀ (PadicAlgCl.integers l E) X :=
  tateTwist_zero _

end TateTwist

section Cohomology

variable [HasCompactification (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure]

/-- The cohomology `Hⁱ(X̄, F)` of a pro-étale `Λ`-Weil sheaf, that of its underlying sheaf
`For(F)` placed in degree `0`, along the structure morphism `X̄ ⟶ Spec k̄` of the geometric
fiber (`AlgebraicGeometry.ProEtale.fieldCohomology`). -/
noncomputable def cohomology (F : ProEtaleIntegralWeilSheaf k₀ Λ X) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCohomology (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F.carrier)

/-- The compactly supported cohomology `Hⁱ_c(X̄, F)` of a pro-étale `Λ`-Weil sheaf, that of its
underlying sheaf `For(F)` placed in degree `0`
(`AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology`). -/
noncomputable def compactlySupportedCohomology (F : ProEtaleIntegralWeilSheaf k₀ Λ X) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCompactlySupportedCohomology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F.carrier)

variable (k₀ Λ X) in
/-- The forgetful functor `For` from the derived category of pro-étale `Λ`-Weil sheaves on `X`
to the derived category of pro-étale `Λ`-sheaves on `X̄`, forgetting the Weil structure; it is
induced by the exact forgetful functor of the abelian categories. -/
noncomputable def derivedForget :
    _root_.DerivedCategory (ProEtaleIntegralWeilSheaf k₀ Λ X) ⥤
      _root_.DerivedCategory (FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (IsoAlgebra.forget _).mapDerivedCategory

/-- The cohomology `Hⁱ(X̄, K) = Hⁱ(X̄, For(K))` of a complex `K` of pro-étale `Λ`-Weil
sheaves. -/
noncomputable def complexCohomology
    (K : _root_.DerivedCategory (ProEtaleIntegralWeilSheaf k₀ Λ X)) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCohomology (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
    ((derivedForget k₀ Λ X).obj K)

/-- The compactly supported cohomology `Hⁱ_c(X̄, K) = Hⁱ_c(X̄, For(K))` of a complex `K` of
pro-étale `Λ`-Weil sheaves. -/
noncomputable def complexCompactlySupportedCohomology
    (K : _root_.DerivedCategory (ProEtaleIntegralWeilSheaf k₀ Λ X)) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCompactlySupportedCohomology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
      ((derivedForget k₀ Λ X).obj K)

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (E : IntermediateField ℚ_[l] (PadicAlgCl l))

variable (k₀ X) in
/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, stage `Λ = 𝒪_E`, with a Tate twist.

The cohomology `Hⁱ(X̄, 𝒪_E(m)) = Hⁱ(X̄, For(𝒪_E(m)_X))` of the geometric fiber `X̄` of a
`k₀`-scheme `X` with coefficients in the Tate twist `𝒪_E(m)`: the cohomology
`Hⁱ(RΓ(X̄, -))`, `RΓ(X̄, -) = Fib_s ∘ Ra_*` (`AlgebraicGeometry.ProEtale.fieldCohomology`), of the
twisted completed coefficient sheaf `𝒪_E(m)_X̄ = 𝒪̂_{E,X̄} ⊗ 𝒪_E(m)`
(`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.tateTwistConstant`). -/
noncomputable def cohomologyTateTwist (m i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integers l E)) :=
  (tateTwistConstant k₀ X E m).cohomology i

variable (k₀ X) in
/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, stage `Λ = 𝒪_E`, with a Tate twist.

The compactly supported cohomology `Hⁱ_c(X̄, 𝒪_E(m)) = Hⁱ_c(X̄, For(𝒪_E(m)_X))`: the cohomology
of `RΓ_c(X̄, -) = Fib_s ∘ Ra_!`
(`AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology`) of the twisted completed
coefficient sheaf `𝒪_E(m)_X̄` (`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.tateTwistConstant`).
-/
noncomputable def compactlySupportedCohomologyTateTwist (m i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integers l E)) :=
  (tateTwistConstant k₀ X E m).compactlySupportedCohomology i

omit [HasCompactification (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure] in
/-- Untwisted, `Hⁱ(X̄, 𝒪_E(0))` is the cohomology `Hⁱ(X̄, 𝒪_E)` of the constant sheaf
(`AlgebraicGeometry.ProEtale.fieldConstantCohomology`). -/
lemma cohomologyTateTwist_zero (i : ℤ) :
    cohomologyTateTwist k₀ X E 0 i =
      fieldConstantCohomology (PadicAlgCl.integers l E)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i := by
  rw [cohomologyTateTwist, tateTwistConstant_zero]
  rfl

/-- Untwisted, `Hⁱ_c(X̄, 𝒪_E(0))` is the compactly supported cohomology `Hⁱ_c(X̄, 𝒪_E)` of the
constant sheaf (`AlgebraicGeometry.ProEtale.fieldConstantCompactlySupportedCohomology`). -/
lemma compactlySupportedCohomologyTateTwist_zero (i : ℤ) :
    compactlySupportedCohomologyTateTwist k₀ X E 0 i =
      fieldConstantCompactlySupportedCohomology (PadicAlgCl.integers l E)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i := by
  rw [compactlySupportedCohomologyTateTwist, tateTwistConstant_zero]
  rfl

end Cohomology

end ProEtaleIntegralWeilSheaf

namespace FieldWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

/-- Compatibility of the twists of the stages `𝒪_E` and `E`: the `E`-stage Tate twisted constant
sheaf `E_X(m)` is the constant twist of `E_X` by the image under `𝒪_E ⊆ E` of the twisting unit
`χ_ℓ(σ)ᵐ ∈ 𝒪_Eˣ` of `𝒪_E(m)_X`
(`AlgebraicGeometry.ProEtaleIntegralWeilSheaf.tateTwistConstant`). -/
lemma tateTwistConstant_eq_constantTwist (m : ℤ) :
    tateTwistConstant k₀ X E m = (constant k₀ E X).constantTwist
      (Units.map (PadicAlgCl.integers l E).subtype.toMonoidHom
        (ProEtaleIntegralWeilSheaf.cyclotomicUnit k₀ E ^ m)) := by
  rw [tateTwistConstant, map_zpow]
  congr 2

end FieldWeilSheaf

end AlgebraicGeometry
