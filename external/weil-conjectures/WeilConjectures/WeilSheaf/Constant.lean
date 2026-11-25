/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# The constant Weil sheaf `ℚ̄_ℓ`

The constant `ℓ`-adic sheaf `ℚ̄_ℓ` on the pro-étale site of the geometric fiber `X̄` of a
`k₀`-scheme `X` (`AlgebraicGeometry.ProEtale.adicConstantSheaf`) carries a canonical Weil
structure: the Frobenius pullback `Fr_X^* = (Fr_X⁻¹)_*` of the sheaf of locally finite
continuous `ℓ`-adic functions is canonically the same sheaf, since `Fr_X` is an automorphism of
schemes (`AlgebraicGeometry.ProEtale.adicConstantSheafLowerStarIso`). On the stalks at closed
points the local Frobenius of this Weil sheaf is the identity of `ℚ̄_ℓ`.

The constant Weil sheaf is lisse, hence constructible, and nonzero as soon as `X` is nonempty
(`AlgebraicGeometry.WeilSheaf.not_isZero_adicConstant`): in contrast to the provisional
definition with discrete coefficients, the category of Weil sheaves on a nonempty scheme is not
zero.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.adicConstant` and
  `AlgebraicGeometry.WeilSheaf.adicConstant`: the constant Weil sheaf `ℚ̄_ℓ`.

## Main results

- `AlgebraicGeometry.WeilSheaf.isLisse_adicConstant`: the constant Weil sheaf is lisse.
- `AlgebraicGeometry.WeilSheaf.not_isZero_adicConstant`: it is nonzero on a nonempty `X`.
- `AlgebraicGeometry.WeilComplex.not_isZero_toComplex_adicConstant`: so is the Weil complex
  `ℚ̄_ℓ[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant pro-étale Weil sheaf `ℚ̄_ℓ` on a `k₀`-scheme `X`: the constant `ℓ`-adic sheaf on
the geometric fiber `X̄`, with the canonical isomorphism `Fr_X^* ℚ̄_ℓ = (Fr_X⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ`
as Weil structure. -/
noncomputable def ProEtaleWeilSheaf.adicConstant : ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mk (AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (adicLowerStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)

lemma ProEtaleWeilSheaf.adicConstant_carrier :
    (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier =
      AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  rfl

end

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant Weil sheaf `ℚ̄_ℓ` on a `k₀`-scheme `X`: the constant `ℓ`-adic sheaf on the
geometric fiber `X̄` with its canonical Weil structure. -/
noncomputable def WeilSheaf.adicConstant : WeilSheaf k₀ l X where
  obj := ProEtaleWeilSheaf.adicConstant k₀ l X
  property := isAdicConstructibleSheaf_adicConstantSheaf _

/-- The constant Weil sheaf is lisse. -/
theorem WeilSheaf.isLisse_adicConstant : (WeilSheaf.adicConstant k₀ l X).IsLisse :=
  isAdicLisseSheaf_adicConstantSheaf _

omit [Finite k₀] in
/-- The geometric fiber of a nonempty `k₀`-scheme is nonempty: it surjects onto the scheme,
being the base change of the surjective morphism `Spec k̄ ⟶ Spec k₀`. -/
lemma Scheme.Hom.nonempty_geometricFiber [Nonempty X] :
    Nonempty (X ↘ Spec (CommRingCat.of k₀)).geometricFiber := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)))) :=
    ⟨fun _ ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : Surjective (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj :=
    MorphismProperty.pullback_fst _ _ this
  exact ⟨((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.surjective x).choose⟩

/-- **Non-degeneracy of Weil sheaves.** The constant Weil sheaf `ℚ̄_ℓ` on a nonempty
`k₀`-scheme is nonzero: its underlying sheaf has the nonzero global section `1`. In particular
the category of Weil sheaves on a nonempty `k₀`-scheme is not zero. -/
theorem WeilSheaf.not_isZero_adicConstant [Nonempty X] :
    ¬ IsZero (WeilSheaf.adicConstant k₀ l X) := by
  have := Scheme.Hom.nonempty_geometricFiber k₀ X
  rw [WeilSheaf.isZero_iff_isZero_carrier]
  exact fun h ↦ not_isZero_adicConstantSheaf l _ ((AdicSheaf.forget _).map_isZero h)

/-- **Non-degeneracy of Weil complexes.** The constant Weil sheaf `ℚ̄_ℓ` placed in degree zero is
a nonzero Weil complex on a nonempty `k₀`-scheme: its cohomology sheaf `𝓗⁰` is `ℚ̄_ℓ`. -/
theorem WeilComplex.not_isZero_toComplex_adicConstant [Nonempty X] :
    ¬ IsZero (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) := fun h ↦
  WeilSheaf.not_isZero_adicConstant k₀ l X
    (((WeilComplex.homologySheaf 0).map_isZero h).of_iso
      (WeilSheaf.toComplexCompHomologySheafIso.app _).symm)

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

lemma WeilSheaf.adicConstant_str_hom_hom :
    (Endofunctor.IsoAlgebra.str (WeilSheaf.adicConstant k₀ l X).obj).hom.hom =
      (ProEtale.adicConstantSheafLowerStarIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom :=
  rfl

end AlgebraicGeometry
