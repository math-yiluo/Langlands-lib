/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The closed-support triangle on `Dᵇc(X̄, E)` is Frobenius-equivariant

Let `k₀` be a finite field, `X` a quasi-compact `k₀`-scheme locally of finite type, `i : Z ⟶ X` a
closed immersion and `j : U ⟶ X` the complementary quasi-compact open immersion, over `k₀`, and
let `X̄`, `Z̄`, `Ū` be the geometric fibres, with the base changes `ī`, `j̄` and the geometric
Frobenii `Fr`. This file proves the Weil clause of blueprint
`lemma-local-cohomology-right-adjoint--2` at the stage `E`: a Weil structure on `K ∈ Dᵇc(X̄, E)` is
an isomorphism `θ : Fr^* K ≅ K`, where `Fr^* = R(Fr⁻¹)_*`, i.e. `(K, θ)` is an object of
`CategoryTheory.Endofunctor.IsoAlgebra`; then

1. `Rī^!` carries Weil structures and `ī_* ⊣ Rī^!` lifts to objects with Weil structure, with the
   original unit and counit
   (`AlgebraicGeometry.Etale.geometricFrobeniusClosedUpperShriekIsoAlgebraAdjunction`); the same
   holds for `j̄^* ⊣ Rj̄_*`
   (`AlgebraicGeometry.Etale.geometricFrobeniusUpperStarIsoAlgebraAdjunction`);
2. the three arrows of the closed-support triangle of a Weil complex are Weil-equivariant
   (`AlgebraicGeometry.Etale.geometricFrobeniusClosedSupportTriangleIso`).

This instantiates `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` with
`τ = Fr⁻¹`, which commutes with `ī` and `j̄`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (M : Submonoid Λ) {I : Ideal Λ} [IsNoetherianRing Λ]
  [Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})] [Finite (Λ ⧸ I)]
  {k₀ : Type u} [Field k₀] [Finite k₀]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of (AlgebraicClosure k₀)))]
  {Z U X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

set_option hygiene false in
/-- The structure morphism `X̄ ⟶ Spec k̄` of the geometric fibre. -/
local notation "a[" Y "]" => (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure

set_option hygiene false in
/-- The inverse `Fr⁻¹` of the geometric Frobenius of `Ȳ`: `R(Fr⁻¹)_* = Fr^*`. -/
local notation "Fr⁻¹[" Y "]" => (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv

set_option hygiene false in
/-- The base change `ī : Z̄ ⟶ X̄`. -/
local notation "ī" => Scheme.Hom.geometricFiberMap i (comp_over i (Spec (CommRingCat.of k₀)))

set_option hygiene false in
/-- The base change `j̄ : Ū ⟶ X̄`. -/
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

omit [Finite k₀] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsClosedImmersion i] [IsOpenImmersion j]
  [QuasiCompact j] in
include hij in
/-- The base changes `ī` and `j̄` have complementary ranges. -/
lemma range_geometricFiberMap_eq_compl : Set.range (ī).base = (Set.range (j̄).base)ᶜ :=
  (Scheme.Hom.isCompl_range_geometricFiberMap i j _ _ hij).eq_compl

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): the adjunction
`j̄^* ⊣ Rj̄_*` on `Dᵇc(-, E)` of the geometric fibres lifts to objects with Weil structure
`θ : Fr^* K ≅ K`, with the original unit and counit. -/
noncomputable def geometricFrobeniusUpperStarIsoAlgebraAdjunction :=
  boundedConstructibleRationalUpperStarIsoAlgebraAdjunction M I a[X] Fr⁻¹[X] ī j̄
    (range_geometricFiberMap_eq_compl i j hij) (ī ≫ a[X]) (j̄ ≫ a[X]) Fr⁻¹[Z] Fr⁻¹[U]
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): `Rī^!` carries
Weil structures, and the adjunction `ī_* ⊣ Rī^!` on `Dᵇc(-, E)` of the geometric fibres lifts to
objects with Weil structure `θ : Fr^* K ≅ K`, with the original unit and counit. -/
noncomputable def geometricFrobeniusClosedUpperShriekIsoAlgebraAdjunction :=
  boundedConstructibleRationalClosedUpperShriekIsoAlgebraAdjunction M I a[X] Fr⁻¹[X] ī j̄
    (range_geometricFiberMap_eq_compl i j hij) (ī ≫ a[X]) (j̄ ≫ a[X]) Fr⁻¹[Z] Fr⁻¹[U]
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): for a Weil complex
`(K, θ : Fr^* K ≅ K)` on the geometric fibre `X̄` at the stage `E`, the three arrows of the
closed-support triangle `ī_* Rī^! K ⟶ K ⟶ Rj̄_* j̄^* K ⟶ (ī_* Rī^! K)[1]` are Weil-equivariant:
the Weil structures of the vertices form an isomorphism of triangles from its image under
`Fr^*`. -/
noncomputable def geometricFrobeniusClosedSupportTriangleIso
    (K : IsoAlgebra (boundedConstructibleRationalRightDerivedLowerStar M I a[X] Fr⁻¹[X])) {w}
    (hw : boundedConstructibleRationalClosedSupportTriangle M a[X] ī j̄
      (range_geometricFiberMap_eq_compl i j hij) K.carrier w ∈ distTriang _) :
    (boundedConstructibleRationalRightDerivedLowerStar M I a[X] Fr⁻¹[X]).mapTriangle.obj
        (boundedConstructibleRationalClosedSupportTriangle M a[X] ī j̄
          (range_geometricFiberMap_eq_compl i j hij) K.carrier w) ≅
      boundedConstructibleRationalClosedSupportTriangle M a[X] ī j̄
        (range_geometricFiberMap_eq_compl i j hij) K.carrier w :=
  boundedConstructibleRationalClosedSupportTriangleIso M I a[X] Fr⁻¹[X] ī j̄
    (range_geometricFiberMap_eq_compl i j hij) (ī ≫ a[X]) (j̄ ≫ a[X]) Fr⁻¹[Z] Fr⁻¹[U]
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) K hw

end Etale

end AlgebraicGeometry
