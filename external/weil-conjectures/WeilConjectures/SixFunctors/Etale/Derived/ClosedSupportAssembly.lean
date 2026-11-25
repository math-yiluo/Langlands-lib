/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.PurityPreservation
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-!
# The preservation clauses are theorems

Over a field `k`, the open-complement condition holds for every quasi-compact open immersion
into a scheme of finite type and of dimension at most `d`, with the constant `2d`, for every
finite coefficient ring whose exponent is invertible in `k`
(`AlgebraicGeometry.Etale.openComplementCondition_two_mul_of_finite`). Consequently the
exceptional inverse image along a closed immersion into such a scheme exists on the ambient
derived category and preserves bounded constructibility and finite Tor amplitude, with explicit
bounds, without any hypothesis
(`Etale.isLeftAdjoint_and_constructibleIn_and_torAmplitudeIn_of_isClosedImmersion`).

Together with the smooth and general cases of
`WeilConjectures.SixFunctors.Etale.Derived.PurityPreservation`, this gives the two remarks of
the blueprint on the status of the admissibility hypotheses: the ambient exceptional right
adjoint exists and the two preservation clauses are derived, not assumed
(`AlgebraicGeometry.Etale.ambient_and_preservationClauses`, blueprint `rem-pur-ambient-only`),
and the only hypothesis of the general preservation theorem, the open-complement condition, is
a theorem (`AlgebraicGeometry.Etale.preservationClauses_assembly`, blueprint
`rem-pur-assembly-status`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-- The open-complement condition (`theorem-f-shriek-finite-coefficients--1`) is a theorem, not an
assumption: for a field `k`, a `k`-scheme `T` of finite type and of dimension at most `d` and a
quasi-compact open immersion `j : V ⟶ T`, every finite ring `Λ` whose exponent is invertible in
`k` satisfies the open-complement condition for `j` with the constant `c = 2d`, which does not
depend on `Λ` (the first half of `rem-pur-assembly-status`, see
`AlgebraicGeometry.Etale.preservationClauses_assembly`).

This is `AlgebraicGeometry.Etale.openComplementCondition_two_mul`
(`theorem-f-shriek-finite-coefficients--1`), derived from the two clauses of the direct-image
finiteness input (`theorem-results-from-etale-theory`): the finite-type constructibility theorem
`proposition-six-operations-dctf--2` and the cohomological dimension bound
`lemma-uniform-bounds-pro-etale-affines`. -/
theorem openComplementCondition_two_mul_of_finite {k : Type u} [Field k] {V T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT] (j : V ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] (d : ℕ)
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    OpenComplementCondition Λ j (2 * d) :=
  openComplementCondition_two_mul aT j d hT

/-- The closed-immersion case of `rem-pur-ambient-only` (see
`AlgebraicGeometry.Etale.ambient_and_preservationClauses` for the full remark).

Let `k` be a field, `T` a `k`-scheme of finite type and of dimension at most `d`, `i : Z ⟶ T` a
closed immersion with open complement `j : U ⟶ T`, and `Λ` a finite ring whose exponent is
invertible in `k`. Then, without any further hypothesis:

1. (the ambient datum) `Ri_!` is a left adjoint on the unbounded derived categories, so that the
   exceptional inverse image `Ri^!` exists (`theorem-existence-exceptional-inverse-image--1`);
2. (the constructibility clause) `Ri^!` carries `D_c^{[a, b]}(T, Λ)` into
   `D_c^{[a, b + 2d + 1]}(Z, Λ)` (`theorem-f-shriek-finite-coefficients--1`);
3. (the finite-Tor clause) `Ri^!` carries bounded constructible complexes of Tor amplitude in
   `[a, b]` to bounded constructible complexes of Tor amplitude in `[a, b + 2d + 1]`
   (`theorem-f-shriek-finite-coefficients--1`).

The open-complement condition used by clauses (2) and (3) is supplied by
`AlgebraicGeometry.Etale.openComplementCondition_two_mul`
(`theorem-f-shriek-finite-coefficients--1`). -/
theorem isLeftAdjoint_and_constructibleIn_and_torAmplitudeIn_of_isClosedImmersion {k : Type u}
    [Field k] {Z T U : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT] (d : ℕ)
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (i : Z ⟶ T) [IsClosedImmersion i]
    [HasCompactification i] (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    (R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint ∧
      (∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b K →
          DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Z a (b + (2 * d : ℕ) + 1)
            ((R(i)^![Λ]).obj K)) ∧
      ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z
              ((R(i)^![Λ]).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + (2 * d : ℕ) + 1)
              ((R(i)^![Λ]).obj K) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have h := openComplementCondition_two_mul (Λ := Λ) aT j d hT
  exact ⟨inferInstance, fun a b K hK ↦ constructibleIn_rightDerivedUpperShriek i j hij h hK,
    fun a b K hK hta ↦ boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek i j hij h hK hta⟩

/-- Blueprint `rem-pur-ambient-only`: The ambient datum of this chapter is a theorem on its
coefficients.

Let `k` be a field and `Λ` a finite ring whose exponent is invertible in `k`. The ambient
exceptional right adjoint datum is not a hypothesis, and the two preservation clauses
(constructibility and finite Tor amplitude) are derived:

1. (the ambient datum) for every compactifiable `f`, `Rf_!` is a left adjoint on the unbounded
   derived categories, so that `Rf^!` exists (`theorem-existence-exceptional-inverse-image--1`);
   and, when `k` is separably closed, the vanishing half of the ambient datum holds on the
   coefficients of étale origin (`theorem-comparison-constructible-sheaves`): for `p : X ⟶ Y` proper
   between finite-type `k`-schemes with `dim X ≤ d`, the class-restricted full
   cohomological-dimension condition holds with the bound `2d`
   (`lemma-uniform-bounds-pro-etale-affines--2`,
   `AlgebraicGeometry.ProEtale.hasCohomologicalDimensionLEOnEtaleOrigin`);
2. (smooth morphisms, `theorem-f-shriek-finite-coefficients`) for `f` smooth of pure relative
dimension
   `d` over a `k`-scheme, `Rf^!` carries `D_c^[a, b]` into `D_c^[a - 2d, b - 2d]` and Tor
   amplitude `[a, b]` to `[a - 2d, b - 2d]`
   (`AlgebraicGeometry.Etale.smooth_preservationClauses`);
3. (closed immersions, without purity input: `lemma-local-cohomology-right-adjoint--1`,
   `theorem-f-shriek-finite-coefficients--1`) for a closed immersion `i` into a
   finite-type `k`-scheme of dimension `≤ d`, `Ri^!` carries `[a, b]` to `[a, b + 2d + 1]` in
   both clauses
   (`Etale.isLeftAdjoint_and_constructibleIn_and_torAmplitudeIn_of_isClosedImmersion`);
4. (separated finite-type morphisms, `theorem-f-shriek-finite-coefficients`,
   `theorem-f-shriek-finite-coefficients--1`) for `f` separated of finite type over a finite-type
   `k`-scheme `Y`, there is `D` such that `Rf^!` carries `[a, b]` to `[a - 2D, b + 2d_Y + 1]` in
   both clauses whenever `dim Y ≤ d_Y`, the open-complement condition being supplied by
   `theorem-f-shriek-finite-coefficients--1` (`AlgebraicGeometry.Etale.exists_preservationClauses`).

The remaining text of the remark (the independence of the chapters and the pointer to the
separate biduality theorem `theorem-verdier-biduality--1`) makes no further formal claim.

In particular, the preservation clauses (2) and (3) of the purity conventions `def-pur-conventions`
are not assumed in the purity chapter; they are the conclusions proved here. -/
theorem ambient_and_preservationClauses {k : Type u} [Field k] (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))] :
    ((∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
      (R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint) ∧
      (IsSepClosed k → ∀ {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
        (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
        [LocallyOfFiniteType aY], p ≫ aY = aX → ∀ d : ℕ,
        topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
        ProEtale.HasCohomologicalDimensionLEOnEtaleOrigin (ModuleCat.{u + 1} Λ) p (2 * d))) ∧
    (∀ {X Y : Scheme.{u}} (_ : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
      [SmoothOfRelativeDimension d f],
      (∀ (a b : ℤ)
        (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
          DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
            ((R(f)^![Λ]).obj L)) ∧
      ∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
              ((R(f)^![Λ]).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
              ((R(f)^![Λ]).obj K)) ∧
    (∀ {Z T U : Scheme.{u}} (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
      (d : ℕ), topologicalKrullDim T ≤ (d : WithBot ℕ∞) → ∀ (i : Z ⟶ T) [IsClosedImmersion i]
      (j : U ⟶ T) [IsOpenImmersion j], Set.range i.base = (Set.range j.base)ᶜ →
      (∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b K →
          DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Z a (b + (2 * d : ℕ) + 1)
            ((R(i)^![Λ]).obj K)) ∧
      ∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z
              ((R(i)^![Λ]).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + (2 * d : ℕ) + 1)
              ((R(i)^![Λ]).obj K)) ∧
    ∀ {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
      (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f],
      ∃ D : ℕ, ∀ dY : ℕ, topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) →
      (∀ (a b : ℤ)
        (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
          DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
            ((R(f)^![Λ]).obj L)) ∧
      ∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
              ((R(f)^![Λ]).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
              ((R(f)^![Λ]).obj K) := by
  refine ⟨⟨fun f _ ↦ inferInstance, fun _ X Y p _ aX aY _ _ hp d hd ↦ ?_⟩, fun aY f _ d _ ↦ ?_,
    fun aT _ _ d hT i _ j _ hij ↦
      (isLeftAdjoint_and_constructibleIn_and_torAmplitudeIn_of_isClosedImmersion aT d hT i j hij
        Λ).2,
    fun aY _ _ f _ _ ↦ exists_preservationClauses Λ aY f⟩
  · have : HasInvertibleExponent Λ X := .of_hom aX
    exact ProEtale.hasCohomologicalDimensionLEOnEtaleOrigin Λ p aX aY hp d hd
  · have : HasInvertibleExponent Λ _ := .of_hom aY
    exact smooth_preservationClauses Λ f d

/-- Blueprint `rem-pur-assembly-status`: Status of the assembly.

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and `f : X ⟶ Y`
separated of finite type (compactifiable and quasi-compact) over a finite-type `k`-scheme `Y`
with `dim Y ≤ d_Y`.

1. The only hypothesis of `theorem-f-shriek-finite-coefficients`
   (`AlgebraicGeometry.Etale.preservationClauses_of_charts`), the open-complement condition
   (`theorem-f-shriek-finite-coefficients--1`) for the open complements `W ⊆ 𝔸ⁿ_V` of the affine
   charts over affine opens `V ⊆ Y`, is a theorem: it holds with the constant `2(d_Y + n)`, which is
   independent of the coefficient ring `Λ` (`theorem-f-shriek-finite-coefficients--1`, derived from
   the direct-image finiteness input `theorem-results-from-etale-theory`).
2. Consequently both preservation clauses hold for `f` without further hypotheses and without
   affineness of `Y` (`theorem-f-shriek-finite-coefficients--1`,
   `AlgebraicGeometry.Etale.exists_preservationClauses`): there is `D` such that `Rf^!` carries
   `D_c^[a, b]` into `D_c^[a - 2D, b + 2d_Y + 1]`, and Tor amplitude `[a, b]` (on bounded
   constructible complexes) to `[a - 2D, b + 2d_Y + 1]`. -/
theorem preservationClauses_assembly {k : Type u} [Field k] (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] (dY : ℕ)
    (hY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) :
    (∀ (V : Y.affineOpens) (n : ℕ) {W : Scheme.{u}}
      (j : W ⟶ 𝔸(ULift.{u} (Fin n); (V : Y.Opens))) [IsOpenImmersion j],
      OpenComplementCondition Λ j (2 * (dY + n))) ∧
    ∃ D : ℕ,
      (∀ (a b : ℤ)
        (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b L →
          DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
            ((R(f)^![Λ]).obj L)) ∧
      ∀ (a b : ℤ)
        (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
              ((R(f)^![Λ]).obj K) ∧
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * dY + 1)
              ((R(f)^![Λ]).obj K) := by
  obtain ⟨D, hD⟩ := exists_preservationClauses Λ aY f
  exact ⟨fun V n _ j _ ↦ openComplementCondition_affineSpace Λ aY dY hY V n j, D, hD dY hY⟩

end Etale

end AlgebraicGeometry
