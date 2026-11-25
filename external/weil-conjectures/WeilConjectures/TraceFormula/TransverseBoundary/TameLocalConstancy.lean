/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DistTriang
public import WeilConjectures.ConstructibleSheaf.ElementaryAbelianCoefficients
public import WeilConjectures.TraceFormula.TransverseBoundary.LocalPurity.LocalConstancy
public import WeilConjectures.TraceFormula.TransverseBoundary.OneDivisor
public import WeilConjectures.TraceFormula.TransverseBoundary.OneDivisorDevissage

/-!
# Local constancy along the boundary divisor

Let `C` be a transverse corner over an algebraically closed field `k`
(`AlgebraicGeometry.Scheme.TransverseCorner`), `ℓ` a prime invertible in `k`, `Λ` a finite
commutative `ℓ`-primary ring and `E` a bounded complex of `Λ`-modules on `Z - (X ∪ Y)` with
finite locally constant cohomology whose monodromy factors through a finite `ℓ`-group. Then
`M = Rj_* i_! E` restricted to `Y - z` has finite locally constant cohomology sheaves: its
stalks are the continuous cohomology of the tame inertia representation of `E` along `Y`, and
the specialization maps between them are isomorphisms (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`).

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.isFiniteLocallyConstantSheaf_homology_boundaryComplex`:
  the cohomology sheaves of `M|_{Y - z}` are finite locally constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]
  (hℓ : (ℓ : k) ≠ 0) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)

include hℓ in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients: for a
finite `Λ`-module `N` killed by `ℓ`, the restriction of `R j_{W*} N` to the regular divisor `Y - z`
of `W = Z - X` has finite locally constant cohomology sheaves. Near every point of `Y - z`, purity
for the regular divisor `Y` of the étale limit of smooth surfaces `Z`
(`Scheme.TransverseCorner.hasFiniteLocallyConstantHomology_puncturedYι_jW_constantZModModule`)
computes `R^q j_* 𝔽_ℓ` as `𝔽_ℓ`, `i_* 𝔽_ℓ(-1)` and `0`, and `N` is a finite direct sum of copies
of `𝔽_ℓ` as an abelian group
(`Scheme.HasFiniteLocallyConstantHomology.constantSheaf_of_constantZModModule`). -/
theorem hasFiniteLocallyConstantHomology_puncturedYι_jW_constantSheaf
    (N : ModuleCat.{u + 1} Λ) [Finite N] (hN : ∀ n : N, (ℓ : Λ) • n = 0) :
    HasFiniteLocallyConstantHomology C.puncturedY
      ((L((C.puncturedYι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((C.jW)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)))) :=
  HasFiniteLocallyConstantHomology.constantSheaf_of_constantZModModule C.jW C.puncturedYι ℓ
    (C.hasFiniteLocallyConstantHomology_puncturedYι_jW_constantZModModule hℓ) N hN

include hℓ hΛ in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`, after the reduction to one
divisor: for `j_W : Z - (X ∪ Y) ⟶ W = Z - X`, the restriction of `R j_{W*} E` to the regular divisor
`Y - z ⊆ W` has finite locally constant cohomology sheaves (tameness along `Y` and Abhyankar's
lemma, Stacks Tag 0EYG). -/
theorem hasFiniteLocallyConstantHomology_puncturedYι_jW
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) :
    HasFiniteLocallyConstantHomology C.puncturedY
      ((L((C.puncturedYι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((C.jW)_*[ModuleCat.{u + 1} Λ])).obj E)) := by
  exact Etale.hasFiniteLocallyConstantHomology_of_constantSheaf ℓ hΛ C.jW C.puncturedYι
    (fun N _ hN ↦ C.hasFiniteLocallyConstantHomology_puncturedYι_jW_constantSheaf hℓ Λ N hN) E hE

include hℓ hΛ in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`: Local constancy along the boundary
divisor. The restriction of `M = Rj_* i_! E` to the punctured divisor `Y - z` has finite locally
constant cohomology sheaves. On `W = Z - X`, which contains `Y - z`, `M` is `R j_{W*} E`
(`AlgebraicGeometry.Scheme.TransverseCorner.leftDerivedUpperStarPuncturedYBoundaryComplexIso`),
and only the regular divisor `Y` remains
(`AlgebraicGeometry.Scheme.TransverseCorner.hasFiniteLocallyConstantHomology_puncturedYι_jW`). -/
theorem isFiniteLocallyConstantSheaf_homology_boundaryComplex
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) (n : ℤ) :
    IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((L((C.puncturedY.ι ≫ C.iY)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E))) := by
  obtain ⟨a, -, ha, -⟩ := hE.1
  exact (C.hasFiniteLocallyConstantHomology_puncturedYι_jW hℓ Λ hΛ E hE).of_iso
    (C.leftDerivedUpperStarPuncturedYBoundaryComplexIso Λ E a).symm n

end AlgebraicGeometry.Scheme.TransverseCorner
