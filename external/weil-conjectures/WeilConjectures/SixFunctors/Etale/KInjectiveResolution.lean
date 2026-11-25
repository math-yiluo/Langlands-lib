/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# K-injective resolutions of complexes of étale sheaves

Every complex of étale sheaves (for instance of sheaves of `R`-modules) admits a K-injective
resolution, functorially; two K-injective resolutions of one complex are chain-homotopy
equivalent; and a bounded-below complex of injective objects is K-injective
(`AlgebraicGeometry.Etale.kInjectiveResolutions_exist`, blueprint
`prop-weil-pbc-kinjective-resolutions-exist`).

The three statements are instances of general facts on Grothendieck abelian categories:
the functorial K-injective replacement `CochainComplex.kInjectiveResolutionFunctor`, the
uniqueness `CochainComplex.IsKInjective.nonempty_iso_quotient_obj` in the homotopy category, and
`CochainComplex.isKInjective_of_injective`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Etale

/-- Blueprint `prop-weil-pbc-kinjective-resolutions-exist`: Existence of K-injective resolutions.

Let `A` be a Grothendieck abelian coefficient category (for instance `ModuleCat R`) and `X` a
scheme. Then, for complexes of `A`-valued étale sheaves on `X`:
1. there is a functorial K-injective resolution: a functor `I` with a natural transformation
   `K ⟶ I K` which is a quasi-isomorphism into a K-injective complex for every `K` (functorial on
   the nose, in particular up to chain homotopy);
2. two K-injective resolutions `K ⟶ I`, `K ⟶ J` of one complex are chain-homotopy equivalent;
3. a bounded-below complex of injective objects is K-injective. -/
theorem kInjectiveResolutions_exist (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    (∃ (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ ⥤
        CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
        (ι : 𝟭 (CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) ⟶ I),
        ∀ K, QuasiIso (ι.app K) ∧ (I.obj K).IsKInjective) ∧
    (∀ {K I J : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ} (s : K ⟶ I) (t : K ⟶ J)
      [QuasiIso s] [QuasiIso t] [I.IsKInjective] [J.IsKInjective],
      Nonempty (HomotopyEquiv I J)) ∧
    ∀ (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (d : ℤ) [I.IsStrictlyGE d]
      [∀ n, Injective (I.X n)], I.IsKInjective := by
  refine ⟨⟨CochainComplex.kInjectiveResolutionFunctor.{u + 1} _,
    CochainComplex.toKInjectiveResolution.{u + 1} _, fun K ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ K).2, inferInstance⟩⟩,
    fun s t _ _ _ _ ↦ ?_, fun I d _ _ ↦ CochainComplex.isKInjective_of_injective I d⟩
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology A)
  obtain ⟨e⟩ := CochainComplex.IsKInjective.nonempty_iso_quotient_obj s t
  exact ⟨HomotopyCategory.homotopyEquivOfIso e⟩

end Etale

end AlgebraicGeometry
