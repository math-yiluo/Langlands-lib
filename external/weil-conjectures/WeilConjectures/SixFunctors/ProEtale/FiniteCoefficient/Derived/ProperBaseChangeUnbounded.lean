/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.BaseChange.UnboundedComparisonBaseChange
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# Proper base change for unbounded classical complexes on the pro-étale site

For finite `ℓ`-primary coefficients and schemes of finite type over the base field, the proper
base change theorem holds for unbounded classical complexes on the pro-étale site.

## Implementation details

The étale statement is
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`
(Stacks Project, Tag 0F0C), and the bounded below pro-étale statement is
`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`. The unbounded pro-étale
statement is transported from the étale one
(`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_comparisonUpperStar`) using the
comparison of unbounded direct images
(`AlgebraicGeometry.ProEtale.isIso_unboundedDirectImageComparisonMap`, still `sorry`): a
classical complex is `K ≅ ν_X^* L` with `L = Rν_* K`
(`AlgebraicGeometry.ProEtale.comparisonUpperStar_isClassicalComplexFor`), and the pro-étale
exchange map at `ν_X^* L` is the étale one conjugated by the comparison maps for `f` and `f'`.
Since the unbounded comparison is applied to `f'` as well as to `f`, it needs `Y'` of finite
type over `k` and `g` a morphism over `k`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- **Proper base change for unbounded classical complexes**: let `k` be a finite or algebraically
closed field, `ℓ` a prime invertible in `k` and `Λ` a finite `ℓ`-primary ring. For a cartesian
square of schemes of finite type over `k`
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `f` proper and every complex `K ∈ D(X_proét, Λ)` with classical cohomology sheaves, the
base change map `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_app_of_isProper_of_isClassicalComplexFor
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hΛ : ∃ r : ℕ, (ℓ : Λ) ^ r = 0)
    {X' X Y' Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : IsClassicalComplexFor X Λ K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨r, hr⟩ := hΛ
  have hcl := (comparisonUpperStar_isClassicalComplexFor k hbase ℓ hℓ Λ
    ⟨r + 1, by omega, by rw [pow_succ, hr, zero_mul]⟩ X).2 K hK
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryRightDerivedAdjunction
  let e : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      ((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerivedFunctor.obj K) ≅ K :=
    asIso (adj.counit.app K)
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  let : X'.Over (Spec (.of k)) := ⟨f' ≫ Y' ↘ Spec (.of k)⟩
  have : f'.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have : LocallyOfFiniteType (X' ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f' ≫ Y' ↘ Spec (.of k)))
  have : QuasiCompact (X' ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (f' ≫ Y' ↘ Spec (.of k)))
  have := Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite sq
  exact isIso_derivedBaseChangeMap_app_comparisonUpperStar Λ sq _ inferInstance
    (isIso_unboundedDirectImageComparisonMap k hbase ℓ hℓ Λ ⟨r, hr⟩ f _)
    (isIso_unboundedDirectImageComparisonMap k hbase ℓ hℓ Λ ⟨r, hr⟩ f' _)

end AlgebraicGeometry.ProEtale
