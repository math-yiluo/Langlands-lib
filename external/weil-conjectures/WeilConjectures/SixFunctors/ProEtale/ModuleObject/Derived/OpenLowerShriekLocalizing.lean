/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Extension by zero on `Loc(Dbc(-, Λ))` for module objects over `Λ`

Let `Λ` be a commutative condensed ring (the `ℓ`-adic coefficient rings `𝒪̲_E`, `E̲`, `ℚ̲̄_ℓ`,
for which `Dctf = Dbc`) and `j : U ⟶ X` an open immersion of separated finite-type schemes over
a field `k`. The extension by zero `j_! = D((j)_!open⟦Λ⟧)` on module objects over `Λ_X` maps
`Dbc(U, Λ)` into `Dbc(X, Λ)` (the extension-by-zero part of `sk-def-sfb-dc-restricted-functors`,
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_openImmersionLowerShriek_obj`),
preserves direct sums (it is left adjoint to `j^*`) and hence maps the localizing closure
`Loc(Dbc(U, Λ))` into `Loc(Dbc(X, Λ))`
(`localizingClosure_boundedConstructible_openImmersionLowerShriek` in the namespace
`AlgebraicGeometry.ProEtale.CondensedRing`,
blueprint `proposition-proper-direct-image-extension-zero` at the `ℓ`-adic stages; the finite stages
are `AlgebraicGeometry.ProEtale.localizingClosure_constructibleFiniteTor_openImmersionLowerShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` on module objects preserves direct sums, being left adjoint to
`j^*`. -/
instance (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) D((j.left)_!open⟦Λ⟧) :=
  have : PreservesColimitsOfSize.{u + 1, u + 1} D((j.left)_!open⟦Λ⟧) :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).leftAdjoint_preservesColimits
  inferInstance

include ℓ in
/-- Blueprint `proposition-proper-direct-image-extension-zero`: Extension by zero on the localizing
categories, at the `ℓ`-adic stages.

For a commutative condensed ring `Λ` (such as `𝒪̲_E`, `E̲` or `ℚ̲̄_ℓ`, for which
`Dctf(-, Λ) = Dbc(-, Λ)`) and an open immersion `j : U ⟶ X` of separated finite-type
`k`-schemes, the extension by zero `j_! : D(U_proét, Λ) ⥤ D(X_proét, Λ)` maps `Dbc(U, Λ)` into
`Dbc(X, Λ)`, preserves direct sums, and maps `Loc(Dbc(U, Λ))` into `Loc(Dbc(X, Λ))`; it is
exact, being induced by an exact functor. The first assertion is the extension-by-zero part of
`proposition-proper-direct-image-extension-zero`; the last one follows by
`proposition-proper-direct-image-extension-zero`. -/
theorem localizingClosure_boundedConstructible_openImmersionLowerShriek :
    boundedConstructible (condensedRingObj Λ U.left) ≤
        (boundedConstructible (condensedRingObj Λ X.left)).inverseImage
          D((j.left)_!open⟦Λ⟧) ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) D((j.left)_!open⟦Λ⟧)) ∧
      (boundedConstructible (condensedRingObj Λ U.left)).localizingClosure ≤
        ((boundedConstructible (condensedRingObj Λ X.left)).localizingClosure
          ).inverseImage D((j.left)_!open⟦Λ⟧) :=
  ⟨fun K hK ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j ⟨K, hK⟩,
    fun _ ↦ inferInstance,
    ObjectProperty.localizingClosure_le_inverseImage _ _ fun K hK ↦
      ObjectProperty.le_localizingClosure _ _
        (boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j ⟨K, hK⟩)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
