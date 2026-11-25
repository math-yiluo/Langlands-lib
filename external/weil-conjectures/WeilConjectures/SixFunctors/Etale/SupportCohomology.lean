/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport

/-!
# Cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. The functor of
*sections with support in `Z`* sends a sheaf `F` on `X` to

`Γ_Z(X, F) = ker (Γ(X, F) ⟶ F(U))`,

the global sections whose restriction to the open complement vanishes. The *cohomology with
support* `H^q_Z(X, F)` is its `q`-th right derived functor, and for complexes it is the
`q`-th cohomology object of the total right derived functor `RΓ_Z(X, -)` on the derived
category (blueprint `definition-local-cohomology`).

The functor of sections with support is defined for an arbitrary site `(C, J)` with global
sections and an object `U` of `C` (`CategoryTheory.Sheaf.ΓSupport`), and specialised to the
small étale site (`AlgebraicGeometry.Etale.globalSectionsWithSupport`) and to the small pro-étale
site (`AlgebraicGeometry.ProEtale.globalSectionsWithSupport`), where `U` is the open complement of
`Z`.

## Main definitions

- `CategoryTheory.Sheaf.ΓSupport`: the sections with support away from an object `U`.
- `AlgebraicGeometry.Etale.globalSectionsWithSupport`, `AlgebraicGeometry.Etale.supportCohomology`,
  `AlgebraicGeometry.Etale.rightDerivedSectionsWithSupport`,
  `AlgebraicGeometry.Etale.derivedSupportCohomology`: `Γ_Z(X, -)`, `H^q_Z(X, -)` on sheaves,
  `RΓ_Z(X, -)` and `H^q_Z(X, -)` on the derived category of the small étale site.
- `AlgebraicGeometry.ProEtale.globalSectionsWithSupport`,
  `AlgebraicGeometry.ProEtale.supportCohomology`,
  `AlgebraicGeometry.ProEtale.rightDerivedSectionsWithSupport`,
  `AlgebraicGeometry.ProEtale.derivedSupportCohomology`: the same on the small pro-étale site.
-/

@[expose] public section

universe u' u v w

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable [HasSmallSiteSheafify A] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The functor `Γ_Z(X, -)` of sections with support in the closed subscheme `i : Z ⟶ X` of étale
sheaves on `X`: `Γ_Z(X, F) = ker (Γ(X, F) ⟶ F(U))` for the open complement `U` of `Z`. -/
noncomputable def globalSectionsWithSupport : Sheaf X.smallEtaleTopology A ⥤ A :=
  Sheaf.ΓSupport X.smallEtaleTopology A (op (Scheme.Etale.mk i.openComplement.ι))

instance : (globalSectionsWithSupport A i).Additive := by
  dsimp [globalSectionsWithSupport]; infer_instance

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, F)` of an étale sheaf `F` on `X`: the `q`-th right
derived functor of the sections with support in `Z`. -/
noncomputable def supportCohomology (q : ℕ) : Sheaf X.smallEtaleTopology A ⥤ A :=
  (globalSectionsWithSupport A i).rightDerived q

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The derived sections with support `RΓ_Z(X, -) : D(X_ét) ⥤ D(A)`, the total right derived
functor of the sections with support in `Z`. -/
noncomputable def rightDerivedSectionsWithSupport :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  (globalSectionsWithSupport A i).rightDerivedFunctor

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, K) = H^q(RΓ_Z(X, K))` of a complex `K` of étale sheaves
on `X`. -/
noncomputable def derivedSupportCohomology (q : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  rightDerivedSectionsWithSupport A i ⋙ DerivedCategory.homologyFunctor A q

end Etale

namespace ProEtale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The functor `Γ_Z(X, -)` of sections with support in the closed subscheme `i : Z ⟶ X` of
sheaves on the small pro-étale site of `X`: `Γ_Z(X, F) = ker (Γ(X, F) ⟶ F(U))` for the open
complement `U` of `Z`. -/
noncomputable def globalSectionsWithSupport : Sheaf (Scheme.ProEt.topology X) A ⥤ A :=
  Sheaf.ΓSupport (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk i.openComplement.ι))

instance : (globalSectionsWithSupport A i).Additive := by
  dsimp [globalSectionsWithSupport]; infer_instance

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, F)` of a pro-étale sheaf `F` on `X`: the `q`-th right
derived functor of the sections with support in `Z`. -/
noncomputable def supportCohomology (q : ℕ) : Sheaf (Scheme.ProEt.topology X) A ⥤ A :=
  (globalSectionsWithSupport A i).rightDerived q

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The derived sections with support `RΓ_Z(X, -) : D(X_proét) ⥤ D(A)`. -/
noncomputable def rightDerivedSectionsWithSupport :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ DerivedCategory A :=
  (globalSectionsWithSupport A i).rightDerivedFunctor

/-- Blueprint `definition-local-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, K) = H^q(RΓ_Z(X, K))` of a complex `K` of pro-étale
sheaves on `X`. -/
noncomputable def derivedSupportCohomology (q : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ A :=
  rightDerivedSectionsWithSupport A i ⋙ DerivedCategory.homologyFunctor A q

end ProEtale

end AlgebraicGeometry
