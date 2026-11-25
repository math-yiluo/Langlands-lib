/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!

# The `ℓ`-adic extensions of scalars are monoidal

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`X` a scheme. The derived extensions of scalars along the coefficient maps
`𝒪_{E,X} ⟶ E_X ⟶ ℚ̄_ℓ,X`,
```
E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X}),   ℚ̄_ℓ ⊗ᴸ_E - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X}),
```
are strong monoidal for the derived tensor products
(`ProEtale.CondensedRing.leftDerivedExtendScalarsPadicIntegersMonoidal`,
`ProEtale.CondensedRing.leftDerivedExtendScalarsPadicAlgClMonoidal`), and so are their
restrictions to the bounded constructible complexes
`ProEtale.boundedConstructibleExtendScalars` and `ProEtale.constructibleToPadicAlgCl`
(blueprint `proposition-six-operations-change-coefficients`, clause (1):
`(K ⊗ M)_{Λ'} ≅ K_{Λ'} ⊗ M_{Λ'}`). They are moreover braided for the Koszul braidings
`DerivedCategory.braidedCategory'`.

These are instances of `Functor.leftDerivedFunctorMonoidal`: extension of scalars is strong
monoidal (`Mod.extendScalarsMonoidal`), preserves flat objects (`Mod.preservesFlat_extendScalars`)
and the quasi-isomorphisms between K-flat complexes (`Mod.preservesKFlatQuasiIso`), and is a left
adjoint.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

section Derived

variable (X : Scheme.{u})

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is
monoidal, with comonoidal structure the tensor comparison `Functor.leftDerivedTensorComparison`
(`Functor.leftDerivedFunctorMonoidal_δ`). -/
@[instance_reducible]
noncomputable def leftDerivedExtendScalarsPadicIntegersMonoidal :
    L(Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).Monoidal :=
  letI := Mod.extendScalarsMonoidal (padicIntegersToPadicSubfield X ℓ E)
  (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctorMonoidal

/-- The derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_E - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` is monoidal,
with comonoidal structure the tensor comparison `Functor.leftDerivedTensorComparison`
(`Functor.leftDerivedFunctorMonoidal_δ`). -/
@[instance_reducible]
noncomputable def leftDerivedExtendScalarsPadicAlgClMonoidal :
    L(Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).Monoidal :=
  letI := Mod.extendScalarsMonoidal (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorMonoidal


section Braided

attribute [local instance] DerivedCategory.braidedCategory'

/-- The braided structure on the derived extension of scalars `E ⊗ᴸ_{𝒪_E} -`, for the Koszul
braidings `DerivedCategory.braidedCategory'`, whose monoidal structure is
`leftDerivedExtendScalarsPadicIntegersMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedExtendScalarsPadicIntegersBraided :
    L(Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).Braided :=
  letI := Mod.extendScalarsMonoidal (padicIntegersToPadicSubfield X ℓ E)
  (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctorBraided
    (Mod.extendScalars_map_braiding_hom_δ (padicIntegersToPadicSubfield X ℓ E))

/-- The braided structure on the derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_E -`, for the Koszul
braidings `DerivedCategory.braidedCategory'`, whose monoidal structure is
`leftDerivedExtendScalarsPadicAlgClMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedExtendScalarsPadicAlgClBraided :
    L(Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).Braided :=
  letI := Mod.extendScalarsMonoidal (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorBraided
    (Mod.extendScalars_map_braiding_hom_δ (padicSubfieldRingObjToPadicAlgCl X ℓ E))

end Braided

end Derived

/-! ### The bounded constructible complexes -/

section BoundedConstructible

variable {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` on bounded
constructible complexes is strong monoidal, with the comparison isomorphisms of
`leftDerivedExtendScalarsPadicIntegersMonoidal`. -/
noncomputable instance monoidal_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X.left ℓ E).Monoidal := by
  letI := leftDerivedExtendScalarsPadicIntegersMonoidal ℓ E X.left
  unfold boundedConstructibleExtendScalars
  exact ObjectProperty.monoidalLift _ _

/-- The derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_E - : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded
constructible complexes is strong monoidal, with the comparison isomorphisms of
`leftDerivedExtendScalarsPadicAlgClMonoidal`. -/
noncomputable instance monoidal_constructibleToPadicAlgCl :
    (constructibleToPadicAlgCl X.left ℓ E).Monoidal := by
  letI := leftDerivedExtendScalarsPadicAlgClMonoidal ℓ E X.left
  unfold constructibleToPadicAlgCl
  exact ObjectProperty.monoidalLift _ _

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
