/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided

/-!
# Braided extensions of scalars on bounded constructible complexes

Let `P` and `Q` be monoidal properties of objects of braided monoidal categories `C` and `D`, and
`F : C ⥤ D` a strong monoidal functor compatible with the braidings and sending objects
satisfying `P` to objects satisfying `Q`. The restriction `Q.lift (P.ι ⋙ F) hF`, with its strong
monoidal structure `CategoryTheory.ObjectProperty.monoidalLift`, is then lax braided for the
braidings `CategoryTheory.ObjectProperty.fullBraidedSubcategory`.

We apply this to the extensions of scalars `Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` and the
Koszul braidings `DerivedCategory.braidedCategory'`.

## Main definitions

- `CategoryTheory.ObjectProperty.laxBraidedLift`: the lax braided structure on the restriction
  of a braided strong monoidal functor to full monoidal subcategories.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExtendScalarsLaxBraided` and
  `AlgebraicGeometry.ProEtale.CondensedRing.constructibleToPadicAlgClLaxBraided`: the lax
  braided structures on the extensions of scalars on bounded constructible complexes.
-/

@[expose] public section

universe u

namespace CategoryTheory.ObjectProperty

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- The restriction `Q.lift (P.ι ⋙ F)` of a strong monoidal functor `F` compatible with the
braidings to full monoidal subcategories is lax braided, for the braidings
`fullBraidedSubcategory`, with the lax monoidal structure of `monoidalLift`. -/
@[instance_reducible]
noncomputable def laxBraidedLift
    (hβ : ∀ X Y : C, μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X) :
    (Q.lift (P.ι ⋙ F) hF).LaxBraided where
  toLaxMonoidal := (monoidalLift F hF).toLaxMonoidal
  braided X Y := hom_ext _ (hβ X.obj Y.obj)

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory MonoidalCategory Scheme

open scoped CategoryTheory.Functor CategoryTheory.Obj

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

attribute [local instance] DerivedCategory.braidedCategory'

/-- The extension of scalars `E ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` is lax braided for the
Koszul braidings, with the lax monoidal structure of
`monoidal_boundedConstructibleExtendScalars`, as the ambient derived extension of scalars is
(`leftDerivedExtendScalarsPadicIntegersBraided`). -/
@[instance_reducible]
noncomputable def boundedConstructibleExtendScalarsLaxBraided :
    (boundedConstructibleExtendScalars X.left ℓ E).LaxBraided :=
  letI := leftDerivedExtendScalarsPadicIntegersMonoidal ℓ E X.left
  ObjectProperty.laxBraidedLift (P := boundedConstructible _) (Q := boundedConstructible _)
    (Mod.extendScalars (padicIntegersToPadicSubfield X.left ℓ E)).leftDerivedFunctor
    (boundedConstructible_derivedExtendScalars_obj X.left ℓ E)
    (leftDerivedExtendScalarsPadicIntegersBraided ℓ E X.left).braided

/-- The extension of scalars `ℚ̄_ℓ ⊗ᴸ_E - : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` is lax braided for the
Koszul braidings, with the lax monoidal structure of `monoidal_constructibleToPadicAlgCl`, as the
ambient derived extension of scalars is (`leftDerivedExtendScalarsPadicAlgClBraided`). -/
@[instance_reducible]
noncomputable def constructibleToPadicAlgClLaxBraided :
    (constructibleToPadicAlgCl X.left ℓ E).LaxBraided :=
  letI := leftDerivedExtendScalarsPadicAlgClMonoidal ℓ E X.left
  ObjectProperty.laxBraidedLift (P := boundedConstructible _) (Q := boundedConstructible _)
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X.left ℓ E)).leftDerivedFunctor
    (boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X.left ℓ E)
    (leftDerivedExtendScalarsPadicAlgClBraided ℓ E X.left).braided

end AlgebraicGeometry.ProEtale.CondensedRing
