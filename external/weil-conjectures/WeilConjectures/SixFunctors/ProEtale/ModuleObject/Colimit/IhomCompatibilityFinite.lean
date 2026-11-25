/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimitIhom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibilityFiniteAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitMonoidal

/-!

# The internal Hom comparison for `E ⟶ ℚ̄_ℓ` on bounded constructible complexes

Let `X` be a separated `k`-scheme of finite type, `char k ≠ ℓ`.

* For finite subextensions `E ≤ F` of `ℚ̄_ℓ`, the extension of scalars
  `T_{E,F} : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦F⟧` commutes with internal homs
  (`ProEtale.CondensedRing.isIso_ihomComparison_constructibleExtendScalars`): this is the
  ambient statement `ProEtale.CondensedRing.isIso_ihomComparison_derivedExtendScalarsSubfield`,
  the internal hom of `Dᵇc` being the restriction of the ambient one.
* Hence, `Dᵇc(X)⟦ℚ̄_ℓ⟧` being the filtered 2-colimit of the `Dᵇc(X)⟦E⟧`
  (`ProEtale.constructibleCocone_isFilteredTwoColimit`), with monoidal transition functors and
  structure isomorphisms (`ProEtale.CondensedRing.isMonoidal_constructibleToPadicAlgClCompIso_hom`),
  the extension of scalars `Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` commutes with internal homs
  (`ProEtale.CondensedRing.isIso_ihomComparison_constructibleToPadicAlgCl_of_twoColimit`, by
  `CategoryTheory.CategoryCocone.isIso_ihomComparison_Φ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The internal Hom comparison for `E ⊆ F`** on bounded constructible complexes: for finite
subextensions `E ≤ F` of `ℚ̄_ℓ`, the extension of scalars `Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦F⟧` commutes with
internal homs. -/
theorem isIso_ihomComparison_constructibleExtendScalars
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (A : PadicSubfieldConstructible X.left ℓ E) :
    IsIso
      (Functor.LaxMonoidal.ihomComparison (constructibleExtendScalars X.left ℓ h) A) := by
  let := leftDerivedExtendScalarsSubfieldMonoidal ℓ X.left h
  have hamb := isIso_ihomComparison_derivedExtendScalarsSubfield ℓ X.left h A.obj
  exact ObjectProperty.isIso_ihomComparison_monoidalLift _ _ A fun B ↦ inferInstance

/-- The monoidal structures of the functors to the vertex of the cocone of bounded constructible
complexes over the finite subextensions. -/
@[instance_reducible]
noncomputable def constructibleCoconeΦMonoidal (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ((constructibleCocone X.left ℓ).Φ E).Monoidal :=
  inferInstanceAs (constructibleToPadicAlgCl X.left ℓ E).Monoidal

/-- The monoidal structures of the transition functors of the cocone of bounded constructible
complexes over the finite subextensions. -/
@[instance_reducible]
noncomputable def constructibleCoconeTMonoidal (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    (h : E ≤ F) : ((constructibleCocone X.left ℓ).T h).Monoidal :=
  inferInstanceAs (constructibleExtendScalars X.left ℓ h).Monoidal

/-- **The internal Hom comparison for `E ⟶ ℚ̄_ℓ`**, through the 2-colimit: for
`A ∈ Dᵇc(X)⟦E⟧`, the comparison `T RHom(A, -) ⟶ RHom(T A, T -)` is an isomorphism. -/
theorem isIso_ihomComparison_constructibleToPadicAlgCl_of_twoColimit
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (A : PadicSubfieldConstructible X.left ℓ E) :
    IsIso
      (Functor.LaxMonoidal.ihomComparison (constructibleToPadicAlgCl X.left ℓ E) A) := by
  have := noetherianSpace_left_of_over X
  let := constructibleCoconeΦMonoidal ℓ X
  let := constructibleCoconeTMonoidal ℓ X
  have (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) :
      NatTrans.IsMonoidal ((constructibleCocone X.left ℓ).iso h).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (constructibleToPadicAlgClCompIso X.left ℓ h).hom)
  exact CategoryCocone.isIso_ihomComparison_Φ (constructibleCocone X.left ℓ)
    (ProEtale.constructibleCocone_isFilteredTwoColimit X.left ℓ)
    (fun _ _ h A ↦ isIso_ihomComparison_constructibleExtendScalars ℓ X h A) E A

end AlgebraicGeometry.ProEtale.CondensedRing
