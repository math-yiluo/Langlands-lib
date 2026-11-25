/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersResidueField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Sites.ModuleLift
public import WeilConjectures.CategoryTheory.ModuleObjects.SectionAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!

# The first derived reduction of integral module objects

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E = 𝒪_E ⧸ π_E`. The residue map `𝒪_E ⟶ 𝔽_E` is a continuous homomorphism onto a discrete
ring, hence induces a morphism of condensed rings `𝒪̲_E ⟶ 𝔽̲_E` and, pulled back to a scheme `X`,
a morphism of coefficient ring objects `𝒪_{E,X} ⟶ 𝔽_{E,X}`
(`ProEtale.padicIntegersToResidueField`). The residue field `𝔽_E` acts on every module object over
`𝔽_{E,X}` through the constant global sections, so that such a module object is a pro-étale sheaf
of `𝔽_E`-modules (`ProEtale.residueFieldModuleSheaf`). The *first derived reduction*
`K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of blueprint `definition-derived-adic-completeness`, as a complex of
pro-étale sheaves of `𝔽_E`-modules, is `ProEtale.derivedReduction`.

-/
@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

open _root_.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The residue map `𝒪̲_E ⟶ 𝔽̲_E` of ring objects of condensed abelian groups, induced by the
continuous residue map `𝒪_E ⟶ 𝔽_E` onto the discrete residue field. -/
noncomputable def padicIntegersRingObjToResidueField :
    padicIntegersRingObj.{u} ℓ E ⟶ continuousMapRingObj (integersResidueField ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (integersResidue ℓ E) (continuous_integersResidue ℓ E))

instance : IsMonHom (padicIntegersRingObjToResidueField.{u} ℓ E) :=
  letI := normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (integersResidue ℓ E) (continuous_integersResidue ℓ E))))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The coefficient ring object `𝔽_{E,X} = p_X^* 𝔽̲_E` on `X_proét`. -/
noncomputable abbrev residueFieldRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E)) X

/-- The residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}` of coefficient ring objects on `X_proét`: the pullback
along `p_X` of the residue map `𝒪̲_E ⟶ 𝔽̲_E` of condensed rings. -/
noncomputable abbrev padicIntegersToResidueField :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X ⟶ residueFieldRingObj X ℓ E :=
  coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E) X

/-- The residue field `𝔽_E`, lifted to the universe `u + 1` of the coefficient rings of pro-étale
sheaves of modules on `u`-schemes. -/
def ResidueFieldCoeff : Type (u + 1) :=
  ULift.{u + 1} (integersResidueField ℓ E)

noncomputable instance : CommRing (ResidueFieldCoeff.{u} ℓ E) :=
  inferInstanceAs (CommRing (ULift.{u + 1} (integersResidueField ℓ E)))

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The prime `ℓ` is zero in `𝔽_E`. -/
lemma natCast_eq_zero_residueFieldCoeff : ((ℓ : ℕ) : ResidueFieldCoeff.{u} ℓ E) = 0 :=
  ULift.ext (natCast_eq_zero_integersResidueField ℓ E)

/-- The constants `𝔽_E ⟶ Γ(𝔽_{E,X})`: an element of the residue field `𝔽_E` is the constant
function `X → 𝔽_E`, a global section of `𝔽_{E,X} = C(-, 𝔽_E)_X`
(`ProEtale.continuousMapCoefficientSectionRingHom`). -/
noncomputable def residueFieldSectionRingHom :
    ResidueFieldCoeff.{u} ℓ E →+* Γ (residueFieldRingObj X ℓ E) :=
  (continuousMapCoefficientSectionRingHom X (integersResidueField ℓ E)).comp
    ((algebraMap (integersResidueField ℓ E) C(X, integersResidueField ℓ E)).comp
      (ULift.ringEquiv : ULift.{u + 1} (integersResidueField ℓ E) ≃+* _).toRingHom)

/-- An `𝔽_{E,X}`-module object, regarded as a pro-étale sheaf of `𝔽_E`-modules: `𝔽_E` acts through
the constant global sections of `𝔽_{E,X}` (`ProEtale.residueFieldSectionRingHom`). -/
noncomputable def residueFieldModuleSheaf :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) :=
  Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))

instance : (residueFieldModuleSheaf X ℓ E).Additive :=
  inferInstanceAs (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))).Additive

instance : PreservesFiniteLimits (residueFieldModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteLimits (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))))

instance : PreservesFiniteColimits (residueFieldModuleSheaf X ℓ E) :=
  inferInstanceAs (PreservesFiniteColimits (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (residueFieldSectionRingHom X ℓ E c))))

instance : (residueFieldModuleSheaf X ℓ E).ReflectsIsomorphisms :=
  inferInstanceAs (Sheaf.moduleLift (Mod.forget _)
    (fun M ↦ (Mod.sectionActRingHom M).comp (residueFieldSectionRingHom X ℓ E))
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f
      (residueFieldSectionRingHom X ℓ E c))).ReflectsIsomorphisms

/-- The **first derived reduction** `K ↦ K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of complexes of
`𝒪_{E,X}`-module objects (blueprint `definition-derived-adic-completeness`), regarded in the derived
category of pro-étale sheaves of `𝔽_E`-modules: the derived extension of scalars along the
residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}`, followed by the exact functor
`ProEtale.residueFieldModuleSheaf`. -/
noncomputable def derivedReduction :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))) :=
  (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor ⋙
    (residueFieldModuleSheaf X ℓ E).mapDerivedCategory

end AlgebraicGeometry.ProEtale
