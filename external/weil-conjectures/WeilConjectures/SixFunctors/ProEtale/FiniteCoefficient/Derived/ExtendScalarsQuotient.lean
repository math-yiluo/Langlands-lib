/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Derived extension of scalars of pro-étale sheaves along a quotient map

Let `φ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel `(a)`,
for instance `𝒪_E ⧸ ℓⁿ ⟶ 𝔽_E`, and let `X` be a scheme. The extension of scalars of pro-étale
sheaves `Λ' ⊗_Λ -` sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms; its
total left derived functor `K ↦ K ⊗ᴸ_Λ Λ'` (`AlgebraicGeometry.ProEtale.derivedExtendScalars`) is
left adjoint to the derived restriction of scalars
(`AlgebraicGeometry.ProEtale.derivedExtendScalarsAdjunction`), and with scalars restricted back
to `Λ` it is the derived tensor product with the constant sheaf `Λ ⧸ (a)`
(`AlgebraicGeometry.ProEtale.nonempty_iso_derivedRestrictScalars_derivedExtendScalars`).

This is the pro-étale counterpart of the corresponding statements of
`WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`, with the same proofs.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`: with these instances, instance
-- search produces exactly the monoidal structure underlying the derived tensor product of
-- pro-étale sheaves.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- The pro-étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  inferInstance

/-- Sheaves of modules on the pro-étale site have countable coproducts. -/
local instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}

/-- Extension of scalars of pro-étale sheaves along a surjective ring morphism with principal
kernel sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms: with scalars
restricted back, it is tensoring with a constant sheaf. -/
lemma preservesKFlatQuasiIso_extendScalars (hφ : Function.Surjective φ) {a : Λ}
    (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u}) :
    (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ :=
    have := Sheaf.reflectsIsomorphisms_restrictScalars (Scheme.ProEt.topology X) φ
    CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsQuotientIso (Scheme.ProEt.topology X) hφ ha) f hK hL

variable (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

/-- The derived extension of scalars `K ↦ K ⊗ᴸ_Λ Λ'`, from `D(X_proét, Λ)` to `D(X_proét, Λ')`,
along a surjective ring morphism `φ : Λ →+* Λ'` with principal kernel: the total left derived
functor of the extension of scalars of pro-étale sheaves. -/
noncomputable def derivedExtendScalars :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ')) :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedFunctor

/-- The derived extension of scalars of pro-étale sheaves is left adjoint to the derived
restriction of scalars. -/
noncomputable def derivedExtendScalarsAdjunction :
    derivedExtendScalars hφ ha X ⊣ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  (Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).rightDerivedFunctorIsoMapDerivedCategory

-- the kernel checks the ten isomorphisms of the chain below
/-- With scalars restricted back to `Λ`, the derived extension of scalars `K ⊗ᴸ_Λ Λ'` of
pro-étale sheaves is the derived tensor product `K ⊗ᴸ (Λ ⧸ ker φ)_X` with the constant sheaf: on a
K-flat complex `P` both are computed by the complex `P ⊗ (Λ ⧸ ker φ)_X`. -/
lemma nonempty_iso_derivedRestrictScalars_derivedExtendScalars
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    Nonempty ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj
        ((derivedExtendScalars hφ ha X).obj L) ≅
      L ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ RingHom.ker φ)))) := by
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  have : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  let F := Sheaf.extendScalars (Scheme.ProEt.topology X) φ
  let R := Sheaf.restrictScalars (Scheme.ProEt.topology X) φ
  let c := (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (Λ ⧸ RingHom.ker φ))
  obtain ⟨P, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso L
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P').1 hP
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P' hP'
  have := _root_.DerivedCategory.isIso_tensorLeftCounit _ hP
  let S := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj c
  let i1 := R.mapDerivedCategory.mapIso ((derivedExtendScalars hφ ha X).mapIso e.symm)
  let i2 := R.mapDerivedCategory.mapIso
      (asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P')))
  let i3 := R.mapDerivedCategory.mapIso
      (_root_.DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors _).app P') ≪≫
        (_root_.DerivedCategory.quotientCompQhIso _).app ((F.mapHomologicalComplex _).obj P'))
  let i4 := R.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex _).obj P')
  let i5 := (Functor.mapHomologicalComplexCompIso
          (Sheaf.extendScalarsCompRestrictScalarsQuotientIso (Scheme.ProEt.topology X) hφ ha)
          _).app P'
  let i6 := ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _) c).app
          P').symm
  let i7 := ((_root_.DerivedCategory.quotientCompQhIso _).app (P' ⊗ S)).symm
  let i8 := _root_.DerivedCategory.Qh.mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) P' S).symm
  let i9 := (asIso ((_root_.DerivedCategory.tensorLeftCounit
      ((HomotopyCategory.quotient _ _).obj P')).app
      ((HomotopyCategory.quotient _ _).obj S))).symm
  let i10 := tensorIso e ((_root_.DerivedCategory.quotientCompQhIso _).app S ≪≫
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app c).symm)
  exact ⟨i1 ≪≫ i2 ≪≫ i3 ≪≫ i4 ≪≫ _root_.DerivedCategory.Q.mapIso (i5 ≪≫ i6) ≪≫ i7 ≪≫ i8 ≪≫
    i9 ≪≫ i10⟩

end ProEtale

end AlgebraicGeometry
