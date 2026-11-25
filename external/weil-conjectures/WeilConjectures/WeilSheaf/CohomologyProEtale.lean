/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.CohomologyExact
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Cohomology of a Weil sheaf as pro-étale sheaf cohomology

Let `F` be a Weil sheaf on a `k₀`-scheme `Y` of finite type, with structure morphism
`a : Y ⟶ Spec k₀` and geometric fiber `ā : Ȳ ⟶ Spec k̄`. Its cohomology
`Hʳ(Y ⊗ k̄, F) = Γ(Spec k̄, 𝓗ʳ(Ra_* F))` (`AlgebraicGeometry.WeilSheaf.cohomology`) is, forgetting
the Frobenius, the pro-étale cohomology `Rʳ Γ(Ȳ_proét, F)` of the underlying sheaf of
`ℚ̄_ℓ`-modules: forgetting the Weil structure and the `ℚ̄_ℓ,Ȳ`-module structure commutes with
`Rā_*`, the global sections functor of `Spec k̄_proét` is exact, and `Γ(Spec k̄, ā_* -) = Γ(Ȳ, -)`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.cohomologyIsoRightDerivedGlobalSections`: the isomorphism
  `Hʳ(Y ⊗ k̄, F) ≅ Rʳ Γ(Ȳ_proét, F)` of `ℚ̄_ℓ`-modules.
- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_of_isZero_rightDerived`: the resulting
  vanishing criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

instance preservesFiniteColimits_Γ_geometricFiber_spec :
    PreservesFiniteColimits (Sheaf.Γ (Scheme.ProEt.topology
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)) := by
  have : (Sheaf.Γ (Scheme.ProEt.topology
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

namespace WeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The underlying sheaf of `ℚ̄_ℓ`-modules on the pro-étale site of the geometric fiber of a
Weil sheaf. -/
noncomputable abbrev underlyingSheaf (F : WeilSheaf k₀ l Y) :
    Sheaf (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) :=
  (ProEtale.AdicSheaf.forget _).obj F.carrier

/-- The functor taking global sections over `Spec k̄` of the underlying sheaf of a Weil sheaf on
`Spec k₀`, whose `ℚ̄_ℓ`-module structure is the carrier of
`AlgebraicGeometry.WeilSheaf.globalSections`. -/
noncomputable abbrev globalSectionsUnderlyingFunctor :
    WeilSheaf k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilCoefficients.{u} l :=
  ObjectProperty.ι _ ⋙ IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
    Sheaf.Γ _ (WeilCoefficients.{u} l)

/-- **Weil cohomology is pro-étale cohomology.** For a Weil sheaf `F` on `Y`, the underlying
`ℚ̄_ℓ`-module of `Hʳ(Y ⊗ k̄, F) = Γ(Spec k̄, 𝓗ʳ(Ra_* F))` is the pro-étale cohomology
`Rʳ Γ(Ȳ_proét, F)` of the underlying sheaf of `ℚ̄_ℓ`-modules on the geometric fiber `Ȳ`. -/
noncomputable def cohomologyIsoRightDerivedGlobalSections (F : WeilSheaf k₀ l Y) (r : ℕ) :
    globalSectionsUnderlyingFunctor.obj ((WeilComplex.homologySheaf (r : ℤ)).obj
        ((WeilComplex.derivedLowerStar (Y ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F))) ≅
      ((Sheaf.Γ (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).rightDerived r).obj F.underlyingSheaf := by
  set a := Y ↘ Spec (CommRingCat.of k₀)
  set ā := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (CommRingCat.of k₀)))
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l a.geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l a.geometricFiber) ℤ
  -- forget the Weil structure: `For (Ra_* F) ≅ Rā_* (For F)`
  let e₁ : (IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l a).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)) ≅
      (ā)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.carrier) :=
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
      Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app F.obj)
  -- forget the `ℚ̄_ℓ,Ȳ`-module structure
  let e₂ : (ProEtale.AdicSheaf.forget _).mapDerivedCategory.obj
      ((ā)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.carrier)) ≅
      ((ā)_*[WeilCoefficients.{u} l]).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.underlyingSheaf) :=
    ((ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso l ā).app _).symm ≪≫
      Functor.mapIso _
        (((ProEtale.AdicSheaf.forget _).mapDerivedCategorySingleFunctor 0).app F.carrier)
  -- the underlying sheaf of `𝓗ʳ(Ra_* F)` is `Rʳā_* F`
  let e₃ : (ProEtale.AdicSheaf.forget _).obj ((IsoAlgebra.forget _).obj
      ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l a).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)))) ≅
      (((ā)_*[WeilCoefficients.{u} l]).rightDerived r).obj F.underlyingSheaf :=
    (ProEtale.AdicSheaf.forget _).mapIso
        ((((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso (r : ℤ)).app _) ≪≫
          (_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e₁) ≪≫
      (((ProEtale.AdicSheaf.forget _).mapDerivedCategoryHomologyFunctorIso (r : ℤ)).app _) ≪≫
      (_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e₂ ≪≫
      ((ā)_*[WeilCoefficients.{u} l]).homologyRightDerivedFunctorObjSingleFunctorIso _ r
  -- `Γ(Spec k̄, -)` is exact and `Γ(Spec k̄, ā_* -) = Γ(Ȳ, -)`
  exact (Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso e₃ ≪≫
    (Functor.rightDerivedCompObjIso _ _ r _).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (ProEtale.globalSectionsLowerStarIso _ ā) r _

/-- **Vanishing of Weil cohomology from pro-étale cohomology.** If the pro-étale cohomology
`Rʳ Γ(Ȳ_proét, F)` of the underlying sheaf of a Weil sheaf `F` vanishes, so does
`Hʳ(Y ⊗ k̄, F)`. -/
theorem subsingleton_cohomology_of_isZero_rightDerived (F : WeilSheaf k₀ l Y) (r : ℕ)
    (h : IsZero (((Sheaf.Γ (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)).rightDerived r).obj F.underlyingSheaf)) :
    Subsingleton (F.cohomology r).carrier :=
  ModuleCat.subsingleton_of_isZero (M := (WeilCoefficients.toModuleCat l).obj
    (globalSectionsUnderlyingFunctor.obj ((WeilComplex.homologySheaf (r : ℤ)).obj
      ((WeilComplex.derivedLowerStar (Y ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F)))))
    ((WeilCoefficients.toModuleCat l).map_isZero
      (h.of_iso (cohomologyIsoRightDerivedGlobalSections F r)))

end WeilSheaf

end AlgebraicGeometry
