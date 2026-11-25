/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
public import WeilConjectures.SixFunctors.Supporting.CompleteTopResidueCellCone
import all WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldLisseInternalHom
import all WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Slice constant residue bases under normalized clopen restriction

Source: Stacks Project, proetale.tex, Tag 09C3; sites.tex, Tag 00XZ.
(blueprint: lem-sf-clopen-residue-free-restriction).
-/

@[expose] public section
set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private noncomputable instance (priority := 10000) residueBasesAbSheafify
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

private instance (priority := 10000) residueBasesAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

/-- A constant rank-r model on the slice becomes the actual rank-r free residue
module sheaf after ordinary restriction to the open subscheme.

Source: Stacks Project, proetale.tex, Tag 09C3, the disjoint-open trivialization;
sites.tex, Tag 00XZ, localization of sheafification. This is the coefficient and
module transport in step 2 of lem-sf-residue-lisse-clopen-bases.
(blueprint: lem-sf-clopen-residue-free-restriction).

Proof: precompose localized module sheaves with the concrete sliceFrom functor to
restrict to the pro-etale site of U, and transport scalars along d.finite 0. This
functor is additive and preserves finite limits sectionwise, hence finite
biproducts. Its canonical map from the local coefficient unit to the restricted
slice coefficient unit is invertible, since d.finite 0 is a ring isomorphism.
The constant model k^r is the finite biproduct of r copies of k. The additive
model-sheafification functor and the constant-unit comparison identify its sheaf
with the corresponding finite biproduct of slice coefficient units. Apply ordinary
restriction to the supplied isomorphism and this description. The resulting
biproduct is the finite coproduct of local coefficient units. Reindex along
ULift.up to obtain precisely topCellResidueFree r and invert the composite. The
empty index r=0 gives the zero module; empty opens are allowed throughout. -/
theorem sf_clopen_residue_free_restriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (U : S.Opens)
    (d : SfClopenCoefficientRestriction.{u, u} l E S U)
    (F : scalarReductionTarget.{u, u} l E S 0) (r : ℕ)
    (hF : Nonempty (F.over (ProEt.mk U.ι) ≅
      proEtaleConstantModuleSheafOverOfUniverses S
        (Padic.coefficientExtensionRing l E 1) (ProEt.mk U.ι)
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))
          (Fin r → ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))))) :
    Nonempty (topCellResidueFree.{u} l E U.toScheme r ≅
      (sfClopenModuleRestriction U _ _ (d.finite 0)).obj F)  := by
  classical
  let W := ProEt.mk U.ι
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing S (Padic.coefficientExtensionRing l E 1))
  let T := integralCoefficientSheaf.{u, u} l E U.toScheme 0
  have : (ProEt.sliceFrom S W).IsDenseSubsite (ProEt.topology U.toScheme)
      ((ProEt.topology S).over W) := ProEt.sliceDense S W
  let c : T ≅ ((ProEt.sliceFrom S W).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U.toScheme) ((ProEt.topology S).over W)).obj (R.over W) :=
    d.finite 0
  let G := SheafOfModules.pushforward.{u + 1} (F := ProEt.sliceFrom S W) c.hom
  have : G.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits G := by
    let V := SheafOfModules.forget.{u + 1} T ⋙ PresheafOfModules.toPresheaf T.obj
    have : PreservesFiniteLimits (G ⋙ V) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{u + 1} (R.over W) ⋙
          PresheafOfModules.toPresheaf (R.over W).obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (ProEt.sliceFrom S W).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves G V
  have : PreservesBiproductsOfShape (Fin r) G :=
    preservesBiproductsOfShape_of_preservesProductsOfShape G
  have hu : IsIso (SheafOfModules.unitToPushforwardObjUnit c.hom) := by
    let V := SheafOfModules.toSheaf T ⋙
      sheafToPresheaf (ProEt.topology U.toScheme) AddCommGrpCat.{u + 1}
    have : IsIso (V.map (SheafOfModules.unitToPushforwardObjUnit c.hom)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Z
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (c.hom.hom.app Z)
      exact (ConcreteCategory.isIso_iff_bijective (c.hom.hom.app Z)).mp inferInstance
    exact isIso_of_reflects_iso (SheafOfModules.unitToPushforwardObjUnit c.hom) V
  let := hu
  let eu : SheafOfModules.unit T ≅ G.obj (SheafOfModules.unit (R.over W)) :=
    asIso (SheafOfModules.unitToPushforwardObjUnit c.hom)
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} (R.over W)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} T) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let M := modelSheafFunctor S (Padic.coefficientExtensionRing l E 1) W
  let eprod : (⨁ fun _ : Fin r ↦ ModuleCat.of A A) ≅
      ModuleCat.of A (Fin r → A) :=
    ModuleCat.biproductIsoPi (fun _ : Fin r ↦ ModuleCat.of A A)
  let em : M.obj (ModuleCat.of A (Fin r → A)) ≅
      ⨁ fun _ : Fin r ↦ SheafOfModules.unit (R.over W) :=
    M.mapIso eprod.symm ≪≫ M.mapBiproduct (fun _ : Fin r ↦ ModuleCat.of A A) ≪≫
      biproduct.mapIso (fun _ ↦ (constant_unit_over S
        (Padic.coefficientExtensionRing l E 1) W).some.symm)
  obtain ⟨eF⟩ := hF
  let e : (sfClopenModuleRestriction U _ _ (d.finite 0)).obj F ≅
      ⨁ fun _ : Fin r ↦ SheafOfModules.unit T :=
    G.mapIso (eF ≪≫ em) ≪≫ G.mapBiproduct (fun _ : Fin r ↦
      SheafOfModules.unit (R.over W)) ≪≫ biproduct.mapIso (fun _ ↦ eu.symm)
  exact ⟨Sigma.reindex Equiv.ulift (fun _ : Fin r ↦ SheafOfModules.unit T) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin r ↦ SheafOfModules.unit T)).symm ≪≫ e.symm⟩

end WeilConjectures
