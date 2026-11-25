/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
import WeilConjectures.AlgebraicGeometry.Native.NativeBasicComparisons
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenProperInterchange
import WeilConjectures.WeilSheaf.Native.NativeCompatibleTowerCalculation
import WeilConjectures.AlgebraicGeometry.Native.NativeCompactificationModelComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeProperNaturalBaseChange
import WeilConjectures.AlgebraicGeometry.Native.NativeOpenNaturalBaseChange
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.WeilSheaf.Native.NativeImmersionHeartLocalization
import WeilConjectures.WeilSheaf.Localization
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Functoriality of the direct image with compact support of Weil complexes

The direct image with compact support `Rf₀! = Rḡ_* ∘ ī_!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) is defined through the compactification
`X ⟶[i] Z ⟶[g] Y` of `f` chosen by Nagata's theorem. This file records the compatibilities of
`Rf₀!` collected in the blueprint theorem `prop-functor-package` of the six-functor chapter that
the Deligne–Laumon reduction (`chap-The-Deligne-Laumon-theorem-in-general`) uses:

- *independence of the compactification* (clause 2), in the case of the compactification
  `U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`: `Rj₀!` is the extension by zero;
- *composition* (clause 3): `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`, and the distinguished triangle
  `R(j ≫ f)₀! j^*K ⟶ Rf₀!K ⟶ R(i ≫ f)₀! i^*K ⟶` obtained by applying `Rf₀!` to the
  localization triangle of an open immersion `j` and its closed complement `i`;
- *base change* (clause 4): `h^* Rf₀! ≅ Rf'₀! g^*` for a cartesian square;

as well as the open–closed triangle `j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶` of a Weil complex
(`proposition-extension-zero-restriction-closed-subscheme--8`), as well as the identification of
`Rf₀!` with `Rf₀*` for proper `f`. The extension by zero, the open–closed triangle and the
composition are deduced from the native comparisons of `Sheaf.WeilSheaf`; the base change is deduced
from the native proper and open base changes (`Sheaf.WeilSheaf.NativeProperNaturalBaseChange`,
`Sheaf.WeilSheaf.NativeOpenNaturalBaseChange`) and the compactification model comparison.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar`: `Rf₀! ≅ Rf₀*` for
  `f` proper.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`,
  `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`,
  `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed` and
  `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`: clauses 2, 3 and 4 of
  `prop-functor-package`.
- `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`: the open–closed triangle
  (`proposition-extension-zero-restriction-closed-subscheme--8`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

namespace WeilComplex

section Proper

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **For a proper morphism, the direct image with compact support is the direct image**: for the
chosen compactification `X ⟶[i] Z ⟶[g] Y` of the proper morphism `f`, the open immersion `i` is
proper, hence a closed immersion, so that `Rf₀!K = Rg_*(i_!K) ≅ Rg_*(i_*K) ≅ Rf₀*K`
(blueprint: `prop-functor-package`, clause 3, "for proper `f`, `Rf_! ≃ Rf_*`"). -/
noncomputable def derivedLowerShriekObjIsoDerivedLowerStar (K : WeilComplex k₀ l X) :
    (derivedLowerShriek k₀ l f).obj K ≅ (derivedLowerStar f).obj K := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

/-- **For a proper morphism, the direct image with compact support is the direct image**, as an
isomorphism of functors on Weil complexes; its components are
`AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar` (blueprint:
`prop-functor-package`, clause 3, "for proper `f`, `Rf_! ≃ Rf_*`"). -/
noncomputable def derivedLowerShriekIsoDerivedLowerStar :
    derivedLowerShriek k₀ l f ≅ derivedLowerStar f := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let Φ : (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor :=
    Functor.isoWhiskerRight
        (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.symm
        _ ≪≫
      (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
          (comp_over c.i _))
        (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm ≪≫
      Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
        (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
        (ProEtaleWeilSheaf.lowerStar k₀ l c.g)) ≪≫
      Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g) ≪≫
      Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)
  exact ((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _ ≪≫
      Functor.isoWhiskerLeft _ Φ ≪≫ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm)

end Proper

universe v w uC uD uE vD vE wD wE

-- Use the same coefficient instances as the native functors in the public imports.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing
  ULift.commRing AlgebraicClosure.instCommRing

private theorem exists_ambient_triangle_of_heart_sequence
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
    (P : C ⥤ D) (J : D ⥤ C) (Q : C ⥤ E) (I : E ⥤ C)
    [P.Additive] [J.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (α : P ⋙ J ⟶ 𝟭 C) (β : 𝟭 C ⟶ Q ⋙ I)
    (h : ∀ M, ∃ w : α.app M ≫ β.app M = 0,
      (ShortComplex.mk (α.app M) (β.app M) w).ShortExact)
    (K : _root_.DerivedCategory C) :
    ∃ T ∈ distTriang (_root_.DerivedCategory C),
      Nonempty (T.obj₁ ≅ J.mapDerivedCategory.obj (P.mapDerivedCategory.obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ I.mapDerivedCategory.obj (Q.mapDerivedCategory.obj K)) := by
  classical
  let L := _root_.DerivedCategory.Q.objPreimage K
  let e := _root_.DerivedCategory.Q.objObjPreimageIso K
  let a : ((P ⋙ J).mapHomologicalComplex (.up ℤ)).obj L ⟶ L :=
    { f := fun n ↦ α.app (L.X n)
      comm' := fun m n _ ↦ (α.naturality (L.d m n)).symm }
  let b : L ⟶ ((Q ⋙ I).mapHomologicalComplex (.up ℤ)).obj L :=
    { f := fun n ↦ β.app (L.X n)
      comm' := fun m n _ ↦ (β.naturality (L.d m n)).symm }
  let S := ShortComplex.mk a b (by ext n : 1; exact (h (L.X n)).choose)
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact S
      (fun n ↦ (h (L.X n)).choose_spec)
  exact ⟨_root_.DerivedCategory.triangleOfSES hS,
    _root_.DerivedCategory.triangleOfSES_distinguished hS,
    ⟨((P ⋙ J).mapDerivedCategoryFactors.app L).symm ≪≫
      (P ⋙ J).mapDerivedCategory.mapIso e ≪≫
      (Functor.mapDerivedCategoryCompIso P J).symm.app K⟩,
    ⟨e⟩, ⟨((Q ⋙ I).mapDerivedCategoryFactors.app L).symm ≪≫
      (Q ⋙ I).mapDerivedCategory.mapIso e ≪≫
      (Functor.mapDerivedCategoryCompIso Q I).symm.app K⟩⟩

private theorem exists_subcategory_triangle_of_ambient
    {C : Type uC} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsTriangulated] (A B D : P.FullSubcategory)
    (T₀ : Triangle C) (hT₀ : T₀ ∈ distTriang C)
    (e₁ : T₀.obj₁ ≅ A.obj) (e₂ : T₀.obj₂ ≅ B.obj) (e₃ : T₀.obj₃ ≅ D.obj) :
    ∃ T ∈ distTriang P.FullSubcategory,
      Nonempty (T.obj₁ ≅ A) ∧ Nonempty (T.obj₂ ≅ B) ∧ Nonempty (T.obj₃ ≅ D) := by
  let ι := P.ι
  let T : Triangle P.FullSubcategory := Triangle.mk
    (ObjectProperty.homMk (e₁.inv ≫ T₀.mor₁ ≫ e₂.hom) : A ⟶ B)
    (ObjectProperty.homMk (e₂.inv ≫ T₀.mor₂ ≫ e₃.hom) : B ⟶ D)
    (ObjectProperty.homMk (e₃.inv ≫ T₀.mor₃ ≫
      (shiftFunctor C (1 : ℤ)).map e₁.hom ≫ (ι.commShiftIso (1 : ℤ)).inv.app A))
  refine ⟨T, ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  change ι.mapTriangle.obj T ∈ distTriang C
  refine isomorphic_distinguished T₀ hT₀ _
    (Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm ?_ ?_ ?_)
  · change (e₁.inv ≫ T₀.mor₁ ≫ e₂.hom) ≫ e₂.inv = e₁.inv ≫ T₀.mor₁
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change (e₂.inv ≫ T₀.mor₂ ≫ e₃.hom) ≫ e₃.inv = e₂.inv ≫ T₀.mor₂
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change ((e₃.inv ≫ T₀.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.hom ≫
        (ι.commShiftIso (1 : ℤ)).inv.app A) ≫
        (ι.commShiftIso (1 : ℤ)).hom.app A) ≫
        (shiftFunctor C (1 : ℤ)).map e₁.inv = e₃.inv ≫ T₀.mor₃
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id]
    rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id]

section Package

variable {X Y Z U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))]

private theorem nonempty_openShriekComparison (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty ((objectProperty k₀ l U).ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ≅
      derivedLowerShriek k₀ l j ⋙ (objectProperty k₀ l X).ι) := by
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  let c := HasCompactification.compactification j
    (hf := hasCompactification_of_over (k₀ := k₀) j)
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨α⟩ := nonempty_extensionByZero_rightDerivedLowerStar_iso
    k₀ l c.i (𝟙 U) c.g j (by simpa using c.comm.symm)
  obtain ⟨e⟩ := (nativeWeilBasicComparisons k₀ l).2.1 U
  exact ⟨(Functor.isoWhiskerLeft (objectProperty k₀ l U).ι
    (Functor.isoWhiskerRight e
      (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ≪≫
      Functor.leftUnitor _)).symm ≪≫ α⟩

private theorem exists_native_localization_triangle (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l i)]
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    ∃ T ∈ distTriang (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)),
      Nonempty (T.obj₁ ≅ (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ (ProEtaleWeilSheaf.lowerStar k₀ l i).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj K)) := by
  -- Keep the unused coefficient comparisons packaged; only the final property is needed.
  obtain ⟨aj, ai, hlocal⟩ :=
    ProEtaleWeilSheaf.nativeImmersionHeartLocalization k₀ l X U Z j i hij.symm
  exact exists_ambient_triangle_of_heart_sequence
    (ProEtaleWeilSheaf.upperStar k₀ l j) (ProEtaleWeilSheaf.extensionByZero k₀ l j)
    (ProEtaleWeilSheaf.upperStar k₀ l i) (ProEtaleWeilSheaf.lowerStar k₀ l i)
    aj.counit ai.unit hlocal.2.2.2.2 K

/-- **The direct image with compact support along an open immersion is the extension by zero**
(blueprint: `prop-functor-package`, clause 2, compactification comparisons for
`Rf_! = Rf̄_* j_!` are independent of the refinement, applied to the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`; and `def-weil-extension-by-zero`). For a
quasi-compact open immersion `j` and a Weil sheaf `G` on `U`, `Rj₀!G ≅ j₀!G` in degree zero. -/
theorem nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l U) :
    Nonempty ((derivedLowerShriek k₀ l j).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.extensionByZero j).obj G)) := by
  obtain ⟨e⟩ := nonempty_openShriekComparison (k₀ := k₀) (l := l) j
  refine ⟨ObjectProperty.isoMk _ ?_⟩
  exact (e.app (WeilSheaf.toComplex.obj G)).symm ≪≫
    ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategorySingleFunctor 0).app G.obj

/-- **The open–closed triangle** (blueprint:
`proposition-extension-zero-restriction-closed-subscheme--8`): for a quasi-compact open immersion
`j : U ⟶ X` with closed complement `i : Z ⟶ X` and a Weil complex `K` on `X`, the open counit and
the closed unit extend to a distinguished triangle of Weil complexes
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ j₀!j₀^*K[1]`.

This is a weakening of the blueprint node: the vertices of the triangle are only identified up
to some isomorphism, and the first two arrows are not asserted to be the canonical counit and
unit. -/
theorem exists_distTriang_openClosed (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l X),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerStar i).obj ((upperStar i).obj K)) := by
  classical
  have : PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l i) :=
    ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl i j hij.symm
  let P := ProEtaleWeilSheaf.upperStar k₀ l j
  let J := ProEtaleWeilSheaf.extensionByZero k₀ l j
  let Q := ProEtaleWeilSheaf.upperStar k₀ l i
  let I := ProEtaleWeilSheaf.lowerStar k₀ l i
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_native_localization_triangle (k₀ := k₀) (l := l) j i hij K.obj
  have pK : P.mapDerivedCategory.obj K.obj = ((upperStar j).obj K).obj := rfl
  have qK : Q.mapDerivedCategory.obj K.obj = ((upperStar i).obj K).obj := rfl
  obtain ⟨ej⟩ := nonempty_openShriekComparison (k₀ := k₀) (l := l) j
  have c₁ : J.mapDerivedCategory.obj (P.mapDerivedCategory.obj K.obj) ≅
      ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)).obj :=
    J.mapDerivedCategory.mapIso (eqToIso pK) ≪≫ ej.app ((upperStar j).obj K)
  have rK : I.rightDerivedFunctor.obj ((upperStar i).obj K).obj =
      ((derivedLowerStar i).obj ((upperStar i).obj K)).obj := rfl
  have c₃ : I.mapDerivedCategory.obj (Q.mapDerivedCategory.obj K.obj) ≅
      ((derivedLowerStar i).obj ((upperStar i).obj K)).obj :=
    I.mapDerivedCategory.mapIso (eqToIso qK) ≪≫
      (I.rightDerivedFunctorIsoMapDerivedCategory.app ((upperStar i).obj K).obj).symm ≪≫
      eqToIso rK
  exact exists_subcategory_triangle_of_ambient (objectProperty k₀ l X)
    ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)) K
    ((derivedLowerStar i).obj ((upperStar i).obj K)) T hT (e₁ ≪≫ c₁) e₂ (e₃ ≪≫ c₃)

/-- **Composition of direct images with compact support** (blueprint: `prop-functor-package`,
clause 3: `R(gf)_! ≃ Rg_!Rf_!`; this is `proposition-composition-base-change-rf-shriek--1` of
`chap-The-Deligne-Laumon-theorem-in-general`). For composable separated morphisms of finite type
`X ⟶[f] Y ⟶[g] Z` of `k₀`-schemes, `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`. -/
theorem nonempty_derivedLowerShriek_comp_iso (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l (f ≫ g) ≅
      derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g) := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  let d := HasCompactification.compactification g
    (hf := hasCompactification_of_over (k₀ := k₀) g)
  let c := HasCompactification.compactification (f ≫ g)
    (hf := hasCompactification_of_over (k₀ := k₀) (f ≫ g))
  obtain ⟨e, _, _⟩ := (exists_compactifiable_compatible_tower f g d c).1
  let T := Compactification.Triangle.ofRestrict d e
  let := Compactification.over (k₀ := k₀) T.cf
  let := Compactification.over (k₀ := k₀) T.cg
  let := Compactification.over (k₀ := k₀) T.cfg
  have : T.p.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨by change T.p ≫ T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀) =
          T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)
        rw [← Category.assoc, T.p_g]⟩
  have hq : T.q ≫ T.cfg.g = T.cf.g ≫ g := by
    rw [← T.p_g, ← Category.assoc, ← T.isPullback.w,
      Category.assoc, ← T.cg.comm]
  have : T.q.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨by change T.q ≫ T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀) =
          T.cf.g ≫ Y ↘ Spec (CommRingCat.of k₀)
        rw [← Category.assoc, hq, Category.assoc, comp_over g _]⟩
  have : LocallyOfFiniteType (T.cf.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (T.cf.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (T.cf.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (T.cf.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : LocallyOfFiniteType (T.cg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (T.cg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (T.cg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : LocallyOfFiniteType (T.cfg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (T.cfg.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (T.cfg.g ≫ Z ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cfg.i := T.cfg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.q := MorphismProperty.of_isPullback T.isPullback inferInstance
  obtain ⟨_, _, _, ⟨α⟩⟩ := nativeWeilCompatibleTowerCalculation k₀ l
    T.cf.i T.q T.cg.i T.p T.cf.g T.cg.g T.isPullback.flip
  obtain ⟨ef⟩ := (nativeWeilCompactificationModelComparison k₀ l f).2.2 T.cf
  obtain ⟨eg⟩ := (nativeWeilCompactificationModelComparison k₀ l g).2.2 T.cg
  obtain ⟨efg⟩ := (nativeWeilCompactificationModelComparison k₀ l (f ≫ g)).2.2 T.cfg
  let IX := (objectProperty k₀ l X).ι
  let IY := (objectProperty k₀ l Y).ι
  let IZ := (objectProperty k₀ l Z).ι
  let F := ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f T.cf
  let G := ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l g T.cg
  let J := (ProEtaleWeilSheaf.extensionByZero k₀ l T.cf.i).mapDerivedCategory
  let R := (ProEtaleWeilSheaf.lowerStar k₀ l T.cf.g).rightDerivedFunctor
  have α₀ : IX ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l (f ≫ g) T.cfg ≅
      IX ⋙ J ⋙ R ⋙ G := by
    simpa only [IX, J, R, G, T.i_q, T.p_g,
      ProEtaleWeilSheaf.rightDerivedLowerShriek] using α
  let α' := α₀ ≪≫ Functor.isoWhiskerLeft IX (Functor.associator J R G).symm ≪≫
    (Functor.associator IX F G).symm
  let F' := derivedLowerShriek k₀ l f
  let G' := derivedLowerShriek k₀ l g
  exact ⟨((objectProperty k₀ l Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (efg.symm ≪≫ α' ≪≫ Functor.isoWhiskerRight ef G ≪≫
      Functor.associator F' IY G ≪≫ Functor.isoWhiskerLeft F' eg ≪≫
      (Functor.associator F' G' IZ).symm)⟩

/-- **Direct image with compact support of the localization triangle** (blueprint:
`prop-functor-package`, clause 3: for a closed immersion `i` with open complement `j`, applying
`Rf_!` to the localization triangle gives `R(fj)_!j^*K ⟶ Rf_!K ⟶ R(fi)_!i^*K ⟶`). -/
theorem exists_distTriang_derivedLowerShriek_openClosed (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l Y),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l (j ≫ f)).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ (derivedLowerShriek k₀ l f).obj K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerShriek k₀ l (i ≫ f)).obj ((upperStar i).obj K)) := by
  have hX : f ≫ Y ↘ Spec (CommRingCat.of k₀) = X ↘ Spec (CommRingCat.of k₀) :=
    comp_over f _
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by rw [← hX]; infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by rw [← hX]; infer_instance
  have : QuasiSeparated (X ↘ Spec (CommRingCat.of k₀)) := by rw [← hX]; infer_instance
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_openClosed (k₀ := k₀) j i hij K
  obtain ⟨cj⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j f
  obtain ⟨ci⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i f
  let F := derivedLowerShriek k₀ l f
  exact ⟨F.mapTriangle.obj T, F.map_distinguished _ hT, ⟨F.mapIso e₁ ≪≫ (cj.app _).symm⟩,
    ⟨F.mapIso e₂⟩, ⟨F.mapIso (e₃ ≪≫ (derivedLowerShriekObjIsoDerivedLowerStar i _).symm) ≪≫
      (ci.app _).symm⟩⟩

/-- **Base change for the direct image with compact support** (blueprint: `prop-functor-package`,
clause 4, `g^*Rf_! ≃ Rf'_!g'^*` for arbitrary base change): for a cartesian
square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h^* Rf₀! ≅ Rf'₀! g^*`. -/
theorem nonempty_upperStar_derivedLowerShriek_iso {X' Y' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) :
    Nonempty
      (derivedLowerShriek k₀ l f ⋙ upperStar h ≅
        upperStar g ⋙ derivedLowerShriek k₀ l f') := by
  let c := HasCompactification.compactification f
    (hf := hasCompactification_of_over (k₀ := k₀) f)
  let c' := c.ofIsPullback hH
  let : (pullback c.g h).Over (Spec (CommRingCat.of k₀)) :=
    ⟨pullback.snd c.g h ≫ Y' ↘ Spec (CommRingCat.of k₀)⟩
  have : (pullback.snd c.g h).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (pullback.fst c.g h).IsOver (Spec (CommRingCat.of k₀)) := by
    constructor
    change pullback.fst c.g h ≫ c.g ≫ (Y ↘ Spec (CommRingCat.of k₀)) =
      pullback.snd c.g h ≫ (Y' ↘ Spec (CommRingCat.of k₀))
    rw [← Category.assoc, pullback.condition, Category.assoc, comp_over h]
  have hc : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hc' : QuasiCompact c'.i := c'.quasiCompact_openImmersion inferInstance
  let sqg : ChosenCartesianSquare (pullback.fst c.g h) c'.g c.g h :=
    { toCommSq := (Compactification.isPullback_g_ofIsPullback hH c).flip.toCommSq
      isoPullback := (Compactification.isPullback_g_ofIsPullback hH c).flip.isoPullback
      hom_fst := (Compactification.isPullback_g_ofIsPullback hH c).flip.isoPullback_hom_fst
      hom_snd := (Compactification.isPullback_g_ofIsPullback hH c).flip.isoPullback_hom_snd }
  let sqi : ChosenCartesianSquare g c'.i c.i (pullback.fst c.g h) :=
    { toCommSq := (Compactification.isPullback_i_ofIsPullback hH c).toCommSq
      isoPullback := (Compactification.isPullback_i_ofIsPullback hH c).isoPullback
      hom_fst := (Compactification.isPullback_i_ofIsPullback hH c).isoPullback_hom_fst
      hom_snd := (Compactification.isPullback_i_ofIsPullback hH c).isoPullback_hom_snd }
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f' (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f' (Spec (CommRingCat.of k₀))]
    infer_instance
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : LocallyOfFiniteType (c'.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c'.g ≫ Y' ↘ Spec (CommRingCat.of k₀)))
  let IX := (objectProperty k₀ l X).ι
  let IX' := (objectProperty k₀ l X').ι
  let IY := (objectProperty k₀ l Y).ι
  let IY' := (objectProperty k₀ l Y').ι
  let IZ := (objectProperty k₀ l c.Z).ι
  let J := (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory
  let J' := (ProEtaleWeilSheaf.extensionByZero k₀ l c'.i).mapDerivedCategory
  let U := (ProEtaleWeilSheaf.upperStar k₀ l h).mapDerivedCategory
  let V := (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory
  let W := (ProEtaleWeilSheaf.upperStar k₀ l (pullback.fst c.g h)).mapDerivedCategory
  let R := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor
  let R' := (ProEtaleWeilSheaf.lowerStar k₀ l c'.g).rightDerivedFunctor
  have hJ : ∀ K, WeilComplex.objectProperty k₀ l X K →
      WeilComplex.objectProperty k₀ l c.Z (J.obj K) := by
    intro K hK
    exact ((nativeWeilBasicComparisons k₀ l).2.2.1 X c.Z c.i).2.2 K hK
  have hJ' : ∀ K, WeilComplex.objectProperty k₀ l X' K →
      WeilComplex.objectProperty k₀ l c'.Z (J'.obj K) := by
    intro K hK
    exact ((nativeWeilBasicComparisons k₀ l).2.2.1 X' c'.Z c'.i).2.2 K hK
  let JL := (objectProperty k₀ l X).liftFullSubcategory
    (objectProperty k₀ l c.Z) J hJ
  let UL := WeilComplex.upperStar (k₀ := k₀) (l := l) h
  let VL := WeilComplex.upperStar (k₀ := k₀) (l := l) g
  let eJ := ObjectProperty.liftFullSubcategoryCompιIso
    (objectProperty k₀ l X) (objectProperty k₀ l c.Z) J hJ
  let eU : UL ⋙ IY' ≅ IY ⋙ U := by
    dsimp [UL, IY', IY, U]
    exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  let eV : VL ⋙ IX' ≅ IX ⋙ V := by
    dsimp [VL, IX', IX, V]
    exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  obtain ⟨ep⟩ := nativeWeil_proper_natural_baseChange k₀ l
    (pullback.fst c.g h) c'.g c.g h sqg
  obtain ⟨eo⟩ := nativeWeilOpenNaturalBaseChange k₀ l
    g c'.i c.i (pullback.fst c.g h) sqi
  obtain ⟨ec⟩ := (nativeWeilCompactificationModelComparison k₀ l f).2.2 c
  obtain ⟨ec'⟩ := (nativeWeilCompactificationModelComparison k₀ l f').2.2 c'
  have eamb : IX ⋙ J ⋙ R ⋙ U ≅ IX ⋙ V ⋙ J' ⋙ R' := by
    exact Functor.isoWhiskerRight eJ.symm (R ⋙ U) ≪≫
      Functor.isoWhiskerLeft JL ep ≪≫
      Functor.isoWhiskerRight eJ (W ⋙ R') ≪≫
      Functor.isoWhiskerLeft IX (Functor.isoWhiskerRight eo R')
  have eleft : (derivedLowerShriek k₀ l f ⋙ UL) ⋙ IY' ≅
      IX ⋙ J ⋙ R ⋙ U := by
    exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f) eU ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.symm U ≪≫
      Functor.associator _ _ _
  have eright : (VL ⋙ derivedLowerShriek k₀ l f') ⋙ IY' ≅
      IX ⋙ V ⋙ J' ⋙ R' := by
    exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft VL ec'.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eV (J' ⋙ R') ≪≫
      Functor.associator _ _ _
  exact ⟨((objectProperty k₀ l Y').fullyFaithfulι.whiskeringRight _).preimageIso
    (eleft ≪≫ eamb ≪≫ eright.symm)⟩

end Package

end WeilComplex

end AlgebraicGeometry
