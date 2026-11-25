/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorIdentification
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.Algebra.Homology.BifunctorHomCone
import all WeilConjectures.Algebra.Homology.BifunctorHomComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

/-! # Support of the ordinary open tensor

Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-ordinary-open-tensor-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem ordinary_supported_of_complement_zero
    {l : ℕ} [Fact l.Prime] {V X : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i] [QuasiCompact i] (F : ProEtale.AdicSheaf l X)
    (hF : IsZero ((ProEtale.adicUpperStar l i.closedComplement).obj F)) :
    (ProEtale.adicOpenImmersionLowerShriek l i).essImage F := by
  let a := ProEtale.adicOpenImmersionLowerShriekAdjunction l i
  let W := i.closedComplement
  let Z : Bool → Scheme.{u} := fun b ↦ Bool.rec (motive := fun _ ↦ Scheme.{u})
    (Over.mk i.closedComplement).left V b
  let g : ∀ b, Z b ⟶ X := fun b ↦ Bool.rec (motive := fun b ↦ Z b ⟶ X) W i b
  have : ∀ b, QuasiCompact (g b) := by
    rintro (_ | _)
    · exact inferInstanceAs (QuasiCompact W)
    · exact inferInstanceAs (QuasiCompact i)
  have hc : IsIso (a.counit.app F) := by
    refine ProEtale.isIso_of_forall_isIso_adicUpperStar_map g (fun x ↦ ?_) _ ?_
    · by_cases hx : x ∈ Set.range i.base
      · exact ⟨true, hx⟩
      · refine ⟨false, ?_⟩
        change x ∈ Set.range i.closedComplement.base
        rwa [i.range_closedComplement]
    · rintro (_ | _)
      · change IsIso ((ProEtale.adicUpperStar l W).map (a.counit.app F))
        have hs := ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek i W
          (by rw [i.range_closedComplement, Set.inter_compl_self])
          ((ProEtale.adicUpperStar l i).obj F)
        exact isIso_of_source_target_iso_zero _ hs.isoZero hF.isoZero
      · change IsIso ((ProEtale.adicUpperStar l i).map (a.counit.app F))
        have he : IsIso (a.unit.app ((ProEtale.adicUpperStar l i).obj F) ≫
            (ProEtale.adicUpperStar l i).map (a.counit.app F)) := by
          rw [a.right_triangle_components]
          exact IsIso.id _
        exact IsIso.of_isIso_comp_left
          (a.unit.app ((ProEtale.adicUpperStar l i).obj F)) _
  exact a.mem_essImage_of_counit_isIso F

private theorem ordinary_sheaf_tensor_supported
    {l : ℕ} [Fact l.Prime] {V X : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i] [QuasiCompact i]
    (M : ProEtale.AdicSheaf l V) (N : ProEtale.AdicSheaf l X) :
    (ProEtale.adicOpenImmersionLowerShriek l i).essImage
      ((ProEtale.adicOpenImmersionLowerShriek l i).obj M ⊗ N) := by
  let E := ProEtale.adicOpenImmersionLowerShriek l i
  let R := ProEtale.adicUpperStar l i.closedComplement
  apply ordinary_supported_of_complement_zero i
  let e : R.obj (E.obj M ⊗ N) ≅ (Mod.tensorLeft (R.obj N)).obj (R.obj (E.obj M)) :=
    R.mapIso (PrecompositionAux.tensorComponent (E.obj M) N).symm ≪≫
      (ProEtale.adicUpperStarTensorLeftIso l i.closedComplement N).app (E.obj M)
  exact ((Mod.tensorLeft (R.obj N)).map_isZero
    (ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek i i.closedComplement
      (by rw [i.range_closedComplement, Set.inter_compl_self]) M)).of_iso e

private theorem ordinary_total_tensor_supported
    {l : ℕ} [Fact l.Prime] {V X : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i] [QuasiCompact i]
    (M : CochainComplex (ProEtale.AdicSheaf l V) ℤ)
    (N : CochainComplex (ProEtale.AdicSheaf l X) ℤ) (n : ℤ) :
    (ProEtale.adicOpenImmersionLowerShriek l i).essImage
      ((((ProEtale.adicOpenImmersionLowerShriek l i).mapHomologicalComplex (.up ℤ)).obj M
        ⊗ N).X n) := by
  let E := ProEtale.adicOpenImmersionLowerShriek l i
  let a := ProEtale.adicOpenImmersionLowerShriekAdjunction l i
  let : E.Full := a.fullyFaithfulLOfIsIsoUnit.full
  let : E.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : PreservesColimitsOfSize.{0, 0} E := a.leftAdjoint_preservesColimits
  exact ObjectProperty.prop_of_isColimit _ (GradedObject.isColimitCofanMapObj _ _ n)
    (fun k ↦ ordinary_sheaf_tensor_supported i (M.X k.as.1.1) (N.X k.as.1.2))

private theorem ordinary_Q_supported
    {l : ℕ} [Fact l.Prime] {V X : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i]
    (C : CochainComplex (ProEtale.AdicSheaf l X) ℤ)
    (hC : ∀ n, (ProEtale.adicOpenImmersionLowerShriek l i).essImage (C.X n)) :
    (ProEtale.adicOpenImmersionLowerShriek l i).mapDerivedCategory.essImage
      (DerivedCategory.Q.obj C) := by
  let E := ProEtale.adicOpenImmersionLowerShriek l i
  let R := ProEtale.adicUpperStar l i
  let a := ProEtale.adicOpenImmersionLowerShriekAdjunction l i
  let : E.Full := a.fullyFaithfulLOfIsIsoUnit.full
  let : E.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have (n : ℤ) : IsIso (a.counit.app (C.X n)) :=
    a.isIso_counit_app_iff_mem_essImage.mpr (hC n)
  let f : (E.mapHomologicalComplex (.up ℤ)).obj
      ((R.mapHomologicalComplex (.up ℤ)).obj C) ⟶ C :=
    { f n := a.counit.app (C.X n)
      comm' _ _ _ := (a.counit.naturality _).symm }
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact ⟨DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj C),
    ⟨E.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso (asIso f)⟩⟩

private theorem ordinary_derived_tensor_supported
    {l : ℕ} [Fact l.Prime] {V X : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i] [QuasiCompact i]
    (M : DerivedCategory (ProEtale.AdicSheaf l V))
    (N : DerivedCategory (ProEtale.AdicSheaf l X)) :
    (ProEtale.adicOpenImmersionLowerShriek l i).mapDerivedCategory.essImage
      ((ProEtale.adicOpenImmersionLowerShriek l i).mapDerivedCategory.obj M ⊗ N) := by
  let E := ProEtale.adicOpenImmersionLowerShriek l i
  have (Y : ProEtale.AdicSheaf l X) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj Y) := inferInstance
  obtain ⟨P, hP, ⟨eN⟩⟩ := DerivedCategory.exists_kFlat_iso N
  let M₀ := DerivedCategory.Q.objPreimage M
  let M₁ := (E.mapHomologicalComplex (.up ℤ)).obj M₀
  have := Functor.isIso_μNatTrans_Qh_app_app_of_kFlat
    ((HomotopyCategory.quotient _ _).obj M₁) P hP
  refine Functor.essImage.ofIso ?_
    (ordinary_Q_supported i (M₁ ⊗ P.as)
      (ordinary_total_tensor_supported i M₀ P.as))
  exact ((DerivedCategory.quotientCompQhIso _).app (M₁ ⊗ P.as)).symm ≪≫
    DerivedCategory.Qh.mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) M₁ P.as) ≪≫
    (asIso (((Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh).app
      ((HomotopyCategory.quotient _ _).obj M₁)).app P)).symm ≪≫
    tensorIso ((E.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
        E.mapDerivedCategoryFactors.app M₀ ≪≫
        ((DerivedCategory.quotientCompQhIso _).app M₁).symm).symm) eN

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

set_option linter.unusedSectionVars false in
/-- Tensor with an extended input remains supported on the geometric open.

Source: Stacks 0GL1, sites-cohomology.tex, lemma-j-shriek-and-tensor, and
Stacks 0E8I, sites-modules.tex, lemma-j-shriek-and-tensor.

Proof: First use the ordinary Hom representative model and uniqueness of tensor
adjoints to compare the fixed tensor with the canonical derived module tensor.
For an ordinary sheaf vanishing on the closed complement, test the open counit
on the open and the complement. On the open the triangle identity and invertible
unit make it an isomorphism; on the complement both objects vanish. These two
quasi-compact pullbacks jointly detect isomorphisms. Pullback commutes with the
relative module tensor, so tensoring an extended sheaf with any sheaf vanishes
on the complement and is therefore in the essential image of extension.

The essential image of the fully faithful left adjoint is closed under the
coproducts forming each term of the total tensor. Its termwise counit is thus
an isomorphism of complexes. Localization exhibits that total complex as an
extended derived object. Represent the ambient input by a K-flat complex and
use the canonical localization tensorator to compute the derived tensor.
Transport along the fixed tensor comparison. Finally the invertible ordinary
open unit gives full faithfulness of the exact derived extension, so its counit
is invertible on this essential image. The argument includes empty opens and
unbounded complexes and asserts no compatibility with forgetting Weil structures.
(blueprint: lem-sf-native-ordinary-open-tensor-support). -/
theorem native_ordinary_open_tensor_support
    (M : DerivedCategory (ProEtale.AdicSheaf l
      (U ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (N : DerivedCategory (ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory.counit.app
        ((nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor.obj
          ((ProEtale.adicOpenImmersionLowerShriek l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory.obj M, N))) := by
    let i := Scheme.Hom.geometricFiberMap j
      (comp_over j (Spec (CommRingCat.of k₀)))
    let E := ProEtale.adicOpenImmersionLowerShriek l i
    let R := ProEtale.adicUpperStar l i
    let a := ProEtale.adicOpenImmersionLowerShriekAdjunction l i
    let C := nativeDerivedClosedComparison k₀ l Z
    obtain ⟨e⟩ := nativeOrdinary_tensorRight_iso l _ C.homModels.ordinaryHom
      C.homModels.ordinaryRepresentatives C.ordinaryClosed N
    have hs := ordinary_derived_tensor_supported i M N
    have hs' : E.mapDerivedCategory.essImage
        (C.ordinaryClosed.tensor.obj (E.mapDerivedCategory.obj M, N)) :=
      Functor.essImage.ofIso (e.app (E.mapDerivedCategory.obj M)).symm hs
    let ff := a.mapExactDerivedCategory.fullyFaithfulLOfCompIsoId
      (Functor.mapDerivedCategoryCompIso E R ≪≫
        Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
    let : E.mapDerivedCategory.Full := ff.full
    let : E.mapDerivedCategory.Faithful := ff.faithful
    exact a.mapExactDerivedCategory.isIso_counit_app_iff_mem_essImage.mpr hs'

end AlgebraicGeometry.ProEtaleWeilSheaf
