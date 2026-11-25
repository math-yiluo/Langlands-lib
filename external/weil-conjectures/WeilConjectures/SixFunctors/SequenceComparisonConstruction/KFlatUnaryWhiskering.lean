/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.CategoryTheory.SixFunctors.UnaryWhiskeringOfProduct

/-! # Unary restriction to K-flat representatives

Source: Stacks 06YS, 07A4 and 0G7E.
(blueprint: lem-sf-kflat-unary-whiskering).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe a b c d e f
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace SequenceComparisonConstruction

/-- Restriction along K-flat representatives is fully faithful on functor categories.
Source: Stacks 06YS, 07A4 and 0G7E
(blueprint: lem-sf-kflat-unary-whiskering).
Proof: every homotopy object has a K-flat resolution, giving the hypotheses of
resolvingRepresentativesFullyFaithfulWhiskering on the K-flat full subcategory.
Transport its product restriction comparison by quotientCompQhIso. Apply the
projection/diagonal construction unaryWhiskeringOfProduct to obtain unary full
faithfulness for the actual derived localization on cochain complexes. -/
theorem kflatWhiskering
    {D : Type e} [Category.{f} D]
    {C : Type a} [Category.{b} C] [EssentiallySmall.{c} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{c} RingCat.{c})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{c}]
    [HasSheafify J AddCommGrpCat.{c}]
    (R : Sheaf J CommRingCat.{c})
    [HasDerivedCategory.{d} (SheafOfModules.{c}
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj R))] :
    let A := SheafOfModules.{c}
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj R)
    let P : ObjectProperty (CochainComplex A ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (R := R)
    Nonempty (((whiskeringLeft P.FullSubcategory (DerivedCategory A) D).obj
      (P.ι ⋙ DerivedCategory.Q)).FullyFaithful) := by
  intro A P
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ P X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (s : Y.obj ⟶ X),
        HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, q, hK, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    exact ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, hK⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map q,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq⟩
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) D
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh P H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ D).mapIso
    (NatIso.prod (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A))))
  exact ⟨CategoryTheory.Functor.unaryWhiskeringOfProduct D (P.ι ⋙ DerivedCategory.Q) ff'⟩

end SequenceComparisonConstruction
