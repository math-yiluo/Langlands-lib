/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperLocalizingPushforward
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Constructibility of the cohomology of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] upperStarFromPoint openImmersionLowerShriek lowerStar
  Functor.rightAdjoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- Every cohomology object of the supplied localizing right adjoint on a bounded
constructible input is constructible.

Source: blueprint `theorem-exceptional-inverse-image` (4), `det-existence-restriction.proof.md`,
Part (2). Proof: compare local finite-presentation charts with the field, algebraic-closure, and
integral adic models using the cited local triviality and resolution theorems.  The smooth
and closed local restriction calculations preserve constructibility; finite affine descent
and uniqueness of right adjoints identify the result with the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/
private theorem homology_constructible_of_key (hkey : ExceptionalKey Λ g)
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : IsNoetherian Y.left := ⟨⟩
  obtain ⟨_, hX⟩ := certified_comparison Λ ℓ hΛ Z.left
  have hY := (certified_comparison Λ ℓ hΛ Y.left).2
  classical
  let LX := localizingClosureProEtale Λ Z.left
  let LY := localizingClosureProEtale Λ Y.left
  have eX := hull_eq Λ Z.left hX
  have eY := hull_eq Λ Y.left hY
  let jX := ObjectProperty.ιOfLE (le_of_eq eX)
  let jY := ObjectProperty.ιOfLE (le_of_eq eY)
  let iX := ObjectProperty.ιOfLE (le_of_eq eX.symm)
  obtain ⟨h, hcomp, H, ⟨adjH⟩, hH⟩ := hkey
  let eShriek : openImmersionLowerShriek Λ (𝟙 Z.left) ≅ 𝟭 _ :=
    ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 Z.left)).ofNatIsoRight
      (upperStarId Λ Z.left)).leftAdjointUniq Adjunction.id
  let eId : (openImmersionLowerShriek Λ (𝟙 Z.left)).mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryNatIso eShriek ≪≫ Functor.mapDerivedCategoryIdIso _
  let ec : rightDerivedLowerShriekOfCompactification Λ
      (Compactification.ofIsProper g.left) ≅ R((g.left)_*⟦Λ⟧) :=
    Functor.isoWhiskerRight eId _ ≪≫ Functor.leftUnitor _
  obtain ⟨bc⟩ := hcomp (Compactification.ofIsProper g.left)
  let beta : localizingLowerShriek Λ (compactificationOverField g) h ⋙ LY.ι ≅
      LX.ι ⋙ R((g.left)_*⟦Λ⟧) :=
    bc ≪≫ Functor.isoWhiskerLeft LX.ι ec
  let J := jY ⋙ G ⋙ iX
  let FStar := LY.lift (LX.ι ⋙ R((g.left)_*⟦Λ⟧))
    (fun A ↦ (le_of_eq eY.symm) _
      (ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ A.obj (jX.obj A).property))
  let alpha : localizingLowerShriek Λ (compactificationOverField g) h ≅ FStar :=
    NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk LY (beta.app A)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact beta.hom.naturality f)
  let adjJ : FStar ⊣ J := adj.restrictFullyFaithful
    (iC := jX) (iD := jY) (L := FStar) (R := J)
    (ObjectProperty.fullyFaithfulιOfLE (le_of_eq eX))
    (ObjectProperty.fullyFaithfulιOfLE (le_of_eq eY))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intros
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intros
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
  let eg : H ≅ J := adjH.rightAdjointUniq (adjJ.ofNatIsoLeft alpha.symm)
  let N : LY.FullSubcategory := ⟨K.obj, (le_of_eq eY.symm) _
    (boundedConstructible_le_localizingClosure Λ Y.left K.obj K.property)⟩
  have hN : (constantModelBoundedConstructible Λ Y.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) N.obj := (congrFun hY K.obj).mpr K.property
  have hHN := hH N hN
  have hJN : (constantModelBoundedConstructible Λ Z.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (J.obj N).obj := by
    have := (constantModelConstructibleFiniteTor_wellDefined Λ Z.left).2.1
    exact (constantModelBoundedConstructible Λ Z.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso (LX.ι.mapIso (eg.app N)) hHN
  have hbounded : boundedConstructible (condensedRingObj Λ Z.left) (J.obj N).obj :=
    (congrFun hX _).mp hJN
  exact hbounded.2

/-- `ellAdic_localizing_rightAdjoint_obj_homology_constructible` for the coefficients `E` and
`Q̄_ℓ`: the exceptional inverse image comes from Brown representability and the rational
restriction theorem alone (blueprint: theorem-f-shriek-ell-adic-coefficients).
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/
theorem ellAdic_localizing_rightAdjoint_obj_homology_constructible_rational
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    (hr : ((∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))))
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) :=
  homology_constructible_of_key Λ ℓ g hΛ (exceptionalKey_rational (hcd := hcd) Λ ℓ g hr) G adj K

end AlgebraicGeometry.ProEtale.CondensedRing
