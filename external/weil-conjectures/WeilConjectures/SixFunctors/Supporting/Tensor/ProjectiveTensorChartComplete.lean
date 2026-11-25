/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SixFunctors.Supporting.BoundedProjectiveTensorComplete
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels

/-! # Completeness of ordinary tensor on a projective chart

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50; Stacks, Tags 07A4 and 0941
(blueprint: lem-fix-projective-tensor-chart-complete).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
open SheafOfModules.CanonicalTensorPullbackOfUniverses

attribute [local irreducible] IntegralOnSlice.duality
  IntegralOnSlice.completion IntegralOnSlice.completionUnit

@[irreducible] private def chartHomotopyIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  have : IsIso (e.hom.mapHomotopyCategory (.up ℤ)) :=
    ⟨e.inv.mapHomotopyCategory (.up ℤ),
      by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
        NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  exact isoWhiskerRight (asIso (e.hom.mapHomotopyCategory (.up ℤ))) DerivedCategory.Qh

@[irreducible] private def chartPullIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W T : Scheme.{u}} (f : T ⟶ W) :
    ordinaryIntegralDerivedPull l E f ≅ IntegralOnSlice.ordinaryDerivedPull l E f := by
  let := IntegralOnSlice.ordinaryPull_additive.{u, u} l E f
  let := IntegralOnSlice.ordinaryPull_hasLeftDerived.{u, u} l E f
  let i := ordinaryAmbientPullIso l E f ≪≫
    (IntegralOnSlice.ordinaryAmbientPullIso l E f).symm
  let τ := chartHomotopyIso _ _ i
  let ε : DerivedCategory.Qh ⋙ IntegralOnSlice.ordinaryDerivedPull l E f ⟶
      (IntegralOnSlice.ordinaryPull l E f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    ((IntegralOnSlice.ordinaryPull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (IntegralOnSlice.Mod l E W none) (.up ℤ))
  have : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E f)
      (HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ)) := by
    unfold ordinaryIntegralDerivedPull ordinaryIntegralPullCounit
    infer_instance
  have hs : (IntegralOnSlice.ordinaryDerivedPull l E f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (IntegralOnSlice.Mod l E W none) (.up ℤ)) := by
    dsimp only [IntegralOnSlice.ordinaryDerivedPull, ε]
    infer_instance
  have : (ordinaryIntegralDerivedPull l E f).IsRightKanExtension
      (ordinaryIntegralPullCounit l E f) :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ))
  have : (IntegralOnSlice.ordinaryDerivedPull l E f).IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (IntegralOnSlice.Mod l E W none) (.up ℤ))
  exact Functor.rightKanExtensionUniqueOfIso _ (ordinaryIntegralPullCounit l E f) τ _ ε

@[irreducible] private def chartTensorRepresentative
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    ((IntegralOnSlice.Good l E W none).ι.prod (IntegralOnSlice.Good l E W none).ι) ⋙
      coefficientTotalTensor.{u, u + 1, u} (IntegralOnSlice.topology W none)
        (IntegralOnSlice.ring l E W none) ⋙ DerivedCategory.Q ≅
      (((IntegralOnSlice.Good l E W none).ι ⋙ DerivedCategory.Q).prod
        ((IntegralOnSlice.Good l E W none).ι ⋙ DerivedCategory.Q)) ⋙
          (IntegralOnSlice.duality l E W none).closed.tensor := by
  let j := ObjectProperty.ιOfLE
    (show IntegralOnSlice.Good l E W none ≤
      CochainComplex.IsKFlatIndependentCoefficients
        (R := IntegralOnSlice.ring l E W none) from fun _ h ↦ h.1)
  exact isoWhiskerLeft (j.prod j) (IntegralOnSlice.duality l E W none).models.comparison

@[irreducible] private def chartPullTensorIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W T : Scheme.{u}} (f : T ⟶ W) :
    (IntegralOnSlice.duality l E W none).closed.tensor ⋙ ordinaryIntegralDerivedPull l E f ≅
      ((ordinaryIntegralDerivedPull l E f).prod (ordinaryIntegralDerivedPull l E f)) ⋙
        (IntegralOnSlice.duality l E T none).closed.tensor := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  have : PreservesFiniteLimits (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 W)).2.2.2.1
  let hIexists := Scheme.proEtaleAlgebraicInverseImage_exists f
    (completedIntegralCommRingSheafUnrestricted l E W)
  let I := hIexists.choose
  have hI := hIexists.choose_spec
  let := ordinaryTensorPull_additive l E f
  let L := ordinaryTensorPull l E f
  let c := ordinaryTensorRingMap l E f
  have hobj (M : integralTowerModules l E W) :
      L.obj M = SheafOfModules.changeOfRings c (I.modules.obj M) :=
    congrArg (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1} c).obj
      (congrArg (fun F ↦ F.obj M) hI.symm)
  have hmap {M N : integralTowerModules l E W} (a : M ⟶ N) :
      L.map a = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
          eqToHom (hobj N).symm :=
    ordinaryFunctorMap _ _
      (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1} c) hI.symm a
  let k := Classical.choice
    (canonicalRingedTensorComparison_existsUnique.{u + 1, u}
      (completedIntegralCommRingSheafUnrestricted l E W)
      (completedIntegralCommRingSheafUnrestricted l E T) _
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) I c L hobj
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) hmap).1
  let hd := ordinaryTensorDerivedData l E f
  let LF := hd.choose
  let ε := hd.choose_spec.choose
  have hLF := hd.choose_spec.choose_spec.1
  let := hLF
  let α := ringedTopoiCanonicalDerivedTensorComparison.{u + 1, u, u + 2}
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) I c L hobj hmap LF ε hLF
      (IntegralOnSlice.Good l E W none) (IntegralOnSlice.Good l E T none)
      (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
      (IntegralOnSlice.duality l E W none).closed.tensor
      (IntegralOnSlice.duality l E T none).closed.tensor
      (chartTensorRepresentative l E W) (chartTensorRepresentative l E T)
      k _ (ordinaryTensorAdjunction l E f)
  have : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E f)
      (HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ)) := by
    unfold ordinaryIntegralDerivedPull ordinaryIntegralPullCounit
    infer_instance
  let e : LF ≅ ordinaryIntegralDerivedPull l E f :=
    Functor.leftDerivedNatIso _ _ ε (ordinaryIntegralPullCounit l E f)
      (HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ))
      (ordinaryTensorHomotopyIso l E f)
  exact isoWhiskerLeft (IntegralOnSlice.duality l E W none).closed.tensor e.symm ≪≫
    α ≪≫ isoWhiskerRight (NatIso.prod e e) (IntegralOnSlice.duality l E T none).closed.tensor

/-- Bounded finite-projective models of both ordinary restrictions make the restriction
of their ordinary tensor complete. No constructibility or completeness of the inputs
is assumed.

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50; Stacks, Tags 07A4 and 0941
(blueprint: lem-fix-projective-tensor-chart-complete).

Proof:
1. The two ordinary pullback presentations use the same completed coefficient map:
   both direct maps are characterized by their finite quotient projections. Uniqueness
   of these maps identifies the module adjunctions. Uniqueness of left derived
   functors identifies ordinaryIntegralDerivedPull with ordinaryDerivedPull.
2. Apply the canonical ringed-topos derived tensor pullback comparison to the ordinary
   tensor models of IntegralOnSlice.duality. Its normalization on flat-term K-flat
   complexes identifies the pullback of the ordinary tensor with the ordinary tensor
   of the two pullbacks. Transport along the supplied representative isomorphisms.
3. Apply bounded_projective_tensor_complete to P and Q. It proves that their terms
   are flat, both complexes and their signed total tensor are K-flat, and the
   completion unit on that total tensor is invertible. The representative comparison
   of IntegralOnSlice.duality identifies this total tensor with its ordinary tensor.
   Naturality of the completion unit transports invertibility along both isomorphisms.
4. The canonical completion-unit criterion converts invertibility to the stated
   Roos-triangle completeness. Empty schemes, zero ranks, and zero complexes are
   included in the bounded-projective theorem and in that criterion. -/
theorem projectiveTensorChartComplete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (f : T ⟶ W) (hl : ∀ x : T, IsUnit (l : T.residueField x))
    (M N : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (P Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (hP : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k))
    (hQ : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (Q.X k))
    (pP : ∀ k : ℤ, ∃ r : ℕ,
      ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (IntegralOnSlice.rings l E T none)),
      ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (IntegralOnSlice.rings l E T none))) ⟶ P.X k, i ≫ p = 𝟙 _)
    (pQ : ∀ k : ℤ, ∃ r : ℕ,
      ∃ i : Q.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (IntegralOnSlice.rings l E T none)),
      ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (IntegralOnSlice.rings l E T none))) ⟶ Q.X k, i ≫ p = 𝟙 _)
    (eP : Nonempty ((ordinaryIntegralDerivedPull l E f).obj M ≅
      (@DerivedCategory.Q _ _ _ (scalarReductionSourceDerived.{u, u} l E T)).obj P))
    (eQ : Nonempty ((ordinaryIntegralDerivedPull l E f).obj N ≅
      (@DerivedCategory.Q _ _ _ (scalarReductionSourceDerived.{u, u} l E T)).obj Q)) :
    IntegralOnSlice.IsComplete l E T none
      ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E f).obj
        (((IntegralOnSlice.duality.{u, u} l E W none).closed.tensor).obj (M, N))) := by
  obtain ⟨eP⟩ := eP
  obtain ⟨eQ⟩ := eQ
  have hp := (bounded_projective_tensor_complete l E T hl).2.2.2 P hP pP
  let V := (coefficientTotalTensor.{u, u + 1, u}
    (IntegralOnSlice.topology T none) (IntegralOnSlice.ring l E T none)).obj (P, Q)
  obtain ⟨_, _, _, hqK, _, _, hunit⟩ := hp.2.2.2 Q hQ pQ V rfl
  let eV := (IntegralOnSlice.duality l E T none).models.iso
    (IntegralOnSlice.topology T none) (IntegralOnSlice.ring l E T none)
    (IntegralOnSlice.duality l E T none).closed P Q hp.2.1 hqK
  let e := ((chartPullIso l E f).app
      ((IntegralOnSlice.duality l E W none).closed.tensor.obj (M, N))).symm ≪≫
    (chartPullTensorIso l E f).app (M, N) ≪≫
    (IntegralOnSlice.duality l E T none).closed.tensor.mapIso (Iso.prod eP eQ) ≪≫ eV.symm
  apply (IntegralOnSlice.canonicalCompletionUnitCriterion l E T _).1
  exact (NatTrans.isIso_app_iff_of_iso (IntegralOnSlice.completionUnit l E T none) e).2 hunit

end WeilConjectures
