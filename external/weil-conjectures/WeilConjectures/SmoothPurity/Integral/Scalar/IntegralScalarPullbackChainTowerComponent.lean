/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackTowerComposition

/-! # Degreewise scalar pullback chain tower comparison

This is the degreewise component of the normalized scalar pullback chain tower
identity.  It isolates the finite-level generator and Roos-coordinate calculation
from the final chain-map extensionality argument.
(blueprint: lem-pur-integral-scalar-pullback-chain-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F)

section RoosComposition

attribute [local implicit_reducible] integralOperationsRoos
  CochainComplex.mappingCocone
open CochainComplex CochainComplex.HomComplex

private theorem roos_comparison_comp
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    {D : Type v} [Category.{w} D] [Abelian D] [HasCountableProducts D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ D) [H.Additive] (α : F ⋙ G ⟶ H)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (scalarRoosMap F C) ≫
        scalarRoosMap G (C ⋙ F.mapHomologicalComplex (.up ℤ)) ≫
          integralOperationsRoosMap
            (Functor.whiskerLeft C (α.mapHomologicalComplex (.up ℤ))) =
      (α.mapHomologicalComplex (.up ℤ)).app (integralOperationsRoos C) ≫
        scalarRoosMap H C := by
  let F' := F.mapHomologicalComplex (.up ℤ)
  let G' := G.mapHomologicalComplex (.up ℤ)
  let H' := H.mapHomologicalComplex (.up ℤ)
  let α' := α.mapHomologicalComplex (.up ℤ)
  let a := Functor.whiskerLeft C α'
  let pcF := piComparison F' (fun n : ℕ ↦ C.obj (op n))
  let pcG := piComparison G' (fun n : ℕ ↦ F'.obj (C.obj (op n)))
  let pcH := piComparison H' (fun n : ℕ ↦ C.obj (op n))
  let b := Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  have hp : G'.map pcF ≫ pcG ≫ b =
      α'.app (∏ᶜ (fun n : ℕ ↦ C.obj (op n))) ≫ pcH := by
    apply Pi.hom_ext
    intro n
    change (G'.map pcF ≫ pcG ≫ b) ≫
        Pi.π (fun n : ℕ ↦ H'.obj (C.obj (op n))) n =
      (α'.app (∏ᶜ (fun n : ℕ ↦ C.obj (op n))) ≫ pcH) ≫
        Pi.π (fun n : ℕ ↦ H'.obj (C.obj (op n))) n
    dsimp only [b]
    simp only [Category.assoc]
    erw [Pi.map_π]
    change G'.map pcF ≫ pcG ≫
        Pi.π (fun n : ℕ ↦ G'.obj (F'.obj (C.obj (op n)))) n ≫ a.app (op n) = _
    erw [piComparison_comp_π_assoc G' (fun n : ℕ ↦ F'.obj (C.obj (op n))) n]
    erw [piComparison_comp_π H' (fun n : ℕ ↦ C.obj (op n)) n]
    rw [← Category.assoc, ← G'.map_comp]
    dsimp only [pcF]
    rw [piComparison_comp_π]
    with_unfolding_all
      exact α'.naturality (Pi.π (fun n : ℕ ↦ C.obj (op n)) n)
  obtain ⟨hFf, hFs⟩ := scalarRoosCoordinates F C
  obtain ⟨hGf, hGs⟩ := scalarRoosCoordinates G (C ⋙ F')
  obtain ⟨hHf, hHs⟩ := scalarRoosCoordinates H C
  obtain ⟨haf, has⟩ := scalarRoosTowerCoordinates a
  change integralOperationsRoosMap a ≫ mappingCocone.fst
      (scalarRoosBoundary (C ⋙ H')) =
    mappingCocone.fst (scalarRoosBoundary ((C ⋙ F') ⋙ G')) ≫ b at haf
  change ∀ (p q : ℤ) (h : p + -1 = q),
    (integralOperationsRoosMap a).f p ≫
        (mappingCocone.snd (scalarRoosBoundary (C ⋙ H'))).v p q h =
      (mappingCocone.snd (scalarRoosBoundary ((C ⋙ F') ⋙ G'))).v p q h ≫ b.f q at has
  let lhs := G'.map (scalarRoosMap F C) ≫
    scalarRoosMap G (C ⋙ F') ≫ integralOperationsRoosMap a
  let rhs := α'.app (integralOperationsRoos C) ≫ scalarRoosMap H C
  have hf : lhs ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ H')) =
      rhs ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ H')) := by
    dsimp only [lhs, rhs]
    simp only [Category.assoc]
    rw [haf, reassoc_of% hGf]
    rw [← Category.assoc (G'.map _) (G'.map _) _, ← G'.map_comp, hFf, G'.map_comp]
    simp only [Category.assoc]
    rw [hp, hHf]
    with_unfolding_all
      simpa only [Category.assoc] using!
        congrArg (fun z ↦ z ≫ pcH)
        (α'.naturality (mappingCocone.fst (scalarRoosBoundary C)))
  have hs (i : ℤ) : lhs.f i ≫
      (mappingCocone.snd (scalarRoosBoundary (C ⋙ H'))).v i (i - 1) (by omega) =
    rhs.f i ≫
      (mappingCocone.snd (scalarRoosBoundary (C ⋙ H'))).v i (i - 1) (by omega) := by
    have hpi := congrArg (fun z ↦ z.f (i - 1)) hp
    change G.map (pcF.f (i - 1)) ≫ pcG.f (i - 1) ≫ b.f (i - 1) =
      α.app ((∏ᶜ (fun n : ℕ ↦ C.obj (op n))).X (i - 1)) ≫ pcH.f (i - 1) at hpi
    dsimp only [lhs, rhs]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [has i (i - 1) (by omega), reassoc_of% (hGs i)]
    change G.map ((scalarRoosMap F C).f i) ≫
      G.map ((mappingCocone.snd (scalarRoosBoundary (C ⋙ F'))).v
        i (i - 1) (by omega)) ≫ pcG.f (i - 1) ≫ b.f (i - 1) = _
    rw [← Category.assoc (G.map _) (G.map _) _, ← G.map_comp, hFs i, G.map_comp]
    simp only [Category.assoc]
    rw [hpi, hHs i]
    with_unfolding_all
      simpa only [Category.assoc] using!
        congrArg (fun z ↦ z ≫ pcH.f (i - 1))
        (α.naturality ((mappingCocone.snd (scalarRoosBoundary C)).v
          i (i - 1) (by omega)))
  change lhs = rhs
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun z ↦ z.f i) hf
  change lhs.f i ≫ _ = rhs.f i ≫ _ at hfi
  have hid := mappingCocone.id_X (scalarRoosBoundary (C ⋙ H')) i (i - 1) (by omega)
  have hleft := congrArg (fun z ↦ lhs.f i ≫ z) hid
  have hright := congrArg (fun z ↦ rhs.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hleft hright
  rw [hfi, hs i] at hleft
  exact (Category.comp_id _).symm.trans
    (hleft.symm.trans (hright.trans (Category.comp_id _)))

private theorem roos_comparison_tower_comp
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    {D : Type v} [Category.{w} D] [Abelian D] [HasCountableProducts D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ D) [H.Additive] (α : F ⋙ G ⟶ H)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C₁ : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C₂ C₃ : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (a : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C₁)
    (b : C₁ ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ C₂)
    (c : C₂ ⟶ C₃) (d : C ⋙ H.mapHomologicalComplex (.up ℤ) ⟶ C₃)
    (h : Functor.whiskerRight a (G.mapHomologicalComplex (.up ℤ)) ≫ b ≫ c =
      Functor.whiskerLeft C (α.mapHomologicalComplex (.up ℤ)) ≫ d) :
    (G.mapHomologicalComplex (.up ℤ)).map (scalarRoosMap F C ≫ integralOperationsRoosMap a) ≫
        (scalarRoosMap G C₁ ≫ integralOperationsRoosMap b) ≫ integralOperationsRoosMap c =
      (α.mapHomologicalComplex (.up ℤ)).app (integralOperationsRoos C) ≫
        scalarRoosMap H C ≫ integralOperationsRoosMap d := by
  let G' := G.mapHomologicalComplex (.up ℤ)
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (G'.map (integralOperationsRoosMap a)) (scalarRoosMap G C₁) _,
    scalarRoosNaturality]
  simp only [Category.assoc]
  rw [← integralOperationsRoosMap_comp, ← integralOperationsRoosMap_comp, h,
    integralOperationsRoosMap_comp]
  rw [← Category.assoc (scalarRoosMap G _) (integralOperationsRoosMap _) _,
    ← Category.assoc (G'.map (scalarRoosMap F C)) _ _,
    roos_comparison_comp F G H α C]
  simp only [Category.assoc]

end RoosComposition

attribute [local irreducible] integralOrdinaryScalarComp scalarPullbackLevel scalarPullbackTower
  integralOperationsPullbackTowerFunctor integralOperationsRoos

/--
Degreewise form of the normalized pullback Roos chain tower identity.

Source: Stacks 07A4, 08TC; the finite-level generator calculation, reduction
squares, and both Roos product-coordinate calculations in the proof of
`lem-pur-integral-scalar-pullback-chain-tower`.

The proof is the explicit coefficient calculation on finite pullback generators,
extended through sheafification and the strict reduction tower, followed by the
unshifted and shifted Roos coordinate formulas.  This statement is strictly
smaller than the chain-map identity because it fixes one cochain degree; the
chain-map result follows by extensionality in the degree index.
(blueprint: lem-pur-integral-scalar-pullback-chain-tower)
-/
theorem integralScalarPullbackChainTower_f {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) :
    (((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)).map
        (scalarPullbackChain l E L ι f P) ≫
      scalarPullbackChain l L F j f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (integralOperationsPullbackComplexFunctor l F f).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P)).f i =
    ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
      (.up ℤ)).hom.app ((integralOperationsPullbackComplexFunctor l E f).obj P) ≫
        scalarPullbackChain l E F (j.comp ι) f P).f i  := by
  suffices h :
      ((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)).map
          (scalarPullbackChain l E L ι f P) ≫
        scalarPullbackChain l L F j f
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (integralOperationsPullbackComplexFunctor l F f).map
          ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
            (.up ℤ)).hom.app P) =
      (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
        (.up ℤ)).hom.app ((integralOperationsPullbackComplexFunctor l E f).obj P) ≫
          scalarPullbackChain l E F (j.comp ι) f P by
    exact congrArg (fun z ↦ z.f i) h
  let C := (integralOperationsPullbackTowerFunctor l E f).obj P
  let S := integralOrdinaryScalar l E L ι X
  let T := integralOrdinaryScalar l L F j X
  let U := integralOrdinaryScalar l E F (j.comp ι) X
  let T' := T.mapHomologicalComplex (.up ℤ)
  let SP := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P
  let a := (scalarPullbackTower l E L ι f).app P
  let b := (scalarPullbackTower l L F j f).app SP
  let c := (integralOperationsPullbackTowerFunctor l F f).map
    ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
      (.up ℤ)).hom.app P)
  let d := (scalarPullbackTower l E F (j.comp ι) f).app P
  let t := (integralOrdinaryScalarComp l E L ι X F j).hom.mapHomologicalComplex (.up ℤ)
  have ht : Functor.whiskerRight a T' ≫ b ≫ c = Functor.whiskerLeft C t ≫ d :=
    integralScalarPullbackTowerComposition l E L ι F j f P
  simp only [scalarPullbackChain]
  with_unfolding_all
    change T'.map (scalarRoosMap S C ≫ integralOperationsRoosMap a) ≫
      (scalarRoosMap T _ ≫ integralOperationsRoosMap b) ≫ integralOperationsRoosMap c =
    t.app (integralOperationsRoos C) ≫ scalarRoosMap U C ≫ integralOperationsRoosMap d
  exact roos_comparison_tower_comp S T U
    (integralOrdinaryScalarComp l E L ι X F j).hom C _ _ _ a b c d ht

end WeilConjectures
