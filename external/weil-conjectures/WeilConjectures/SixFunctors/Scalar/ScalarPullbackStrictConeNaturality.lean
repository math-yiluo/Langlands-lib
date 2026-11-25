/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictConeData
import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictTowerConstruction
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictCoherence
import WeilConjectures.SixFunctors.Scalar.ScalarPullbackUniqueDerivedDescent
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

set_option linter.privateModule false

/-! # Assembly and derived descent of the normalized strict scalar pullback map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor
  integralOperationsPullbackComplexFunctor integralOperationsGoodLocalization
  integralOperationsPullbackOnGood
  CochainComplex.mappingCocone
  completedOrdinaryScalarComplex scalarPullbackSourceTower scalarPullbackRoosEnd
attribute [local instance 5000] integralTowerHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section ProductComparison
universe a b c d e f
open CochainComplex
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

private noncomputable def coconeCoordinates {K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

private theorem product_roos_isIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := scalarRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let f : F.obj ((mappingCocone (scalarRoosBoundary C)).X i) ⟶
        (mappingCocone (scalarRoosBoundary (C ⋙ G))).X i := (scalarRoosMap F C).f i
    let : IsIso (pc.f i) := hpcf i
    let : IsIso (pc.f (i - 1)) := hpcf (i - 1)
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : f ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        simpa only [f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
          using congrArg (fun z ↦ z.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso (f ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (@asIso _ _ _ _ (pc.f i) (hpcf i))
          (@asIso _ _ _ _ (pc.f (i - 1)) (hpcf (i - 1)))).hom)
      infer_instance
    change IsIso f
    let : IsIso eX.hom := eX.isIso_hom
    exact IsIso.of_isIso_comp_right f eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

end ProductComparison

end WeilConjectures
