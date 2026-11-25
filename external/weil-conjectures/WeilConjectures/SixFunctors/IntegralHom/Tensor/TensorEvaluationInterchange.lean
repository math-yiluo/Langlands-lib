/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Interchanging tensor factors before evaluation

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 0A8X and 08J7.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option quotPrecheck false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

local notation "J" => AlgebraicGeometry.Scheme.ProEt.topology Y

attribute [local instance 2000] abSheafify abLocallyBijective

private noncomputable local instance : MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.cochainModulesMonoidal R
private noncomputable local instance : SymmetricCategory (Modules.{t, u} Y R) :=
  SheafOfModules.cochainModulesSymmetric R
private noncomputable local instance : MonoidalClosed (Modules.{t, u} Y R) :=
  RingedDerivedNative.baseClosed.{t + 1, t, u} J R
private noncomputable local instance : HasLimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  RingedDerivedNative.baseLimits.{t + 1, t, u} J R
private noncomputable local instance : HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  RingedDerivedNative.baseColimits.{t + 1, t, u} J R
private noncomputable local instance :
    ∀ (X Z : GradedObject ℤ (Modules.{t, u} Y R)), X.HasTensor Z :=
  RingedDerivedNative.gradedTensor.{t + 1, t, u} J R
private noncomputable local instance : ∀ (W X Z V : GradedObject ℤ (Modules.{t, u} Y R)),
    GradedObject.HasTensor₄ObjExt W X Z V :=
  RingedDerivedNative.gradedTensorFour.{t + 1, t, u} J R
private noncomputable local instance : ∀ (X Z V : GradedObject ℤ (Modules.{t, u} Y R)),
    GradedObject.HasGoodTensor₁₂Tensor X Z V :=
  RingedDerivedNative.gradedTensorLeft.{t + 1, t, u} J R
private noncomputable local instance : ∀ (X Z V : GradedObject ℤ (Modules.{t, u} Y R)),
    GradedObject.HasGoodTensorTensor₂₃ X Z V :=
  RingedDerivedNative.gradedTensorRight.{t + 1, t, u} J R

attribute [local instance 4000] HomologicalComplex.monoidalCategory

private noncomputable local instance complexMonoidal :
    MonoidalCategory (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  HomologicalComplex.monoidalCategory (Modules.{t, u} Y R) (.up ℤ)

private noncomputable local instance complexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (Modules.{t, u} Y R) (.up ℤ)

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification

private theorem generator_map
    (A B A' B' : CochainComplex (Modules.{t, u} Y R) ℤ) (f : A ⟶ A') (g : B ⟶ B')
    (p q n : ℤ) (h : p + q = n) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X p).val.obj U) (y : (B.X q).val.obj U) :
    ((f ⊗ₘ g).f n).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} J R A B p q n h U x y) =
      coefficientTensorGenerator.{u, t + 1, t} J R A' B' p q n h U
        ((f.f p).val.app U x) ((g.f q).val.app U y) := by
  have hm := HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor (Modules.{t, u} Y R))
    (.up ℤ) p q n h
  change HomologicalComplex.ιTensorObj A B p q n h ≫ (f ⊗ₘ g).f n =
    (f.f p ▷ B.X q) ≫ (A'.X p ◁ g.f q) ≫
      HomologicalComplex.ιTensorObj A' B' p q n h at hm
  rw [← Category.assoc, ← tensorHom_def] at hm
  have he := congrArg (fun k ↦ k.val.app U
    (RingedDerivedNative.pureTensor.{t + 1, t, u} J R (A.X p) (B.X q) U x y)) hm
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, RingedDerivedNative.pureTensor_map] at he
  erw [RingedDerivedNative.generator_eq, RingedDerivedNative.generator_eq]
  exact he

private theorem generator_zsmul_right
    (A B : CochainComplex (Modules.{t, u} Y R) ℤ) (p q n : ℤ) (h : p + q = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X p).val.obj U) (y : (B.X q).val.obj U) (z : ℤ) :
    coefficientTensorGenerator.{u, t + 1, t} J R A B p q n h U x (z • y) =
      z • coefficientTensorGenerator.{u, t + 1, t} J R A B p q n h U x y := by
  have ht : x ⊗ₜ[R.obj.obj U] (z • y) = z • (x ⊗ₜ[R.obj.obj U] y) :=
    map_zsmul
      (TensorProduct.mk (R.obj.obj U) ((A.X p).val.obj U) ((B.X q).val.obj U) x) z y
  dsimp only [coefficientTensorGenerator]
  rw [ht]
  simp only [map_zsmul]

private theorem associator_inv_generator
    (A B C : CochainComplex (Modules.{t, u} Y R) ℤ)
    (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X p).val.obj U) (y : (B.X q).val.obj U) (z : (C.X r).val.obj U) :
    ((α_ A B C).inv.f n).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} J R A (B ⊗ C) p qr n hn' U x
          (coefficientTensorGenerator.{u, t + 1, t} J R B C q r qr hqr U y z)) =
      coefficientTensorGenerator.{u, t + 1, t} J R (A ⊗ B) C pq r n hn U
        (coefficientTensorGenerator.{u, t + 1, t} J R A B p q pq hpq U x y) z := by
  have ha := RingedDerivedNative.associator_formula.{t + 1, t, u} J R
    A B C p q r pq qr n hpq hqr hn hn' U x y z
  have he := congrArg (fun w ↦ ((α_ A B C).inv.f n).val.app U w) ha
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val] at he
  have hi := congrArg (fun f ↦ f.f n) (α_ A B C).hom_inv_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
  rw [hi] at he
  exact he.symm

private theorem exchange_pure
    (H P I Q : CochainComplex (Modules.{t, u} Y R) ℤ) (e : H ⊗ P ⟶ I)
    (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (H.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U) :
    (((α_ H Q P).hom ≫ (𝟙 H ⊗ₘ (β_ Q P).hom) ≫
        (α_ H P Q).inv ≫ (e ⊗ₘ 𝟙 Q)).f (p + (a + b))).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} J R (H ⊗ Q) P
          (a + b) p (p + (a + b)) (add_comm (a + b) p) U
          (coefficientTensorGenerator.{u, t + 1, t} J R H Q a b (a + b) rfl U v z) x) =
      (b * p).negOnePow •
        coefficientTensorGenerator.{u, t + 1, t} J R I Q (p + a) b (p + (a + b))
          (add_assoc p a b) U
          ((e.f (p + a)).val.app U
            (coefficientTensorGenerator.{u, t + 1, t} J R H P a p (p + a)
              (add_comm a p) U v x)) z := by
  let gen := coefficientTensorGenerator.{u, t + 1, t} J R
  let k := p + (a + b)
  let h : a + (b + p) = k := by dsimp [k]; omega
  let sig : ℤ := (b * p).negOnePow
  let f₂ := (𝟙 H ⊗ₘ (β_ Q P).hom)
  let f₃ := (α_ H P Q).inv
  let f₄ := (e ⊗ₘ 𝟙 Q)
  let qpx := gen Q P b p (b + p) rfl U z x
  let pqx := gen P Q p b (b + p) (add_comm p b) U x z
  let t₁ := gen H (Q ⊗ P) a (b + p) k h U v qpx
  let t₂ := gen H (P ⊗ Q) a (b + p) k h U v pqx
  let t₃ := gen (H ⊗ P) Q (p + a) b k (add_assoc p a b) U
    (gen H P a p (p + a) (add_comm a p) U v x) z
  let t₄ := gen I Q (p + a) b k (add_assoc p a b) U
    ((e.f (p + a)).val.app U
      (gen H P a p (p + a) (add_comm a p) U v x)) z
  have h₁ := RingedDerivedNative.associator_formula.{t + 1, t, u} J R
    H Q P a b p (a + b) (b + p) k rfl rfl (by dsimp [k]; omega) h U v z x
  have h₂ : (f₂.f k).val.app U t₁ =
      gen H (P ⊗ Q) a (b + p) k h U v
        (((β_ Q P).hom.f (b + p)).val.app U qpx) :=
    generator_map Y R H (Q ⊗ P) H (P ⊗ Q) (𝟙 H) (β_ Q P).hom
      a (b + p) k h U v qpx
  have hbraid : ((β_ Q P).hom.f (b + p)).val.app U qpx = sig • pqx :=
    RingedDerivedNative.symmetry_formula.{t + 1, t, u} J R Q P b p (b + p)
      rfl (add_comm p b) U z x
  have h₂' : (f₂.f k).val.app U t₁ = sig • t₂ :=
    h₂.trans ((congrArg (fun w ↦ gen H (P ⊗ Q) a (b + p) k h U v w) hbraid).trans
      (generator_zsmul_right Y R H (P ⊗ Q) a (b + p) k h U v pqx sig))
  have h₃ : (f₃.f k).val.app U t₂ = t₃ :=
    associator_inv_generator Y R H P Q a p b (p + a) (b + p) k
      (add_comm a p) (add_comm p b) (add_assoc p a b) h U v x z
  have h₄ : (f₄.f k).val.app U t₃ = t₄ :=
    generator_map Y R (H ⊗ P) Q I Q e (𝟙 Q)
      (p + a) b k (add_assoc p a b) U
      (gen H P a p (p + a) (add_comm a p) U v x) z
  change (f₄.f k).val.app U ((f₃.f k).val.app U
    ((f₂.f k).val.app U (((α_ H Q P).hom.f k).val.app U _))) = sig • t₄
  calc
    _ = (f₄.f k).val.app U ((f₃.f k).val.app U ((f₂.f k).val.app U t₁)) :=
      congrArg (fun w ↦ (f₄.f k).val.app U
        ((f₃.f k).val.app U ((f₂.f k).val.app U w))) h₁
    _ = (f₄.f k).val.app U ((f₃.f k).val.app U (sig • t₂)) :=
      congrArg (fun w ↦ (f₄.f k).val.app U ((f₃.f k).val.app U w)) h₂'
    _ = sig • (f₄.f k).val.app U ((f₃.f k).val.app U t₂) := by simp only [map_zsmul]
    _ = sig • (f₄.f k).val.app U t₃ :=
      congrArg (fun w ↦ sig • (f₄.f k).val.app U w) h₃
    _ = sig • t₄ := congrArg (fun w ↦ sig • w) h₄

/-- Interchanging the last two tensor factors before applying a chain map has
exactly the Koszul sign of their degrees.
Source: Stacks Tags 03EK and 0FPQ; blueprint
`lem-coef-integral-hom-reduction.proof.md`, paragraph 1
(blueprint: lem-sf-tensor-evaluation-interchange).

Proof: reassociate (H tensor Q) tensor P, apply the braiding from Q tensor P
to P tensor Q, reassociate back, and apply e tensor the identity of Q. The
associator formulas preserve pure tensors; the braiding formula contributes
(-1)^(bp). Tensoring maps acts on the two factors, and linearity carries that
sign through the remaining maps. This is valid without any boundedness or
flatness hypotheses. -/
theorem tensorEvaluation_interchange
    (H P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (e : (((totalTensor.{t, u} Y R).obj H).obj P) ⟶ I) :
    ∃ psi : (((totalTensor.{t, u} Y R).obj
        (((totalTensor.{t, u} Y R).obj H).obj Q)).obj P) ⟶
        (((totalTensor.{t, u} Y R).obj I).obj Q),
      ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (H.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        (psi.f (p + (a + b))).val.app U
            (coefficientTensorGenerator.{u, t + 1, t} J R
              (((totalTensor.{t, u} Y R).obj H).obj Q) P
              (a + b) p (p + (a + b)) (add_comm (a + b) p) U
              (coefficientTensorGenerator.{u, t + 1, t} J R H Q a b (a + b) rfl U v z) x) =
          (b * p).negOnePow •
            coefficientTensorGenerator.{u, t + 1, t} J R I Q (p + a) b (p + (a + b))
              (add_assoc p a b) U
              ((e.f (p + a)).val.app U
                (coefficientTensorGenerator.{u, t + 1, t} J R H P a p (p + a)
                  (add_comm a p) U v x)) z := by
  refine ⟨(α_ H Q P).hom ≫ (𝟙 H ⊗ₘ (β_ Q P).hom) ≫
    (α_ H P Q).inv ≫ (e ⊗ₘ 𝟙 Q), ?_⟩
  intro a b p U v z x
  exact exchange_pure Y R H P I Q e a b p U v z x

end WeilConjectures.IntegralHom
