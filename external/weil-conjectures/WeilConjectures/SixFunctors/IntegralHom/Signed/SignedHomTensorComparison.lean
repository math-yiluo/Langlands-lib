/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorComponents
import all WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorComparisonConstruction
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
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # The signed tensor--Hom map before passing to derived categories

Source: the finite-free construction in the first paragraph of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 08J9 and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

open CategoryTheory.MonoidalCategory CategoryTheory.RingedDerivedNative
attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose

attribute [local instance] signedModuleMonoidal signedModuleSymmetric
  signedModulePreadditive signedModuleClosed signedModuleLimits signedModuleColimits
  signedGradedTensor signedGradedTensorFour signedGradedTensorLeft signedGradedTensorRight
attribute [local instance 5000] signedComplexMonoidal signedComplexBraided
attribute [local instance 10000] signedComplexStruct
attribute [local irreducible] homComplexFunctor chainEquiv SheafOfModules.monoidalCategory
  exchangeEquiv signedGenerator

private theorem tensor_generator
    {P P' Q Q' : CochainComplex (Modules.{t, u} Y R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (a b k : ℤ) (h : a + b = k)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U) :
    ((f ⊗ₘ g).f k).val.app U
        (signedGenerator.{t, u} Y R P Q a b k h U x y) =
      signedGenerator.{t, u} Y R P' Q' a b k h U
        ((f.f a).val.app U x) ((g.f b).val.app U y) := by
  unfold signedGenerator
  have he := CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y) (R := R) f g a b k h U x y
  rw [totalTensor_map_eq] at he
  exact he

private theorem generator_smul_right
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (a b k : ℤ) (h : a + b = k)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U) (r : ℤˣ) :
    signedGenerator.{t, u} Y R P Q a b k h U x (r • y) =
      r • signedGenerator.{t, u} Y R P Q a b k h U x y := by
  unfold signedGenerator
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let adj := PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R).obj)
  let F := ((((adj.unit.app ((P.X a).val ⊗ (Q.X b).val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X a) (Q.X b)).inv.val).app U) ≫
      (HomologicalComplex.ιMapBifunctor P Q (curriedTensor (Modules.{t, u} Y R))
        (.up ℤ) a b k h).val.app U).hom)
  change F (x ⊗ₜ[R.obj.obj U] ((r : ℤ) • y)) =
    (r : ℤ) • F (x ⊗ₜ[R.obj.obj U] y)
  rw [TensorProduct.tmul_smul]
  exact map_zsmul F _ _

private theorem section_units_smul {M N : Modules.{t, u} Y R} (f : M ⟶ N)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (r : ℤˣ) (x : M.val.obj U) :
    f.val.app U (r • x) = r • f.val.app U x :=
  map_zsmul_unit (f.val.app U).hom r x

private theorem generator_transport
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (a b k k' : ℤ) (h : a + b = k) (h' : k = k')
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U) :
    (eqToHom (congrArg (fun j ↦ (P ⊗ Q).X j) h')).val.app U
        (signedGenerator.{t, u} Y R P Q a b k h U x y) =
      signedGenerator.{t, u} Y R P Q a b k' (h.trans h') U x y := by
  subst k'
  rfl

private theorem complex_iso_inv_hom
    {P Q : CochainComplex (Modules.{t, u} Y R) ℤ} (e : P ≅ Q) (k : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : (P.X k).val.obj U) :
    (e.inv.f k).val.app U ((e.hom.f k).val.app U x) = x :=
  congrArg (fun f ↦ (f.f k).val.app U x) e.hom_inv_id

private theorem associator_generator
    (M Q P : CochainComplex (Modules.{t, u} Y R) ℤ)
    (a b p ab bp k : ℤ) (hab : a + b = ab) (hbp : b + p = bp)
    (habp : ab + p = k) (habp' : a + bp = k)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (M.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U) :
    ((α_ M Q P).hom.f k).val.app U
        (signedGenerator.{t, u} Y R (M ⊗ Q) P ab p k habp U
          (signedGenerator.{t, u} Y R M Q a b ab hab U v z) x) =
      signedGenerator.{t, u} Y R M (Q ⊗ P) a bp k habp' U v
        (signedGenerator.{t, u} Y R Q P b p bp hbp U z x) := by
  unfold signedGenerator
  exact (complexConstraints.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R).associator
      M Q P a b p ab bp k hab hbp habp habp' U v z x

private theorem braiding_generator
    (Q P : CochainComplex (Modules.{t, u} Y R) ℤ)
    (b p k : ℤ) (h : b + p = k) (h' : p + b = k)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U) :
    ((β_ Q P).hom.f k).val.app U (signedGenerator.{t, u} Y R Q P b p k h U z x) =
      (b * p).negOnePow • signedGenerator.{t, u} Y R P Q p b k h' U x z := by
  unfold signedGenerator
  exact (complexConstraints.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R).symmetry
      Q P b p k h h' U z x

private theorem totalPair_generator
    (M Q : CochainComplex (Modules.{t, u} Y R) ℤ) (a b : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (M.X a).val.obj U) (z : (Q.X b).val.obj U) :
    totalPair.{t, u} Y R M Q a b U v z =
      signedGenerator.{t, u} Y R M Q a b (a + b) rfl U v z := by
  unfold signedGenerator
  rfl

private theorem exchange_generator
    (M P I Q : CochainComplex (Modules.{t, u} Y R) ℤ) (e : M ⊗ P ⟶ I)
    (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (M.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U) :
    (((α_ M Q P).hom ≫ M ◁ (β_ Q P).hom ≫ (α_ M P Q).inv ≫ e ▷ Q).f
        (p + (a + b))).val.app U
      (signedGenerator.{t, u} Y R (M ⊗ Q) P (a + b) p
        (p + (a + b)) (add_comm _ _) U
        (signedGenerator.{t, u} Y R M Q a b (a + b) rfl U v z) x) =
      (b * p).negOnePow •
        signedGenerator.{t, u} Y R I Q (p + a) b (p + (a + b))
          (by omega) U
          ((e.f (p + a)).val.app U
            (signedGenerator.{t, u} Y R M P a p (p + a)
              (add_comm _ _) U v x)) z := by
  have ha := associator_generator.{t, u} Y R M Q P
    a b p (a + b) (b + p) (p + (a + b)) rfl rfl (by omega) (by omega) U v z x
  have hb := braiding_generator.{t, u} Y R Q P
    b p (b + p) rfl (add_comm _ _) U z x
  have ha' := associator_generator.{t, u} Y R M P Q
    a p b (p + a) (b + p) (p + (a + b)) (add_comm _ _) (add_comm _ _)
    (by omega) (by omega) U v x z
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [ha]
  rw [← id_tensorHom, tensor_generator]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  rw [hb, generator_smul_right]
  simp only [section_units_smul]
  rw [← ha', complex_iso_inv_hom]
  rw [← tensorHom_id, tensor_generator]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]

/-- The signed tensor--Hom map is natural in an arbitrary coefficient complex.
This constructs maps only: neither a quotient resolution nor an invertibility
assertion is part of this statement.

Source: the first paragraph of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`, finite-free construction;
Stacks Tags 08J9 and 0A8X
(blueprint: lem-sf-signed-hom-tensor-comparison).

Proof: let H=Hom(P,I), and take evaluation H tensor P to I to be the inverse
transpose of its identity under the existing normalized chain tensor--Hom
equivalence. Associate (H tensor Q) tensor P, braid Q past P, reassociate,
and apply evaluation tensor identity. Curry this map. Associator and braiding
naturality and tensor interchange give naturality in Q before currying; the
naturality identities of the equivalence then give a natural transformation.
On the homogeneous generator (v tensor z) tensor x of degrees (a,b,p), the
associators contribute no sign and the middle braiding contributes (-1)^(bp).
Normalized evaluation sends v tensor x to v(x). The resulting formula is
exactly IsSignedHomTensor, with the degree transport (p+a)+b=p+(a+b).
No boundedness, flatness or injectivity is used; zero complexes and the empty
scheme are included. -/
theorem signedHomTensorComparison_exists
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) :
    ∃ α : (totalTensor.{t, u} Y R).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) ⟶
        (totalTensor.{t, u} Y R).obj I ⋙
          (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := R)).obj (op P),
      ∀ Q, IsSignedHomTensor.{t, u} Y R P I Q (α.app Q) := by
  refine ⟨exchangeNatural.{t, u} Y R P I, ?_⟩
  intro Q a b p U v z x
  erw [totalPair_generator, totalPair_generator]
  let H := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I
  let ev := (exchangeEquiv.{t, u} Y R H P I).symm (𝟙 H)
  have hc := exchangeEquiv_symm_pure.{t, u} Y R (H ⊗ Q) P (I ⊗ Q)
    (exchangeMap.{t, u} Y R P I Q) (a + b) p (p + (a + b)) (add_comm _ _) rfl U
    (signedGenerator.{t, u} Y R H Q a b (a + b) rfl U v z) x
  simp only [H, exchangeMap, Equiv.symm_apply_apply] at hc
  change ((exchangeUncurry.{t, u} Y R P I Q).f (p + (a + b))).val.app U
      (signedGenerator.{t, u} Y R (H ⊗ Q) P (a + b) p
        (p + (a + b)) (add_comm _ _) U
        (signedGenerator.{t, u} Y R H Q a b (a + b) rfl U v z) x) =
    evaluate.{t, u} Y R P (I ⊗ Q) (a + b) p U
      (((exchangeMap.{t, u} Y R P I Q).f (a + b)).val.app U
        (signedGenerator.{t, u} Y R H Q a b (a + b) rfl U v z)) x at hc
  change evaluate.{t, u} Y R P (I ⊗ Q) (a + b) p U
      (((exchangeMap.{t, u} Y R P I Q).f (a + b)).val.app U
        (signedGenerator.{t, u} Y R H Q a b (a + b) rfl U v z)) x = _
  rw [← hc]
  have hev := exchangeEquiv_symm_pure.{t, u} Y R H P I (𝟙 H)
    a p (p + a) (add_comm _ _) rfl U v x
  change (ev.f (p + a)).val.app U
      (signedGenerator.{t, u} Y R H P a p (p + a)
        (add_comm _ _) U v x) = evaluate.{t, u} Y R P I a p U v x at hev
  unfold exchangeUncurry
  rw [exchange_generator Y R H P I Q ev a b p U v z x, hev]
  congr 1
  exact (generator_transport Y R I Q (p + a) b ((p + a) + b)
    (p + (a + b)) rfl (add_assoc _ _ _) U (evaluate.{t, u} Y R P I a p U v x) z).symm

end WeilConjectures.IntegralHom
