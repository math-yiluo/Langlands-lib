/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.CommSq

/-! # Laws for the normalized native ringed total comparison

Source: Stacks 06YN and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The uncurried total bifunctor acts by the simultaneous map on both variables. -/
private theorem uncurry_total_map
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ a, (F.obj a).PreservesZeroMorphisms]
    [∀ (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q F (.up ℤ)]
    {P P' : CochainComplex A ℤ} {Q Q' : CochainComplex B ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).map
        (Prod.mkHom f g) = HomologicalComplex.mapBifunctorMap f g F (.up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f]
  erw [(F.obj (P'.X p)).map_id (Q.X q), F.map_id (P'.X p)]
  simp only [NatTrans.id_app, Category.id_comp]

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

attribute [local irreducible] SheafOfModules.monoidalCategory
  HomologicalComplex.mapBifunctorComparison HomologicalComplex.mapBifunctorFlipIso

/-- Naturality of the normalized total comparison, independently of its summand law. -/
private theorem chain_comparison_naturality
    (τ : (Functor.postcompose₂.obj b.native.functor).obj T ⟶
      (((Functor.whiskeringLeft₂
        (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).obj b.native.functor).obj
          b.native.functor).obj
        (MonoidalCategory.curriedTensor
          (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).flip)
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
            (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hchain : ∀ P Q,
      (chain P Q).hom =
        (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q ≫
          (HomologicalComplex.mapBifunctorFlipIso
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
            (MonoidalCategory.curriedTensor
              (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) (.up ℤ)).hom)) :
    ∀ (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (b.native.functor.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (chain P' Q').hom =
          (chain P Q).hom ≫
            (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
              (Prod.mkHom ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
                ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f)) := by
  intro P Q P' Q' f g
  have hc := HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) f g
  have hf := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
    ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
    ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f)
    (MonoidalCategory.curriedTensor
      (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) (.up ℤ)
  conv_lhs => rhs; rw [hchain P' Q']
  conv_rhs => lhs; rw [hchain P Q]
  simpa only [coefficientTotalTensor, uncurry_total_map] using
    (CommSq.vert_comp (CommSq.mk hc) (CommSq.mk hf)).w

-- The total-complex coproducts of the ringed tensor are found by a deep search.
/-- The signed summand and bifunctor naturality laws for the canonical total map.
Source: Stacks 06YN and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).

Proof: expand the generic `mapBifunctorComparison` and the total-complex flip
isomorphism.  The former gives naturality and the latter gives the Koszul scalar
on each homogeneous summand; the normalized underived comparison identifies the
component with `U.underived`. -/
theorem native_weil_tensor_ringed_chain_laws
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (sign : ∀ (_p _q : ℤ)
      {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z), Y ⟶ Z)
    (hsign : ∀ (_p _q : ℤ)
      {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z),
      sign _p _q _f =
        letI : AddCommGroup (Y ⟶ Z) :=
          @Preadditive.homGroup
            (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
            _ inferInstance Y Z
        ZSMul.zsmul ((_p * _q).negOnePow : ℤ) _f)
    (τ : (Functor.postcompose₂.obj b.native.functor).obj T ⟶
      (((Functor.whiskeringLeft₂
        (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).obj b.native.functor).obj
          b.native.functor).obj
        (MonoidalCategory.curriedTensor
          (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).flip)
    (hτ : ∀ P Q : ProEtaleWeilSheaf k₀ l X,
      (τ.app P).app Q = (U.underived P Q).hom)
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
            (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hchain : ∀ P Q,
      (chain P Q).hom =
        (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q ≫
          (HomologicalComplex.mapBifunctorFlipIso
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
            (MonoidalCategory.curriedTensor
              (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) (.up ℤ)).hom)) :
    (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
      b.native.functor.map (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq) ≫
          (chain P Q).hom.f n =
        sign p q ((U.underived (P.X p) (Q.X q)).hom ≫
          RingedForgetTensorTransposition.tensorSummand b.J b.R
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) q p n hqp)) ∧
      (∀ (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (b.native.functor.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (chain P' Q').hom =
          (chain P Q).hom ≫
            (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
              (Prod.mkHom ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
                ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f))) := by
  constructor
  · intro P Q p q n hpq hqp
    conv_lhs =>
      rw [hchain P Q, HomologicalComplex.comp_f, ← Category.assoc,
        HomologicalComplex.mapBifunctorComparison_f τ (.up ℤ) P Q n,
        HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
          τ (.up ℤ) P Q p q n hpq,
        Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
    dsimp only [HomologicalComplex.mapBifunctorComparisonApp]
    conv_lhs => lhs; rw [hτ (P.X p) (Q.X q)]
    conv_rhs => rw [hsign p q]
    have hσ : ComplexShape.σ (.up ℤ) (.up ℤ) (.up ℤ) q p = (p * q).negOnePow := by
      change (q * p).negOnePow = _
      rw [mul_comm q p]
    conv_lhs => rw [hσ, Units.smul_def, Preadditive.comp_zsmul]
    rfl
  · exact chain_comparison_naturality b T τ chain hchain

end AlgebraicGeometry.ProEtaleWeilSheaf
