/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedIso
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainLaws
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Total-complex data for normalized native ringed tensor comparisons

This module records the total comparison, its homogeneous summand formula, and
naturality.  The scalar sign is a parameter so this interface can be used with
the item module's specified normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a va b vb
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private def curryTensorComparison
    {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
    (T : B ⥤ B ⥤ B) (W : A ⥤ A ⥤ A) (F : B ⥤ A)
    (e : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj W) :
    (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ A).obj F).obj F).obj W :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun Q ↦ e.app (P, Q)) (by
    intro Q Q' g
    simpa using e.hom.naturality (X := (P, Q)) (Y := (P, Q')) (𝟙 P, g))) (by
    intro P P' f
    apply NatTrans.ext
    funext Q
    simpa using e.hom.naturality (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q))

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

structure NativeWeilRingedTensorChainData
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (sign : ∀ (_p _q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z), Y ⟶ Z) where
  chain (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q T) ≅
      (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
          (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
  summand (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    b.native.functor.map (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq) ≫
        (chain P Q).hom.f n =
      sign p q ((U.underived (P.X p) (Q.X q)).hom ≫
        RingedForgetTensorTransposition.tensorSummand b.J b.R
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) q p n hqp)
  naturality (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (f : P ⟶ P') (g : Q ⟶ Q') :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (chain P' Q').hom =
      (chain P Q).hom ≫
        (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
          (Prod.mkHom ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f))

/-- The total comparison, summand equation, and naturality.
Source: Stacks 06YN and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).

The unrestricted sign parameter in the imported interface is too strong: an
arbitrary endomorphism assignment need not preserve isomorphisms.  We therefore
require it to be the normalized Koszul scalar action.  The proof first assembles
the underived comparisons into a bifunctor isomorphism, applies the generic total
comparison, and then uses the total-complex flip isomorphism. -/
theorem native_weil_tensor_ringed_chain_data
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
        ZSMul.zsmul ((_p * _q).negOnePow : ℤ) _f) :
    Nonempty (NativeWeilRingedTensorChainData b T adj U sign) := by
  obtain ⟨e, he⟩ := native_weil_tensor_ringed_underived_iso b T adj U
  let c := curryTensorComparison T
    (MonoidalCategory.curriedTensor
      (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).flip
    b.native.functor e
  let chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
            (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) := by
    intro P Q
    let r := HomologicalComplex.mapBifunctorComparison c.hom (.up ℤ) P Q
    let f := HomologicalComplex.mapBifunctorFlipIso
      ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
      ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
      (MonoidalCategory.curriedTensor
        (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) (.up ℤ)
    exact asIso (r ≫ f.hom)
  have hτ : ∀ P Q : ProEtaleWeilSheaf k₀ l X,
      (c.hom.app P).app Q = (U.underived P Q).hom := by
    intro P Q
    simpa [c, curryTensorComparison] using he P Q
  have hchain : ∀ P Q,
      (chain P Q).hom =
        (HomologicalComplex.mapBifunctorComparison c.hom (.up ℤ) P Q ≫
          (HomologicalComplex.mapBifunctorFlipIso
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
            (MonoidalCategory.curriedTensor
              (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) (.up ℤ)).hom) := by
    intro P Q
    rfl
  obtain ⟨hs, hn⟩ := native_weil_tensor_ringed_chain_laws b T adj U sign hsign
    c.hom hτ chain hchain
  exact ⟨{ chain := chain, summand := hs, naturality := hn }⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
