/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapSummand

/-! # Ordinary forgetting of the native signed chain swap

Source: Stacks 06YU and 0FPT, homogeneous-summand comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- The native and ordinary mapped-complex instances need additional elaboration fuel.
/-- The native signed chain swap becomes the prescribed ordinary signed swap.
Source: Stacks 06YU and 0FPT; homogeneous-summand part of native tensor transport.
(blueprint: new-sf-native-weil-ringed-swap-forget).

Proof: use the signed summand formula for the native chain swap and expand
both ordinary total comparisons using hchain. Apply the assumed underived
balanced-tensor equation. Its Koszul scalar agrees with hswap since p*q=q*p.
Balanced-tensor and coproduct extensionality then give the chain-map equation.
No K-flatness or derived-category argument is used. -/
theorem nativeRingedSwapComplex_forget_of_underived
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    (A : NativeWeilRingedTensorComplexes b T adj)
    (hunderived : ∀ P Q : ProEtaleWeilSheaf k₀ l X,
      Mod.tensorπ P.carrier Q.carrier ≫
          (e.inv.app (Q, P)).hom ≫
          ((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).map
              (nativeRingedSwapUnderived b T adj A P Q).hom).hom ≫
          (e.hom.app (P, Q)).hom =
        (β_ P.carrier.X Q.carrier.X).hom ≫ Mod.tensorπ Q.carrier P.carrier)
    (swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q P)
    (hswap : NativeOrdinarySignedSwap l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber swap)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
 :
    let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let V := U.mapHomologicalComplex (.up ℤ)
    V.map (nativeRingedSwapComplex b T adj A P Q).hom ≫ (chain P Q).hom =
      (chain Q P).hom ≫ (swap (V.obj Q) (V.obj P)).hom := by
  classical
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let V := U.mapHomologicalComplex (.up ℤ)
  change V.map _ ≫ _ = _
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map U
  intro q p hqp
  change q + p = n at hqp
  have hpq : p + q = n := by omega
  change U.map (HomologicalComplex.ιMapBifunctor Q P T (.up ℤ) q p n hqp) ≫
      (U.map ((nativeRingedSwapComplex b T adj A P Q).hom.f n) ≫
        (chain P Q).hom.f n) =
    U.map (HomologicalComplex.ιMapBifunctor Q P T (.up ℤ) q p n hqp) ≫
      ((chain Q P).hom.f n ≫ (swap (V.obj Q) (V.obj P)).hom.f n)
  rw [← U.map_comp_assoc, nativeRingedSwapComplex_summand b T adj A P Q p q n hpq hqp]
  simp only [Functor.map_zsmul, Functor.map_comp, Preadditive.zsmul_comp, Category.assoc]
  rw [hchain P Q p q n hpq, reassoc_of% (hchain Q P q p n hqp)]
  apply (cancel_epi (e.inv.app (Q.X q, P.X p))).1
  apply Mod.tensorLeft_obj_hom_ext
  simp only [Preadditive.comp_zsmul, Mod.comp_hom', Mod.zsmul_hom,
    Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% (hunderived (P.X p) (Q.X q))]
  simpa only [V, U, Functor.mapHomologicalComplex_obj_X, Functor.prod_obj,
    Endofunctor.IsoAlgebra.forget_obj, mul_comm q p, Units.smul_def,
    Preadditive.zsmul_comp, Category.assoc] using
    (hswap (V.obj Q) (V.obj P) q p n hqp hpq).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
