/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapSummand
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapModel
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapForget
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapUnderived
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison

/-! # Signed swap through the explicit native tensor model

Source: Stacks 06YU, 0FPT; blueprint step 3 of
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Conditional localization of the explicit native swap.
Source: Stacks 06YU and 0FPT, localization of the signed tensor symmetry.
(blueprint: new-sf-native-weil-ringed-swap-conditional).

Proof: the transported derived braiding is modeled by the native chain swap.
The underived hypothesis and the signed summand calculation identify its
forgetful image with the prescribed ordinary chain swap. Naturality of the
localization comparison moves this chain equation into the derived category.
Associativity of composition gives the required equality. -/
theorem native_weil_tensor_ringed_swap_localization_of_underived
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
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (hunderived : ∀ P Q : ProEtaleWeilSheaf k₀ l X,
      Mod.tensorπ P.carrier Q.carrier ≫
          (e.inv.app (Q, P)).hom ≫
          ((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).map
              (nativeRingedSwapUnderived b T adj A P Q).hom).hom ≫
          (e.hom.app (P, Q)).hom =
        (β_ P.carrier.X Q.carrier.X).hom ≫ Mod.tensorπ Q.carrier P.carrier)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q P)
    (hswap : NativeOrdinarySignedSwap l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber swap)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
    let F := nativeForget k₀ l X
    let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let Pc := (U.mapHomologicalComplex (.up ℤ)).obj P
    let Qc := (U.mapHomologicalComplex (.up ℤ)).obj Q
    F.map ((nativeWeilRingedSymmetric b SB βB).toBraidedCategory.braiding
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        U.mapDerivedCategoryFactors.hom.app (CochainComplex.mapBifunctor P Q T) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).hom ≫
        U.mapDerivedCategoryFactors.hom.app (CochainComplex.mapBifunctor Q P T) ≫
        DerivedCategory.Q.map (chain Q P).hom ≫
        DerivedCategory.Q.map (swap Qc Pc).hom := by
  classical
  let F := nativeForget k₀ l X
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let V := U.mapHomologicalComplex (.up ℤ)
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qA := DerivedCategory.Q (C := ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  have hm := nativeRingedSwapComplex_model b T adj A SB TB βB cB P Q hP hQ
  have hc := nativeRingedSwapComplex_forget_of_underived
    k₀ l X T adj e chain hchain b A hunderived swap hswap P Q
  have hl := localizationModel_square q qA F V U.mapDerivedCategoryFactors
    (nativeRingedSwapComplex b T adj A P Q).hom (chain Q P).hom (chain P Q).hom
    (swap (V.obj Q) (V.obj P)).hom hc
  change F.map _ ≫ F.map _ ≫ _ ≫ _ = _
  rw [← F.map_comp_assoc, hm]
  simp only [Functor.map_comp, Category.assoc]
  rw [hl]
  simp only [Category.assoc]
  rfl

/-- The explicit localized native model carries the ringed braiding to the signed swap.

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 0FPT; the summand
calculation in step 3 of lem-sf-native-weil-tensor-ringed-unit-symmetry-representatives.
(blueprint: lem-sf-native-weil-tensor-ringed-swap-localization).

Proof: take the ordinary underived comparison determined uniquely by its
adjunction mate. The binary bridge calculation uses A.uncurry, he and
b.hom_square to compare it with A across restriction. Restriction symmetry and
the actual balanced ordinary symmetry retained in b.ordinary_coherence then
identify the forgotten native swap. Apply the proved conditional localization
assembly: its signed summand calculation gives the ordinary chain square, and
its transported-model and localization equations give the stated identity.
No chosen ordinary derived tensor model or unit comparison is used. -/
theorem native_weil_tensor_ringed_swap_localization
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
    (he : ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
      e.inv.app (P, Q) ≫
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
            (((adj.adj P).homEquiv Q I).symm f) =
        ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f)
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
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q P)
    (hswap : NativeOrdinarySignedSwap l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber swap)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
    let F := nativeForget k₀ l X
    let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let Pc := (U.mapHomologicalComplex (.up ℤ)).obj P
    let Qc := (U.mapHomologicalComplex (.up ℤ)).obj Q
    F.map ((nativeWeilRingedSymmetric b SB βB).toBraidedCategory.braiding
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        U.mapDerivedCategoryFactors.hom.app (CochainComplex.mapBifunctor P Q T) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).hom ≫
        U.mapDerivedCategoryFactors.hom.app (CochainComplex.mapBifunctor Q P T) ≫
        DerivedCategory.Q.map (chain Q P).hom ≫
        DerivedCategory.Q.map (swap Qc Pc).hom := by
  classical
  obtain ⟨d⟩ := native_ordinary_ringed_tensor_underived_data b
  exact native_weil_tensor_ringed_swap_localization_of_underived
    k₀ l X T adj e chain hchain b A
    (nativeRingedSwapUnderived_forget b T adj A e he d) SB TB βB cB swap hswap P Q hP hQ

end AlgebraicGeometry.ProEtaleWeilSheaf
