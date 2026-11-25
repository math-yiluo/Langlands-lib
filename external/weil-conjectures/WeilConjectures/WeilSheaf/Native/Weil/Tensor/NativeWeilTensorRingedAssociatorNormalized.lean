/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorModel
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedForgetLocalization
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedForgetBinary
import WeilConjectures.CategoryTheory.Tensor.TensorComparisonFromModels

/-! # Native representative associativity with the canonical ordinary tensor

Source: Stacks 06YU, 0FPT; direct native tensor transport on representatives.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local implicit_reducible] Mod.monoidalCategoryCochainComplex Monoidal.induced

attribute [local irreducible] SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  nativeWeilRingedMonoidal nativeWeilRingedTensorModel NativeOrdinaryKFlat NativeTensorKFlat
  nativeRingedAssociatorComplex nativeRingedTripleLeft nativeRingedTripleRight
  nativeWeilRingedTensorComplexModel

-- Keep localization and total-tensor definitions folded in the concrete representative types.
/-- Associativity after normalizing the ordinary monoidal structure.
Source: Stacks 06YU, 0FPT
(blueprint: lem-sf-native-weil-ringed-associator-normalized).

Proof: invert the four given binary representative equations. Native tensor
closure makes the inner and outer representatives K-flat. The canonical lax
localization tensorator is invertible on these pairs. Paste the binary squares
using inverse tensorator naturality, apply its associativity and the native
associator model equation, and localize the signed chain comparison. Cancel the
iterated model isomorphisms using associativity_transport. -/
theorem nativeRingedAssociatorRepresentatives_normalized
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
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB) :
    letI _mC : MonoidalCategory (CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
    letI := _mC.toMonoidalCategoryStruct
    ∀ (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          (MonoidalCategory.tensor _).obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (_hcanonical : ∃ κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P,
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) ∧
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
        (_hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q),
        HEq (ordinaryModel P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv))
    (t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ MonoidalCategory.tensor _)
    (_hforget : (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        (MonoidalCategory.tensor _).map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom))
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (_hP : NativeTensorKFlat k₀ l X T P) (_hQ : NativeTensorKFlat k₀ l X T Q)
    (_hN : NativeTensorKFlat k₀ l X T N),
    letI := nativeWeilRingedMonoidal b SB
      let F := nativeForget k₀ l X
      let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
      F.map (α_ (q.obj P) (q.obj Q) (q.obj N)).hom ≫
          t.hom.app (q.obj P, q.obj Q ⊗ q.obj N) ≫
          (F.obj (q.obj P) ◁ t.hom.app (q.obj Q, q.obj N)) =
        t.hom.app (q.obj P ⊗ q.obj Q, q.obj N) ≫
          (t.hom.app (q.obj P, q.obj Q) ▷ F.obj (q.obj N)) ≫
          (α_ (F.obj (q.obj P)) (F.obj (q.obj Q)) (F.obj (q.obj N))).hom := by
  classical
  letI mC : MonoidalCategory (CochainComplex (ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
    Mod.monoidalCategoryCochainComplex
  letI := mC.toMonoidalCategoryStruct
  intro ordinaryModel hcanonical t hforget P Q N hP hQ hN
  letI := nativeWeilRingedMonoidal b SB
  obtain ⟨κ, hκ, hmodel⟩ := hcanonical
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let V := U.mapHomologicalComplex (.up ℤ)
  let F := nativeForget k₀ l X
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qA := DerivedCategory.Q (C := ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  letI : Functor.LaxMonoidal qA := inferInstance
  let ε := U.mapDerivedCategoryFactors
  let c (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
      V.obj (nativeTensorComplex T P Q) ≅ V.obj P ⊗ V.obj Q :=
    chain Q P ≪≫ κ (V.obj Q) (V.obj P)
  have hflat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P) :=
    native_weil_tensor_forget_kflat k₀ l X T chain P hP
  have hμ (P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
      (hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q) :
      IsIso (Functor.LaxMonoidal.μ qA P Q) :=
    nativeOrdinaryKFlat_isIso_mu l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      κ P Q (Or.inr hQ)
  have hμ' (P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
      (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P) :
      IsIso (Functor.LaxMonoidal.μ qA P Q) :=
    nativeOrdinaryKFlat_isIso_mu l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      κ P Q (Or.inl hP)
  have binary := nativeRingedTensorModel_forget_binary k₀ l X T adj chain b A
    SB TB βB cB ordinaryModel κ hmodel t hforget
  let pq := nativeTensorComplex T P Q
  let qn := nativeTensorComplex T Q N
  have hpq := nativeTensorComplex_kflat b T adj A P Q hP hQ
  have hqn := nativeTensorComplex_kflat b T adj A Q N hQ hN
  let := hμ (V.obj P) (V.obj Q) (hflat Q hQ)
  let := hμ (V.obj Q) (V.obj N) (hflat N hN)
  let := hμ (V.obj pq) (V.obj N) (hflat N hN)
  let := hμ' (V.obj P) (V.obj qn) (hflat P hP)
  let := hμ (V.obj P ⊗ V.obj Q) (V.obj N) (hflat N hN)
  let := hμ' (V.obj P) (V.obj Q ⊗ V.obj N) (hflat P hP)
  let bPQ := (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).symm
  let bQN := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N Q hN).symm
  let bL := (nativeWeilRingedTensorModel b T adj A SB TB βB cB N pq hN).symm
  let bR := (nativeWeilRingedTensorModel b T adj A SB TB βB cB qn P hqn).symm
  have hB := nativeRingedAssociatorComplex_model b T adj A SB TB βB cB P Q N hP hQ hN
  have hC := nativeRingedAssociatorComplex_forget_localization k₀ l X T adj e he chain
    hchain b A κ hκ P Q N
  exact associativity_from_inverse_tensor_models F qA t
    (P := q.obj P) (Q := q.obj Q) (N := q.obj N)
    (PQ := q.obj pq) (QN := q.obj qn)
    (L := q.obj (nativeTensorComplex T pq N))
    (R := q.obj (nativeTensorComplex T P qn))
    (P' := V.obj P) (Q' := V.obj Q) (N' := V.obj N)
    (PQ' := V.obj pq) (QN' := V.obj qn)
    (L' := V.obj (nativeTensorComplex T pq N))
    (R' := V.obj (nativeTensorComplex T P qn)) bPQ bQN bL bR
    (c P Q) (c Q N) (c pq N) (c P qn)
    (ε.app P) (ε.app Q) (ε.app N) (ε.app pq) (ε.app qn)
    (ε.app (nativeTensorComplex T pq N)) (ε.app (nativeTensorComplex T P qn))
    (q.map (nativeRingedAssociatorComplex b T adj A P Q N).hom)
    hB (binary P Q hP hQ) (binary Q N hQ hN) (binary pq N hpq hN)
    (binary P qn hP hqn) (by
      simpa only [c, pq, qn, U, V, F, q, qA, ε, Iso.app_hom, Category.assoc] using hC)

end AlgebraicGeometry.ProEtaleWeilSheaf
