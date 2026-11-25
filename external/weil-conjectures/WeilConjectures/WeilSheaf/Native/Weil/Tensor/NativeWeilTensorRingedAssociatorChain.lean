/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainAssembly
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainTransport
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainRingedSquare

/-! # Signed forgetting of the explicit native chain associator

Source: Stacks 0FPQ, 0FNG, 06YU, 0FPT; homogeneous-triple part of native tensor transport.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Elaborating the statement unfolds the deep cochain tensor instance terms of the chain data.
/-- The comparison of total complexes respects reassociation before localization.
Source: Stacks 0FPQ, 0FNG, 06YU, 0FPT; homogeneous-triple step of native tensor transport.
(blueprint: lem-sf-native-weil-ringed-associator-chain).

Proof: precompose with each triple coproduct inclusion and each balanced tensor
quotient. Expand the two native ringed total comparisons using A.summand, and
the two forgetting comparisons using hchain and the summand equation for kappa.
The normalized mates he and A.uncurry identify the underived tensor maps across
b.square by b.hom_square. Underived associativity of b.underived.coherence then
identifies the two composites. The exchange signs agree by
pq+(p+q)r=qr+p(q+r). Local balanced tensor extensionality and the coproduct
universal property give equality of chain maps. This statement uses no derived
category, derived tensor comparison, K-flat replacement, or associativity square
for an arbitrary derived natural transformation. -/
theorem nativeRingedAssociatorComplex_forget
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
    (A : NativeWeilRingedTensorComplexes b T adj)
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P)
    (hκ : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) :
    let U := (Endofunctor.IsoAlgebra.forget
      (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)
    let c : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
        U.obj (nativeTensorComplex T P Q) ≅ U.obj P ⊗ U.obj Q :=
      fun P Q ↦ chain Q P ≪≫ κ (U.obj Q) (U.obj P)
    ∀ P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      U.map (nativeRingedAssociatorComplex b T adj A P Q N).hom ≫
          (c P (nativeTensorComplex T Q N)).hom ≫
          (U.obj P ◁ (c Q N).hom) =
        (c (nativeTensorComplex T P Q) N).hom ≫
          ((c P Q).hom ▷ U.obj N) ≫ (α_ (U.obj P) (U.obj Q) (U.obj N)).hom := by
  let D : NativeWeilTensorRingedAssociatorChainData k₀ l X T :=
    { adj := adj
      e := e
      he := he
      chain := chain
      hchain := hchain
      b := b
      A := A
      κ := κ
      hκ := hκ }
  have hD := nativeChainForgetAssociator_assembly D (fun P Q N n p q h ↦
    nativeChainForgetComponent_transport D P Q N
      (fun m ↦ nativeRingedAssociatorComponent_square D P Q N m) n p q h)
  simpa only [nativeChainForgetAssociator, nativeChainForgetU, nativeChainForgetC,
    D, Iso.trans_hom] using hD

end AlgebraicGeometry.ProEtaleWeilSheaf
