/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorAdjunctionExchange
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorExchangeRepresentative
import WeilConjectures.SixFunctors.IntegralHom.Scalar.IntegralHomScalarTensorExchangeChain
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionCounitCoherence
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorExchangeNaturality

/-! # Scalar tensor exchange on K-flat representatives

Source: Stacks Tags 06YY and 08J7, scalar tensor comparison and evaluation.
(blueprint: lem-sfb-integral-hom-scalar-tensor-exchange-representatives)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe d u
open CategoryTheory Opposite
namespace WeilConjectures.IntegralHom

private theorem exchange_naturality
    {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) (b : HomReductionTensorModel R)
    (K K' A A' : Derived.{u, u} X R) (f : K ⟶ K') (g : A ⟶ A') :
    a.tensor.map (Prod.mkHom f g) ≫ tensorAdjunctionExchange R a b K' A' =
      tensorAdjunctionExchange R a b K A ≫ b.tensor.map (Prod.mkHom g f) := by
  have ha : a.tensor.map (Prod.mkHom f g) =
      a.tensor.map (Prod.mkHom f (𝟙 A)) ≫ a.tensor.map (Prod.mkHom (𝟙 K') g) := by
    rw [← Functor.map_comp]
    simp
  have hb : b.tensor.map (Prod.mkHom g f) =
      b.tensor.map (Prod.mkHom (𝟙 A) f) ≫ b.tensor.map (Prod.mkHom g (𝟙 K')) := by
    rw [← Functor.map_comp]
    simp
  rw [ha, Category.assoc, tensorAdjunctionExchange_naturality_second,
    ← Category.assoc, tensorAdjunctionExchange_naturality_first, Category.assoc, ← hb]

-- Paste the representative and counit squares with the tensor models kept abstract.
attribute [-instance] derivedCategory in
/-- The two normalized scalar tensor comparisons commute with adjunction exchange
on K-flat representatives. The two inputs are independent complexes; no internal
Hom input or evaluation morphism occurs in this square.

Source: Stacks Tags 06YY and 08J7, the K-flat scalar tensor and evaluation
normalizations in the integral Hom reduction construction.
(blueprint: lem-sfb-integral-hom-scalar-tensor-exchange-representatives).

Proof: use the representative comparisons to identify the source tensors with the
signed total tensors of P,Q and Q,P. Identify the reduced inputs with the ordinary
extensions of P,Q by their derived counits, which are isomorphisms on K-flat
complexes. Both reduced complexes are K-flat, by the two normalization packets.
The evaluation normalizations identify each adjunction-defined exchange with the
signed interchange x tensor y maps to (-1)^(ij) y tensor x in bidegree (i,j).
The ordinary extension units in both packets send x to 1 tensor x. The scalar
comparison of m is specified in the inverse direction to the total comparison of b;
on the unit images its equation sends (1 tensor x) tensor (1 tensor y) to
1 tensor (x tensor y). Consequently each composite in the displayed square sends
a generating tensor to the same signed tensor. Scalars and tensor generation give
the equality in each bidegree, sheafification preserves it, and direct-sum totalization
makes it an equality of complexes. The two derived counit normalization squares
transport this equality to the displayed square; cancel their invertible components
and the representative isomorphisms. No derived internal Hom comparison is used.
The unit, empty site, zero complexes, and exponent n=0 obey the same formulas. -/
theorem scalarTensorExchange_representatives
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl))
    (m : ReductionPresentation l E X D hl a n)
    (b : IntegralHomReductionTensorData D l hl E X n)
    (P Q : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (hP : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P)
    (hQ : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) Q) :
    tensorAdjunctionExchange.{u} (integralCoefficientCommRingSheaf l E X n)
        m.target b.target
        ((integralDerivedReduction l E X D hl n).obj
          ((DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj P))
        ((integralDerivedReduction l E X D hl n).obj
          ((DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj Q)) ≫
      b.tensor.inv.app
        ((DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj Q,
          (DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj P) =
    m.mu.inv.app
        ((DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj P,
          (DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj Q) ≫
      (integralDerivedReduction l E X D hl n).map
        (tensorAdjunctionExchange.{u} (completedIntegralCommRingSheaf l E X D hl)
          a b.source
          ((DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj P)
          ((DerivedCategory.Q (C := completedIntegralModuleSheaves l E X D hl)).obj Q)) := by
  classical
  let F := integralDerivedReduction l E X D hl n
  let G := (integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)
  let R := completedIntegralCommRingSheaf l E X D hl
  let S := integralCoefficientCommRingSheaf l E X n
  let K := DerivedCategory.Q.obj P
  let A := DerivedCategory.Q.obj Q
  let rP := reductionCounit l E X D hl n P
  let rQ := reductionCounit l E X D hl n Q
  obtain ⟨hp, hq, beta, hbeta, hpure, hnorm⟩ := m.normalization P Q hP hQ
  have : IsIso beta := hbeta
  have : IsIso rP := reductionCounit_isIso D l hl E X n P hP
  have : IsIso rQ := reductionCounit_isIso D l hl E X n Q hQ
  have : IsIso (Prod.mkHom rQ rP) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  let a0 := a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)
  let a1 := m.target.representative.hom.app (⟨G.obj P, hp⟩, ⟨G.obj Q, hq⟩)
  let b0 := (b.source.compute Q P hQ hP).hom
  let b1 := (b.target.compute (G.obj Q) (G.obj P) hq hp).hom
  let am := m.target.tensor.map (Prod.mkHom rP rQ)
  let bm := b.target.tensor.map (Prod.mkHom rQ rP)
  let e0 := tensorAdjunctionExchange R a b.source K A
  let e1 := tensorAdjunctionExchange S m.target b.target (F.obj K) (F.obj A)
  let e2 := tensorAdjunctionExchange S m.target b.target
    (DerivedCategory.Q.obj (G.obj P)) (DerivedCategory.Q.obj (G.obj Q))
  let s0 := (tensorRepresentativeSwap R P Q).hom
  let s1 := (tensorRepresentativeSwap S (G.obj P) (G.obj Q)).hom
  have hb0 : a0 ≫ e0 = DerivedCategory.Q.map s0 ≫ b0 :=
    tensorAdjunctionExchange_representative R a b.source P Q hP hQ s0
      (tensorRepresentativeSwap_pure R P Q)
  have hb1 : a1 ≫ e2 = DerivedCategory.Q.map s1 ≫ b1 :=
    tensorAdjunctionExchange_representative S m.target b.target (G.obj P) (G.obj Q)
      hp hq s1 (tensorRepresentativeSwap_pure S (G.obj P) (G.obj Q))
  have hn : am ≫ e2 = e1 ≫ bm :=
    exchange_naturality S m.target b.target _ _ _ _ rP rQ
  have hc := scalarTensorExchange_chain D l hl E X n b P Q (asIso beta) hpure
  change beta ≫ G.map s0 ≫ b.total Q P = s1 at hc
  have hcb : DerivedCategory.Q.map beta ≫ DerivedCategory.Q.map (G.map s0) ≫
      DerivedCategory.Q.map (b.total Q P) = DerivedCategory.Q.map s1 := by
    erw [← Functor.map_comp, ← Functor.map_comp, hc]
  have hr := reductionCounit_naturality D l hl E X n s0
  have hb := b.normalize Q P hQ hP
  simp only [← reductionCounit_eq_complexComparison D l hl E X n] at hb
  change F.map b0 ≫ b.tensor.hom.app (A, K) ≫ bm =
    reductionCounit l E X D hl n (homReductionTotal R Q P) ≫
      DerivedCategory.Q.map (b.total Q P) ≫ b1 at hb
  have ha : F.map a0 ≫ m.mu.hom.app (K, A) ≫ am ≫
      m.target.representative.inv.app (⟨G.obj P, hp⟩, ⟨G.obj Q, hq⟩) ≫
      DerivedCategory.Q.map beta =
    reductionCounit l E X D hl n (((totalTensor.{u, u} X R).obj P).obj Q) := hnorm
  have he2 : e2 = m.target.representative.inv.app
      (⟨G.obj P, hp⟩, ⟨G.obj Q, hq⟩) ≫ DerivedCategory.Q.map s1 ≫ b1 := by
    erw [← hb1]
    simp only [a1, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  change e1 ≫ b.tensor.inv.app (A, K) = m.mu.inv.app (K, A) ≫ F.map e0
  apply (cancel_mono (b.tensor.hom.app (A, K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  apply (cancel_epi (m.mu.hom.app (K, A))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply (cancel_mono bm).1
  apply (cancel_epi (F.map a0)).1
  erw [Category.comp_id]
  calc
    F.map a0 ≫ (m.mu.hom.app (K, A) ≫ e1) ≫ bm =
        F.map a0 ≫ m.mu.hom.app (K, A) ≫ am ≫ e2 := by
      simp only [Category.assoc, hn]
    _ = F.map a0 ≫ m.mu.hom.app (K, A) ≫ am ≫
        m.target.representative.inv.app (⟨G.obj P, hp⟩, ⟨G.obj Q, hq⟩) ≫
        DerivedCategory.Q.map beta ≫ DerivedCategory.Q.map (G.map s0) ≫
        DerivedCategory.Q.map (b.total Q P) ≫ b1 := by
      erw [he2, ← hcb]
      simp only [Category.assoc]
    _ = reductionCounit l E X D hl n
        (((totalTensor.{u, u} X R).obj P).obj Q) ≫
        DerivedCategory.Q.map (G.map s0) ≫ DerivedCategory.Q.map (b.total Q P) ≫ b1 := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ DerivedCategory.Q.map (G.map s0) ≫
          DerivedCategory.Q.map (b.total Q P) ≫ b1) ha
    _ = F.map (DerivedCategory.Q.map s0) ≫
        reductionCounit l E X D hl n (homReductionTotal R Q P) ≫
        DerivedCategory.Q.map (b.total Q P) ≫ b1 := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ DerivedCategory.Q.map (b.total Q P) ≫ b1) hr.symm
    _ = F.map (DerivedCategory.Q.map s0) ≫ F.map b0 ≫
        b.tensor.hom.app (A, K) ≫ bm := by
      erw [hb]
    _ = F.map a0 ≫ (F.map e0 ≫ b.tensor.hom.app (A, K)) ≫ bm := by
      with_unfolding_all
        simpa only [Functor.map_comp, Category.assoc] using congrArg
          (fun f ↦ F.map f ≫ b.tensor.hom.app (A, K) ≫ bm) hb0.symm

end WeilConjectures.IntegralHom
