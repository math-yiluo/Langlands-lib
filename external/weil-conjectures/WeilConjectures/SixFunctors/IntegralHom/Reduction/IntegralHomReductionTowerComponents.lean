/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorComparison
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionTowerUnitModels

/-! # Component comparisons for the integral Hom reduction tower

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingSheaf CategoryTheory.sheafCompose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

private theorem augmentation_of_unit
    {C : Type*} [Category C] {V : Type*} [Category V]
    (F G : C ⥤ V) (α : F ⟶ G) {B Q : C} (ι : B ⟶ Q)
    {X : V} (b : X ⟶ F.obj B) (a : X ⟶ G.obj B)
    (hunit : b ≫ α.app B = a) :
    b ≫ F.map ι ≫ α.app Q = a ≫ G.map ι := by
  rw [α.naturality ι, ← Category.assoc, hunit]

/-- The finite signed Hom comparisons respect consecutive quotient maps and the quotient
unit on fixed representatives. No product or completeness assertion occurs here, and
neither the representative nor its K-flat resolution is chosen by this theorem.

Source: blueprint order 2478, steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components).

Proof: Use separate tensor models preserving the two quotient augmentations and
the specified apex map e. The signed tensor-Hom comparison is natural in the
coefficient complex. Its components at the two-term free coefficient complexes
are invertible by the degreewise criterion; localization preserves this. Invert
that comparison and conjugate by the two model isomorphisms to obtain one
family of components. On K-flat source and K-injective target models,
the finite comparison sends f tensor z to the function sending x to
(-1)^(degree(z)*degree(x)) f(x) tensor z. This formula is natural in the two-term
quotient complex. Apply it to the quotient chain map whose components are the
uniformizer and identity to obtain the consecutive-transition square. Apply it
to the degree-zero quotient unit to obtain the augmentation square. The scalar
unit and evaluation normalizations identify these with the actual recorded maps.
Resolution independence transports both squares to the fixed q and q'. This
uses arbitrary unbounded K and does not require any countable product. -/
theorem reductionTower_components
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let H := (Functor.curry.obj
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
    ∃ θ : ∀ n : ℕ, H.obj ((integralReductionTower l E Y D hl P).obj (op n)) ≅
        (integralReductionTower l E Y D hl P').obj (op n),
      (∀ n : ℕ,
        H.map ((integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op) ≫
          (θ n).hom = (θ (n + 1)).hom ≫
            (integralReductionTower l E Y D hl P').map (homOfLE n.le_succ).op) ∧
      ∀ n : ℕ, e.inv ≫ (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) =
        H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
          (θ n).hom := by
  obtain ⟨A, I, Q, hQ, ι, s, t, s0, t0, hs, ht, hunit⟩ :=
    reductionTower_unit_models l E Y D hl K P G P' G' q q' hq hq' e
  obtain ⟨α, hα⟩ := signedHomTensorComparison_exists Y
    (completedIntegralCommRingSheaf l E Y D hl) A I
  let β := Functor.whiskerRight α DerivedCategory.Q
  have (n : ℕᵒᵖ) : IsIso (β.app (Q.obj n)) := by
    obtain ⟨hz, ⟨eNeg⟩, ⟨eZero⟩⟩ := hQ n.unop
    have (j : ℤ) : IsIso ((α.app (Q.obj n)).f j) :=
      twoTermFreeHomTensor_component_isIso Y _ A I (Q.obj n)
        hz eNeg eZero (α.app (Q.obj n)) (hα (Q.obj n)) j
    have : IsIso (α.app (Q.obj n)) :=
      HomologicalComplex.Hom.isIso_of_components _
    change IsIso (DerivedCategory.Q.map (α.app (Q.obj n)))
    infer_instance
  let βQ := Functor.whiskerLeft Q β
  have (n : ℕᵒᵖ) : IsIso (βQ.app n) := by
    change IsIso (β.app (Q.obj n))
    infer_instance
  have : IsIso βQ := NatIso.isIso_of_isIso_app βQ
  let τ := s ≪≫ (asIso βQ).symm ≪≫ t.symm
  refine ⟨fun n ↦ τ.app (op n), ?_, ?_⟩
  · intro n
    exact τ.hom.naturality (homOfLE n.le_succ).op
  · intro n
    have hbase : (e.inv ≫ t0.hom) ≫ β.app _ = s0.hom := by
      set_option backward.isDefEq.respectTransparency false in
      simpa only [β, Functor.whiskerRight_app, Category.assoc] using hunit _ (hα _)
    have hnat := augmentation_of_unit _ _ β (ι.app (op n))
      (e.inv ≫ t0.hom) s0.hom hbase
    have hc :
        (e.inv ≫ (integralReductionTowerCone l E Y D hl q' hq').π.app (op n)) ≫
            t.hom.app (op n) ≫ β.app (Q.obj (op n)) =
          ((Functor.curry.obj
            (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)).map
              ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
            s.hom.app (op n) := by
      set_option backward.isDefEq.respectTransparency false in
      calc
        _ = (e.inv ≫ t0.hom) ≫ _ ≫ β.app (Q.obj (op n)) := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ e.inv ≫ f ≫ β.app (Q.obj (op n))) (ht n)
        _ = _ := hnat
        _ = _ := (hs n).symm
    apply (cancel_mono (t.hom.app (op n))).1
    apply (cancel_mono (β.app (Q.obj (op n)))).1
    set_option backward.isDefEq.respectTransparency false in
    simpa only [τ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.app_hom, asIso_inv, NatIso.isIso_inv_app, Functor.whiskerLeft_app,
      Iso.inv_hom_id_app_assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, βQ] using hc

end WeilConjectures.IntegralHom
