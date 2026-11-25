/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFinitePullbackCoordinates

/-! # Proper finite projection in scalar reduction coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem unique_conjugate
    {A B : Type*} [Category A] [Category B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (δ : R₂ ≅ R₁) :
    conjugateEquiv a b
      (((a.ofNatIsoRight δ.symm).leftAdjointUniq b).inv) = δ.inv := by
  ext M
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  have h := conjugateEquiv_counit a b
    (((a.ofNatIsoRight δ.symm).leftAdjointUniq b).inv) M
  rw [h]
  have hh := Adjunction.leftAdjointUniq_hom_app_counit b (a.ofNatIsoRight δ.symm) M
  rw [← Adjunction.leftAdjointUniq_inv_app] at hh
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv] at hh
  have hn := ((a.ofNatIsoRight δ.symm).leftAdjointUniq b).inv.naturality (δ.inv.app M)
  change L₂.map (δ.inv.app M) ≫
    ((a.ofNatIsoRight δ.symm).leftAdjointUniq b).inv.app (R₂.obj M) =
      ((a.ofNatIsoRight δ.symm).leftAdjointUniq b).inv.app (R₁.obj M) ≫
        L₁.map (δ.inv.app M) at hn
  have hh' := congrArg (fun z ↦ L₂.map (δ.inv.app M) ≫ z) hh
  simp only [← Category.assoc] at hh'
  rw [hn] at hh'
  simpa only [Category.assoc, ← L₁.map_comp, Iso.inv_hom_id_app,
    L₁.map_id, Category.id_comp] using hh'

private theorem geometric_scalar_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {p : A ⥤ B} {q : B ⥤ A} {P : C ⥤ D} {Q : D ⥤ C}
    {T : A ⥤ C} {U : C ⥤ A} {S : B ⥤ D} {V : D ⥤ B}
    (a : p ⊣ q) (b : P ⊣ Q) (c : T ⊣ U) (d : S ⊣ V)
    (δ : Q ⋙ U ≅ V ⋙ q) (K : B) :
    P.map (((mateEquiv d c).symm (TwoSquare.mk _ _ _ _ δ.inv)).app K) ≫
        b.counit.app (S.obj K) =
      (((a.comp d).ofNatIsoRight δ.symm).leftAdjointUniq (c.comp b)).inv.app
          (q.obj K) ≫ S.map (a.counit.app K) := by
  let θ := (((a.comp d).ofNatIsoRight δ.symm).leftAdjointUniq (c.comp b))
  have h := iterated_mateEquiv_conjugateEquiv a b c d
    (TwoSquare.mk _ _ _ _ θ.inv)
  have hc := unique_conjugate (a.comp d) (c.comp b) δ
  change _ = conjugateEquiv (a.comp d) (c.comp b) θ.inv at h
  rw [hc] at h
  have hm : (mateEquiv a b (TwoSquare.mk _ _ _ _ θ.inv)) =
      ((mateEquiv d c).symm (TwoSquare.mk _ _ _ _ δ.inv)) := by
    apply (mateEquiv d c).injective
    refine NatTrans.ext (funext fun X ↦ ?_)
    simpa only [Equiv.apply_symm_apply] using congrArg (fun t ↦ t.app X) h
  rw [← hm]
  exact mateEquiv_counit a b (TwoSquare.mk _ _ _ _ θ.inv) K

private theorem transport_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {p : A ⥤ B} {q : B ⥤ A} {P P' : C ⥤ D} {Q Q' : D ⥤ C}
    {T RY : A ⥤ C} {S RX : B ⥤ D}
    (a : p ⊣ q) (b : P ⊣ Q) (b' : P' ⊣ Q')
    (αY : T ≅ RY) (αX : S ≅ RX) (d : Q ≅ Q')
    (β : q ⋙ T ⟶ S ⋙ Q) (θ : T ⋙ P ⟶ p ⋙ S)
    (h : ∀ K, P.map (β.app K) ≫ b.counit.app (S.obj K) =
      θ.app (q.obj K) ≫ S.map (a.counit.app K))
    (K : B) :
    P'.map (αY.inv.app (q.obj K) ≫ β.app K ≫ d.hom.app (S.obj K) ≫
        Q'.map (αX.hom.app K)) ≫ b'.counit.app (RX.obj K) =
      P'.map (αY.inv.app (q.obj K)) ≫
        (((b.ofNatIsoRight d).leftAdjointUniq b').inv.app (T.obj (q.obj K))) ≫
        θ.app (q.obj K) ≫ αX.hom.app (p.obj (q.obj K)) ≫ RX.map (a.counit.app K) := by
  let e := (b.ofNatIsoRight d).leftAdjointUniq b'
  have hc (M : D) : e.inv.app (Q'.obj M) ≫
      P.map (d.inv.app M) ≫ b.counit.app M = b'.counit.app M := by
    simpa only [e, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app] using
      Adjunction.leftAdjointUniq_hom_app_counit b' (b.ofNatIsoRight d) M
  simp only [Functor.map_comp, Category.assoc]
  have hz {U V : D} (f : U ⟶ V) :
      P'.map (Q'.map f) ≫ b'.counit.app V = b'.counit.app U ≫ f := by
    simpa only [Functor.comp_map, Functor.id_map] using b'.counit.naturality f
  rw [hz (αX.hom.app K)]
  rw [← Category.assoc (P'.map (d.hom.app (S.obj K))), ← hc]
  simp only [Category.assoc]
  rw [e.inv.naturality_assoc (d.hom.app (S.obj K)), ← P.map_comp_assoc]
  simp only [Iso.hom_inv_id_app, P.map_id, Category.id_comp]
  have hnβ := e.inv.naturality (β.app K)
  change P'.map (β.app K) ≫ e.inv.app (Q.obj (S.obj K)) =
    e.inv.app (T.obj (q.obj K)) ≫ P.map (β.app K) at hnβ
  rw [reassoc_of% hnβ, ← Category.assoc (P.map (β.app K)), h]
  have hnX := αX.hom.naturality (a.counit.app K)
  change S.map (a.counit.app K) ≫ αX.hom.app K =
    αX.hom.app (p.obj (q.obj K)) ≫ RX.map (a.counit.app K) at hnX
  simpa only [Category.assoc] using congrArg
    (fun z ↦ P'.map (αY.inv.app (q.obj K)) ≫ e.inv.app (T.obj (q.obj K)) ≫
      θ.app (q.obj K) ≫ z) hnX

/-- The finite proper scalar comparison is the geometric mate of scalar pullback.

Source: Stacks Tags 03D8, 06YY, 07A6; the adjunction normalizations in
IntegralCompactSupportCoefficientComparison.
(blueprint: lem-sf-integral-finite-proper-mate).

Proof: scalarPull is the unique left-adjoint comparison conjugate to the
restriction/direct-image isomorphism. Its inverse has geometric mate equal to
properComparison: transpose through the two scalar adjunctions and the two
geometric adjunctions; both transposes are the inverse of that same restriction
isomorphism. Injectivity of the composite adjunction Hom bijection proves this
identity. Transport the left and right sides by finiteReductionIso at X and Y
and finiteRingPullbackIso/derived finiteDirectImage_eq. These identifications
preserve units and counits by uniqueness of adjoints and functorial derivation.
Naturality cancels the inverse endpoint factors, and the mate counit identity
gives the displayed equation. No coefficient system, realization model,
constructibility, completeness or properness hypothesis occurs. Zero objects,
identity morphisms and exponent one obey the same adjunction identities. -/
theorem integralFiniteProperMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : Integral l E X) :
    letI := (proEtaleConstantModuleDirectImage_additive_leftExact f
      (Padic.coefficientExtensionRing l E (n + 1))).1
    (finiteDerivedPullback l E n f).map
      ((Functor.whiskerLeft _ (PurCompactSupport.finiteReductionIso l E Y n).inv ≫
      PurCompactSupport.properComparison
        (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f ≫
      Functor.whiskerLeft _
        (Functor.rightDerivedFunctorNatIso
          (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f))).hom ≫
      Functor.whiskerRight (PurCompactSupport.finiteReductionIso l E X n).hom _).app K) ≫
        (finiteAdj l E f n).counit.app
          ((scalarReductionDerivedExtension l E X n).obj K) =
      (finiteScalarPullback l E f n).inv.app ((ringedPush l E f).obj K) ≫
        (scalarReductionDerivedExtension l E X n).map
          ((ringedAdj l E f).counit.app K) := by
  let := (proEtaleConstantModuleDirectImage_additive_leftExact f
    (Padic.coefficientExtensionRing l E (n + 1))).1
  let R := PurCompactSupport.completed l E
  let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
  let r := proEtaleRingDerivedAdjunction f (R.ring Y) (R.ring X) (R.pull f)
  let s := proEtaleRingDerivedAdjunction f (S.ring Y) (S.ring X) (S.pull f)
  let v := pbcDerivedScalarAdjunction (a.map Y)
  let u := pbcDerivedScalarAdjunction (a.map X)
  let δ := proEtaleRingRestrictionDerivedDirectImage f
    (R.ring Y) (S.ring Y) (R.ring X) (S.ring X)
    (a.map Y) (a.map X) (R.pull f) (S.pull f) (a.square f)
  let d := Functor.rightDerivedFunctorNatIso
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f))
  have h := transport_mate r s (finiteAdj l E f n)
    (PurCompactSupport.finiteReductionIso l E Y n)
    (PurCompactSupport.finiteReductionIso l E X n) d
    (PurCompactSupport.properComparison a f) (PurCompactSupport.scalarPull a f).inv
    (fun K ↦ geometric_scalar_mate r s v u δ K) K
  dsimp only [Functor.comp_obj]
  convert h using 1 <;>
    simp only [finiteScalarPullback, finiteRingPullbackIso, Iso.trans_inv,
      Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Category.assoc, R, S, a, r, s, d, ringedPush, ringedPull,
      Functor.comp_obj, Functor.id_obj, ringedAdj,
      PurCompactSupport.push, PurCompactSupport.pull, PurCompactSupport.scalarPull,
      PurCompactSupport.reduction, PurCompactSupport.finite]

end WeilConjectures.IntegralSystemRealization
