/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFinitePullbackCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullFiniteSquare
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

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
/-- The normalized Hom equation for an exact left adjoint on homotopy representatives. -/
private theorem exactDerivedTranspose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : HomotopyCategory C (.up ℤ)) (K : HomotopyCategory D (.up ℤ))
    (f : (F.mapHomotopyCategory (.up ℤ)).obj P ⟶ K) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (F.mapDerivedCategoryFactorsh.hom.app P ≫ DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv P K f) ≫
        G.rightDerivedFunctorUnit.app K := by
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit P
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj P) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app P) = _ at hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hu, Category.assoc]
  have hn := G.rightDerivedFunctorUnit.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

/-- Deriving the specified ordinary uniqueness comparison preserves its normalization. -/
private theorem derivedUniq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F H : C ⥤ D} {G U : D ⥤ C}
    [F.Additive] [H.Additive] [G.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : F ⊣ G) (b : H ⊣ U) (η : G ≅ U) :
    ((a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        (Functor.rightDerivedFunctorNatIso η)).leftAdjointUniq
          b.mapDerivedCategoryRightDerivedAdjunction) =
      Functor.mapDerivedCategoryNatIso ((a.ofNatIsoRight η).leftAdjointUniq b) := by
  let e := (a.ofNatIsoRight η).leftAdjointUniq b
  let ηh : G.mapHomotopyCategory (.up ℤ) ≅ U.mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory η.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory η.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, η.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, η.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have hν (P : HomotopyCategory C (.up ℤ)) :
      (a.mapHomotopyCategory (.up ℤ)).homEquiv _ _
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) ≫
        ηh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj P) =
      (b.mapHomotopyCategory (.up ℤ)).unit.app P := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    rw [Adjunction.homEquiv_unit, Adjunction.mapHomotopyCategory_unit_app_quotient,
      Adjunction.mapHomotopyCategory_unit_app_quotient]
    change ((HomotopyCategory.quotient C (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C (.up ℤ)).map _) ≫
        (HomotopyCategory.quotient C (.up ℤ)).map _ =
      (HomotopyCategory.quotient C (.up ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro i
    change (a.unit.app (P.X i) ≫ G.map (e.hom.app (P.X i))) ≫
      η.hom.app (H.obj (P.X i)) = b.unit.app (P.X i)
    have he := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight η) b (P.X i)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at he
    simpa only [Adjunction.homEquiv_unit, e] using he
  have hρ (K : HomotopyCategory D (.up ℤ)) :
      G.rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatIso η).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map (ηh.hom.app K) ≫ U.rightDerivedFunctorUnit.app K := by
    simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      Functor.rightDerivedNatTrans_app, Functor.whiskerRight_app, ηh]
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro P
  apply (cancel_mono (H.mapDerivedCategoryFactorsh.hom.app P)).1
  rw [Functor.mapDerivedCategoryNatIso_fach]
  exact normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Qh) (QB := DerivedCategory.Qh)
    (a.mapHomotopyCategory (.up ℤ)) (b.mapHomotopyCategory (.up ℤ))
    a.mapDerivedCategoryRightDerivedAdjunction b.mapDerivedCategoryRightDerivedAdjunction
    (fun P ↦ F.mapDerivedCategoryFactorsh.hom.app P)
    (fun P ↦ H.mapDerivedCategoryFactorsh.hom.app P)
    (fun K ↦ G.rightDerivedFunctorUnit.app K)
    (fun K ↦ U.rightDerivedFunctorUnit.app K)
    (exactDerivedTranspose a) (exactDerivedTranspose b)
    ηh (Functor.rightDerivedFunctorNatIso η)
    (fun P ↦ (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) hν hρ P

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finitePullbackIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    letI : (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f).Additive :=
      sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    finiteRingPullbackIso l E f n =
      Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n f) := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let : (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  exact derivedUniq
    (proEtaleRingModuleAdjunction f
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l E (n + 1)))
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f))

private theorem finiteScalarPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteScalarPullback l E f n = integralFiniteScalarPull l E f n := by
  unfold finiteScalarPullback integralFiniteScalarPull
  rw [← finitePullbackIso_eq l E f n]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
  rw [← (finiteRingPullbackIso l E f n).hom.naturality]

/-- Finite coordinates of the inverse quotient/pullback comparison on a good complex.

Source: Stacks Tags 03D7, 03EL, 07A6, 0941; current blueprint
fix-prop-coherence.proof.md, preservation of coefficient comparisons of units and counits.
(blueprint: lem-sf-integral-finite-pullback-normalization).

Proof: the existing integralReductionPullFiniteSquare gives the forward equation
on every derived object. Its finite geometric comparison is obtained by deriving
finitePullbackIso, whereas finiteScalarPullback uses uniqueness of the derived
left adjoints. The derived Hom transpose equation and normalized adjoint
uniqueness identify these two geometric comparisons. Naturality moves the finite
reduction presentation through this common comparison, identifying the two scalar
pullback isomorphisms. Specialize the forward equation to Q(P), view it as equality
of composite isomorphisms, and take inverses. Functors preserve these inverses,
and reassociation gives exactly the displayed equation. This uses no new finite
normalization obligation and no property of P beyond its underlying complex.
Empty schemes, the zero complex, the identity morphism and n=0 obey the same
adjunction and inverse identities. -/
theorem integralFinitePullback_onGood (o : Operations l E)
    (model : RealizationModel l E o) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    (finiteScalarPullback l E f n).inv.app (DerivedCategory.Q.obj P.obj) ≫
        ((calculus l E X).reductionEvaluation n).inv.app
          ((ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)) =
      (finiteDerivedPullback l E n f).map
          (((calculus l E Y).reductionEvaluation n).inv.app
            (DerivedCategory.Q.obj P.obj)) ≫
        (pullbackTensorDerivedEvaluation l E f n).inv.app
          ((calculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((model.reductionPull f).inv.app (DerivedCategory.Q.obj P.obj)) := by
  let K := DerivedCategory.Q.obj P.obj
  let a := (coefficientSequenceDerivedEvaluation l E X n).mapIso
    ((model.reductionPull f).app K)
  let b := (pullbackTensorDerivedEvaluation l E f n).app
    ((calculus l E Y).reduction.obj K)
  let c := (finiteDerivedPullback l E n f).mapIso
    (((calculus l E Y).reductionEvaluation n).app K)
  let d := ((calculus l E X).reductionEvaluation n).app ((ringedPull l E f).obj K)
  let e := (integralFiniteScalarPull l E f n).app K
  have h : a ≪≫ b ≪≫ c = d ≪≫ e := by
    apply Iso.ext
    exact integralReductionPullFiniteSquare l E o model f K n
  have hi := congrArg Iso.inv h
  simp only [Iso.trans_inv, a, b, c, d, e, Functor.mapIso_inv, Iso.app_inv] at hi
  rw [finiteScalarPullback_eq l E f n]
  simpa only [Category.assoc] using hi.symm

end WeilConjectures.IntegralSystemRealization
