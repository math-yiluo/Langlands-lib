/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteOperations
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Exceptional finite scalar operation core

Source: Zheng, Propositions 2.23 and 2.29; Stacks 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-operation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

private theorem compactComparison_eq
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    FiniteCompactScalar.compactRealizationIso A c =
      ProEtale.sfIntrinsicCompactSupportComparison A c := by
  unfold FiniteCompactScalar.compactRealizationIso
    ProEtale.sfIntrinsicCompactSupportComparison
    ProEtale.sfIntrinsicOpenExtensionComparison Equivalence.funInvIdAssoc
  rfl

private theorem supportComparison_app
    (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E.carrier n)) :
    (sfFiniteOperationsSupportComparison l E n c).app K =
      leftFixedIso (Padic.coefficientExtensionRing l E.carrier n) c K := by
  unfold leftFixedIso
  rw [compactComparison_eq]
  apply Iso.ext
  dsimp [sfFiniteOperationsSupportComparison, Iso.compInverseIso, Iso.inverseCompIso]
  dsimp [sfIntrinsicCompactSupport, sfAmbientCompactSupportCandidate]
  simp only [Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]

private theorem transportRightRealization_hom
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (e : D ≌ B) {F : C ⥤ B} {H : C ⥤ D} (r : F ⋙ e.inverse ≅ H)
    {K : B} (N : C) (v : K ⟶ F.obj N) :
    v ≫ (Iso.isoCompInverse (H := e.symm) r).hom.app N =
      (e.counitIso.app K).inv ≫ e.functor.map (e.inverse.map v ≫ r.hom.app N) := by
  dsimp only [Iso.isoCompInverse, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app]
  simp only [Category.id_comp, Functor.map_comp]
  change v ≫ (e.counitIso.app (F.obj N)).inv ≫ e.functor.map (r.hom.app N) = _
  have hc := e.counitIso.inv.naturality v
  change v ≫ (e.counitIso.app (F.obj N)).inv =
    (e.counitIso.app K).inv ≫ e.functor.map (e.inverse.map v) at hc
  rw [← Category.assoc, hc, Category.assoc]

/-- The normalized finite operation package. The former core omitted the relation
between its right realization and its adjunction, so could not support normalization.
Source: Zheng, Proposition 2.23; Stacks 09AL
(blueprint: lem-sf-exceptional-finite-scalar-operation-core). -/
abbrev OperationCore
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) := Operation l E n c

set_option maxRecDepth 4096 in
/-- Construction of the core from the existing finite exceptional operations theorem.
Retain its normalized Hom formula while transporting the right realization back
through the canonical coefficient equivalence and its counit.
(blueprint: lem-sf-exceptional-finite-scalar-operation-core) -/
theorem operationCore_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (OperationCore l E n c) := by
  classical
  let : c.Z.Over (Spec (.of D.k)) := ⟨c.g ≫ (Y ↘ Spec (.of D.k))⟩
  let : LocallyOfFiniteType (c.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of D.k))))
  let : QuasiCompact (c.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ (Y ↘ Spec (.of D.k))))
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.Z ↘ Spec (.of D.k))
  obtain ⟨_, _, h⟩ := exists_sfFiniteExceptionalOperations D l _hl f c d hd
  let E' : ConstructibleExceptionalCoefficients.FieldStage l := ⟨E⟩
  have hs := h E' ⟨n + 1, Nat.succ_pos n⟩
  dsimp only [E', PNat.mk_coe] at hs
  obtain ⟨F, G, eF, eG, _, _, sF, sG, adj, htriF, htriG, hunit, hcounit,
    hsG, rF, rG, hX, hY, hrF, hrG, hrFshift, hrGshift, horigin, hnorm, hbounds⟩ := hs
  clear htriF htriG hunit hcounit hsG hrG hrFshift hrGshift horigin hbounds sF sG
  subst rF
  let left := eqToIso eF
  let : F.CommShift ℤ := Functor.CommShift.ofComp left ℤ
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let EX := sfIntrinsicDerivedEquivalence X A
  let IX := (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι
  let IY := (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι
  let right' := Iso.isoCompInverse (G := G ⋙ IX) (H := EX.symm) rG
  let right : G ⋙ IX ≅ IY ⋙ exceptional A c := right'
  refine ⟨{
    F := F
    G := G
    left := left
    right := right
    adjunction := adj
    leftShift := Functor.CommShift.ofComp left ℤ
    rightShift := adj.rightAdjointCommShift ℤ
    unitShift := (adj.commShift_of_leftAdjoint ℤ).commShift_unit
    counitShift := (adj.commShift_of_leftAdjoint ℤ).commShift_counit
    leftShiftRealization := Functor.CommShift.ofComp_compatibility left ℤ
    normalized := ?_ }⟩
  intro hY' K N hK hN W v
  have hn := hnorm K N W v
  have hleft :
      (sfFiniteOperationsLeftRealization l ⟨E⟩ ⟨n + 1, Nat.succ_pos n⟩ c F eF).inv.app K =
        (leftFixedIso A c K.obj).inv ≫
          (sfIntrinsicDerivedEquivalence Y A).inverse.map (left.inv.app K) := by
    dsimp only [sfFiniteOperationsLeftRealization, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app,
      whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app]
    simp only [Category.id_comp, Category.comp_id]
    exact congrArg (fun t ↦ t ≫
      (sfIntrinsicDerivedEquivalence Y A).inverse.map (left.inv.app K))
      (congrArg Iso.inv (supportComparison_app l ⟨E⟩ ⟨n + 1, Nat.succ_pos n⟩ c K.obj))
  rw [hleft] at hn
  have hh := congrArg (fun t ↦ (EX.counitIso.app K.obj).inv ≫ EX.functor.map t) hn
  change IX.map (adj.homEquiv K N v) ≫
    (Iso.isoCompInverse (G := G ⋙ IX) (H := EX.symm) rG).hom.app N = _
  refine (transportRightRealization_hom EX (F := G ⋙ IX) rG N
    (IX.map (adj.homEquiv K N v))).trans ?_
  dsimp only [sfFiniteOperationsHomEquiv, sfFiniteOperationsRealization,
    Functor.comp_map, Functor.comp_obj] at hh
  simp only [Functor.map_comp, Category.assoc] at hh ⊢
  exact hh

/-- The normalized Hom formula for the core operation.
(blueprint: lem-sf-exceptional-finite-scalar-operation-normalization) -/
theorem operationCore_normalized
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (o : OperationCore l E n c) :
    ∀ (hY : CompactSpace Y)
      (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X)
      (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y)
      (hK : DerivedCategory.TStructure.t.plus
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj K.obj))
      (hN : DerivedCategory.TStructure.t.plus
        ((sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj N.obj))
      (W : X.FixedEtaleOriginWitness (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))) ⟨_, hK⟩)
      (v : o.F.obj K ⟶ N),
      (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι.map
          (o.adjunction.homEquiv K N v) ≫ o.right.hom.app N =
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).counitIso.app K.obj).inv ≫
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor.map
            (@ProEtale.specifiedExceptionalHomEquiv _ _ _ _ _ _ _ hY c
              (Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
                (ULift.{u + 1, u}
                  (Padic.coefficientExtensionRing l E (n + 1))) c)
              ⟨_, hK⟩ W ⟨_, hN⟩
              ((leftFixedIso (Padic.coefficientExtensionRing l E (n + 1)) c K.obj).inv ≫
                (sfIntrinsicDerivedEquivalence Y
                  (Padic.coefficientExtensionRing l E (n + 1))).inverse.map
                  (o.left.inv.app K ≫
                    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι.map v))) := by
  exact o.normalized

end WeilConjectures.ExceptionalFiniteScalar
