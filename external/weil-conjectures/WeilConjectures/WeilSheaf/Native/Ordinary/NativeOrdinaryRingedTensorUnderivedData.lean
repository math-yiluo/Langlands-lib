/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData

/-! # Underived data for normalized ordinary ringed tensor comparisons

This is the underived and evaluation-normalized part of the normalized complex
comparison.  It is separated so that the total-complex and localization clauses
can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)

abbrev nativeOrdinaryRingedTensorObj (P Q : ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (SheafOfModules.monoidalCategory b.Q).tensorObj (b.ordinary.functor.obj Q)
    (b.ordinary.functor.obj P)

/-- The underived comparison and its evaluation normalization.
Source: Stacks 06YS and 06YU (blueprint: new-sf-native-ordinary-ringed-tensor-underived-data). -/
abbrev NativeOrdinaryRingedTensorUnderivedData :=
  OrdinaryRingedTensorUnderivedData l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    b.K b.Q b.ordinary b.ordinaryHom

set_option linter.unusedSectionVars false in
/-- The underived comparison fixed by the ordinary and ringed tensor-Hom adjunctions.
Source: Stacks 06YS and 06YU; the uniqueness-of-left-adjoints step in the native
tensor model proof (blueprint: new-sf-native-ordinary-ringed-tensor-underived-data).

Proof: transport the ordinary parameter adjunction through the additive equivalence
`b.ordinary`, compare its right adjoint with the sheaf tensor-Hom adjunction by
`b.ordinaryHom`, and use uniqueness of left adjoints.  The counit identity is the
displayed uncurrying equation; naturality in the parameter gives the required
two-variable comparison.  The construction is independent of all derived data.
Its normalization determines
this isomorphism uniquely: specialize to the adjunct of the identity to recover
its inverse.  Thus this existence theorem specifies actual comparison data.
-/
theorem native_ordinary_ringed_tensor_underived_data :
    Nonempty (NativeOrdinaryRingedTensorUnderivedData b) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
  let := SheafOfModules.monoidalCategory b.Q
  let := SheafOfModules.symmetricCategory b.Q
  let h (P Q I : ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
      (((ordinaryTensorBifunctor l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj P).obj Q ⟶ I) ≃
        (nativeOrdinaryRingedTensorObj b P Q ⟶ b.ordinary.functor.obj I) :=
    (((((Mod.ihomAdjunction P).homEquiv Q I).trans b.ordinary.fullyFaithfulFunctor.homEquiv).trans
      (b.ordinaryHom.app (op P, I)).homToEquiv).trans
        ((SheafOfModules.tensorHomAdjunction b.Q
          (b.ordinary.functor.obj P)).homEquiv
            (b.ordinary.functor.obj Q) (b.ordinary.functor.obj I)).symm).trans
      (β_ (b.ordinary.functor.obj Q) (b.ordinary.functor.obj P)).symm.homFromEquiv
  have h_apply (P Q I : ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (f : ((ordinaryTensorBifunctor l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj P).obj Q ⟶ I) :
      h P Q I f = (β_ (b.ordinary.functor.obj Q) (b.ordinary.functor.obj P)).hom ≫
        ((SheafOfModules.tensorHomAdjunction b.Q (b.ordinary.functor.obj P)).homEquiv
          (b.ordinary.functor.obj Q) (b.ordinary.functor.obj I)).symm
            (b.ordinary.functor.map ((Mod.ihomAdjunction P).homEquiv Q I f) ≫
              b.ordinaryHom.hom.app (op P, I)) := rfl
  have hn (P Q I I' : ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (f : ((ordinaryTensorBifunctor l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj P).obj Q ⟶ I) (g : I ⟶ I') :
      h P Q I' (f ≫ g) = h P Q I f ≫ b.ordinary.functor.map g := by
    have nh := b.ordinaryHom.hom.naturality
      (show (op P, I) ⟶ (op P, I') from (𝟙 _, g))
    dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
      Functor.op_map] at nh
    simp only [unop_id, CategoryTheory.Functor.map_id, op_id, NatTrans.id_app,
      Category.id_comp] at nh
    erw [(SheafOfModules.homFunctor b.Q).map_id, NatTrans.id_app,
      Category.id_comp] at nh
    dsimp only [Functor.prod_obj, Functor.op_obj] at nh
    change b.ordinary.functor.map ((Mod.ihom P).map g) ≫
        b.ordinaryHom.hom.app (op P, I') =
      b.ordinaryHom.hom.app (op P, I) ≫
        ((SheafOfModules.homFunctor b.Q).obj (op (b.ordinary.functor.obj P))).map
          (b.ordinary.functor.map g) at nh
    rw [h_apply, h_apply, Adjunction.homEquiv_naturality_right, Functor.map_comp,
      Category.assoc, nh, ← Category.assoc]
    have nt := (SheafOfModules.tensorHomAdjunction b.Q
      (b.ordinary.functor.obj P)).homEquiv_naturality_right_symm
        (b.ordinary.functor.map ((Mod.ihomAdjunction P).homEquiv Q I f) ≫
          b.ordinaryHom.hom.app (op P, I)) (b.ordinary.functor.map g)
    simpa only [Category.assoc, Functor.prod_obj, nativeOrdinaryRingedTensorObj] using
      congrArg ((β_ (b.ordinary.functor.obj Q) (b.ordinary.functor.obj P)).hom ≫ ·) nt
  have he (P Q : ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    iso_of_natural_hom_equiv b.ordinary (((ordinaryTensorBifunctor l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj P).obj Q)
      (nativeOrdinaryRingedTensorObj b P Q) (h P Q) (hn P Q)
  refine ⟨{ underived := fun P Q ↦ (he P Q).choose, uncurry := ?_ }⟩
  intro P Q I f
  rw [(he P Q).choose_spec I (((Mod.ihomAdjunction P).homEquiv Q I).symm f)]
  rw [h_apply, Equiv.apply_symm_apply]

end AlgebraicGeometry.ProEtaleWeilSheaf
