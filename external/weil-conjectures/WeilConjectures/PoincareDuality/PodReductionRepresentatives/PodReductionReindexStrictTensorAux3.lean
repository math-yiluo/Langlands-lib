/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensorAux
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed

/-! # The generator formula of the transported system tensor comparison

Source: Stacks 03EL and 07A4.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local semireducible] pullbackTensorSequenceRingMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example {X Y : Scheme.{u}} (g : X ⟶ Y) (M : coefficientSequenceModules l E Y) (U : (ℕ × X.ProEt)ᵒᵖ)
    (x : ((integralComparisonSequencePullback l E g).obj M).val.obj U) :
    (((eqToIso (inverse_eq l E g)).hom.app M).val.app U) x = x := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example {X Y : Scheme.{u}} (g : X ⟶ Y) (M : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : M.val.obj U) :
    ((pullbackTensorSequenceAdjunction l E g).unit.app M).val.app U x =
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app M).val.app
      U x := rfl

section TotalTensor

open MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Total-tensor generators are natural for restriction of sections.
Source: Stacks 03EK and 06YN. -/
theorem coefficientTensorGenerator_restrict
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (A : Sheaf J CommRingCat.{u + 1})
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ)
    (p q k : ℤ) (hpq : p + q = k) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{u, u + 1, u} J A).obj (P, Q)).X k).val.map i
        (coefficientTensorGenerator.{u, u + 1, u} J A P Q p q k hpq U x y) =
      coefficientTensorGenerator.{u, u + 1, u} J A P Q p q k hpq V
        ((P.X p).val.map i x) ((Q.X q).val.map i y) := by
  let : EssentiallySmall.{u + 1} C := essentiallySmallSelf.{0, u, u + 1} C
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} A
  let := SheafOfModules.monoidalCategory A
  open SheafOfModules in
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients.{u + 1, u, u + 1} A
  open SheafOfModules in
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u + 1, u, u + 1} A
  let ι := HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
    (.up ℤ) p q k hpq
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)
  let z := x ⊗ₜ[A.obj.obj U] y
  have hi := PresheafOfModules.naturality_apply ι.val i
    ((SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val.app U
      ((adj.unit.app ((P.X p).val ⊗ (Q.X q).val)).app U z))
  have ht := PresheafOfModules.naturality_apply
    (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val i
    ((adj.unit.app ((P.X p).val ⊗ (Q.X q).val)).app U z)
  have hu := PresheafOfModules.naturality_apply
    (adj.unit.app ((P.X p).val ⊗ (Q.X q).val)) i z
  dsimp only [Functor.id_obj] at hu
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at hu
  simp only [coefficientTotalTensor, coefficientTensorGenerator]
  with_unfolding_all
    exact (hi.symm.trans (congrArg (ι.val.app V)
      (ht.symm.trans (congrArg
        ((SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val.app V)
        hu.symm))))

end TotalTensor

-- The transported comparison is unfolded through two equality transports.
/-- The transported system tensor comparison sends the inverse-image unit of a pure tensor to
the tensor of the two inverse-image units.
Source: Stacks 03EL and 07A4. -/
theorem systemChain_generator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B : CochainComplex (coefficientSequenceModules l E Y) ℤ) (p q k : ℤ) (hpq : p + q = k)
    (V : ℕ × Y.ProEt) (x : (A.X p).val.obj (op V)) (y : (B.X q).val.obj (op V)) :
    (((systemChain l E g).hom.app (A, B)).f k).val.app
        (op ((pullbackTensorSequenceBase g).obj V))
      (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          (((coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y)).obj (A, B)).X k)).val.app (op V)
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) A B p q k hpq (op V) x y)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj A)
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj B)
        p q k hpq (op ((pullbackTensorSequenceBase g).obj V))
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          (A.X p)).val.app (op V) x)
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          (B.X q)).val.app (op V) y) := by
  have hc := (pullbackTensorSequenceCochain_existsUnique l E g).exists.choose_spec A B p q k hpq
    V x y
  unfold systemChain
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, HomologicalComplex.comp_f]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  let e := NatIso.mapHomologicalComplex (eqToIso (inverse_eq l E g)) (.up ℤ)
  have hm := coefficientTotalTensor_map_tensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    (e.hom.app A) (e.hom.app B) p q k hpq (op ((pullbackTensorSequenceBase g).obj V))
    (((pullbackTensorSequenceAdjunction l E g).unit.app (A.X p)).val.app (op V) x)
    (((pullbackTensorSequenceAdjunction l E g).unit.app (B.X q)).val.app (op V) y)
  exact (congrArg (fun z ↦ (((coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)).map
      ((NatIso.prod e e).hom.app (A, B))).f k).val.app
        (op ((pullbackTensorSequenceBase g).obj V)) z) hc).trans hm

end WeilConjectures.PodReductionRepresentatives
