/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientPullbackIso
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientComposition
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackCompositionLaws
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientTensorComposition

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-pullback-tensor-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

private theorem compositor_unit {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) (M : Modules ell E Z s) :
    ((adjunction ell E g s).comp (adjunction ell E f s)).unit.app M ≫
        (push ell E f s ⋙ push ell E g s).map ((comp ell E f g s).hom.app M) =
      (adjunction ell E (f ≫ g) s).unit.app M ≫
        (pushComp ell E f g s).hom.app ((pull ell E (f ≫ g) s).obj M) := by
  exact (unit_conjugateEquiv_symm (adjunction ell E (f ≫ g) s)
    ((adjunction ell E g s).comp (adjunction ell E f s))
    (pushComp ell E f g s).hom M).symm

private theorem compositor_generator {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ)
    (M : Modules ell E Z s) (U : Site Z s) (V : Site Y s) (W : Site X s)
    (p : V ⟶ (base g s).obj U) (q : W ⟶ (base f s).obj V)
    (m : M.val.obj (op U)) (a : (coefficients ell E Y s).obj.obj (op V))
    (b : (coefficients ell E X s).obj.obj (op W)) :
    ((comp ell E f g s).hom.app M).val.app (op W)
        (generator ell E f s ((pull ell E g s).obj M) V W q
          (generator ell E g s M U V p m a) b) =
      generator ell E (f ≫ g) s M U W
        (q ≫ (base f s).map p ≫ (baseComp f g s).inv.app U) m
        (scalar ell E f s V W q a * b) := by
  let : ∀ (T : Scheme.{t}) (P : Modules ell E T s)
      {U V : (Site T s)ᵒᵖ} (i : U ⟶ V),
      MulAction ((coefficients ell E T s).obj.obj V)
        ((ModuleCat.restrictScalars
          ((ring (topology T s) (coefficients ell E T s)).obj.map i).hom).obj
            (P.val.obj V)) :=
    fun _ P {_ _} _ ↦ (P.val.obj _).isModule.toDistribMulAction.toMulAction
  let LgM := (pull ell E g s).obj M
  let H := (pull ell E f s).obj LgM
  let N := (pull ell E (f ≫ g) s).obj M
  let c := (comp ell E f g s).hom.app M
  let ef := (adjunction ell E f s).unit.app LgM
  let eg := (adjunction ell E g s).unit.app M
  let eh := (adjunction ell E (f ≫ g) s).unit.app M
  have hu := congrArg (fun z ↦ z.val.app (op U) m) (compositor_unit ell E f g s M)
  have he : c.val.app (op ((base f s).obj ((base g s).obj U)))
      (ef.val.app (op ((base g s).obj U)) (eg.val.app (op U) m)) =
      N.val.map ((baseComp f g s).inv.app U).op (eh.val.app (op U) m) := by
    exact hu.trans ((pushComp_existsUnique ell E f g s).exists.choose_spec
      N U (eh.val.app (op U) m))
  let z : H.val.obj (op ((base f s).obj ((base g s).obj U))) :=
    ef.val.app (op ((base g s).obj U)) (eg.val.app (op U) m)
  let r := scalar ell E f s V W q a
  have hs : ef.val.app (op V) (a • LgM.val.map p.op (eg.val.app (op U) m)) =
      (ringComponent ell E f s (op V)).hom a •
        (show H.val.obj (op ((base f s).obj V)) from
          H.val.map ((base f s).map p).op z) := by
    calc
      _ = (ringComponent ell E f s (op V)).hom a •
          (show H.val.obj (op ((base f s).obj V)) from
            ef.val.app (op V) (LgM.val.map p.op (eg.val.app (op U) m))) :=
        (ef.val.app (op V)).hom.map_smul a _
      _ = _ := congrArg (fun y : H.val.obj (op ((base f s).obj V)) ↦
          (ringComponent ell E f s (op V)).hom a • y)
        (PresheafOfModules.naturality_apply ef.val p.op (eg.val.app (op U) m))
  have ht : H.val.map q.op
      ((ringComponent ell E f s (op V)).hom a •
        (show H.val.obj (op ((base f s).obj V)) from
          H.val.map ((base f s).map p).op z)) =
      r • H.val.map q.op (H.val.map ((base f s).map p).op z) :=
    H.val.map_smul q.op ((ringComponent ell E f s (op V)).hom a) _
  have hn : c.val.app (op W)
      (H.val.map q.op (H.val.map ((base f s).map p).op z)) =
      N.val.map q.op (N.val.map ((base f s).map p).op
        (c.val.app (op ((base f s).obj ((base g s).obj U))) z)) := by
    exact (PresheafOfModules.naturality_apply c.val q.op _).trans
      (congrArg (fun y ↦ N.val.map q.op y)
        (PresheafOfModules.naturality_apply c.val ((base f s).map p).op z))
  change c.val.app (op W)
      (b • H.val.map q.op
        (ef.val.app (op V) (a • LgM.val.map p.op (eg.val.app (op U) m)))) =
    (r * b) • N.val.map
      (q ≫ (base f s).map p ≫ (baseComp f g s).inv.app U).op (eh.val.app (op U) m)
  calc
    _ = c.val.app (op W)
        (b • H.val.map q.op ((ringComponent ell E f s (op V)).hom a •
          (show H.val.obj (op ((base f s).obj V)) from
            H.val.map ((base f s).map p).op z))) :=
      congrArg (fun y ↦ c.val.app (op W) (b • H.val.map q.op y)) hs
    _ = c.val.app (op W)
        (b • (r • H.val.map q.op (H.val.map ((base f s).map p).op z))) :=
      congrArg (fun y ↦ c.val.app (op W) (b • y)) ht
    _ = b • (r • c.val.app (op W)
        (H.val.map q.op (H.val.map ((base f s).map p).op z))) :=
      ((c.val.app (op W)).hom.map_smul b _).trans
        (congrArg (fun y ↦ b • y) ((c.val.app (op W)).hom.map_smul r _))
    _ = b • (r • N.val.map q.op (N.val.map ((base f s).map p).op
        (N.val.map ((baseComp f g s).inv.app U).op (eh.val.app (op U) m)))) := by
      rw [hn, he]
    _ = _ := by
      rw [smul_smul, mul_comm b]
      congr 1
      simp only [op_comp, PresheafOfModules.map_comp_apply]
      rfl

/-- Coherence of pullback composition with ordinary, chain and derived tensors.
Source: Stacks 03D3, 03CB, 03EL, 07A4, 0G7E and 04VG
(blueprint: lem-sf-ambient-pullback-tensor-coherence).

Proof:
The three selected tensor bundles satisfy Normalized by tensorData_existsUnique.
The coefficient maps are invertible by coefficientPullback_isIso, and their
composition equation is ringMap_composition. The adjunction unit equation is
unit_conjugateEquiv_symm for the chosen pushforward comparison. Evaluating this
equation on a section gives its value on an iterated unit. Semilinearity of the
first unit, naturality of both units and of the compositor, and commutativity of
the coefficient ring then give the displayed formula on two scalar generators.
Apply normalizedTensor_composition to these normalized bundles and this formula
for the ordinary, chain and derived squares. Finally pullback_compositionLaws
supplies the independent associativity and identity laws. The calculations are
on the whole ringed sequence site, without an assumption on module transitions. -/
theorem ambientPullbackTensorCoherence
    (k₀ k : Type t) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]
    (_hell : ell ≠ ringChar k) {X Y Z : Scheme.{t}}
    (aX : X ⟶ Spec (CommRingCat.of k)) (aY : Y ⟶ Spec (CommRingCat.of k))
    (aZ : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (f : X ⟶ Y) (g : Y ⟶ Z) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY) (s : Option ℕ)
    (A : Tensor ell E Z s) (B : Tensor ell E Y s) (C : Tensor ell E X s)
    (TA : TensorModels ell E Z s A) (TB : TensorModels ell E Y s B)
    (TC : TensorModels ell E X s C) :
    CompositionLaws ell E (Spec (CommRingCat.of k)) s ∧
    (IsIso (ringMap ell E f s) ∧ IsIso (ringMap ell E g s) ∧
      IsIso (ringMap ell E (f ≫ g) s)) ∧
    (ringMap ell E (f ≫ g) s =
      (ringComp f g s).hom.app (coefficients ell E Z s) ≫
        (ringPull f s).map (ringMap ell E g s) ≫ ringMap ell E f s) ∧
    ((tensorData ell E f s B C TB TC).Normalized ell E f s B C TB TC ∧
      (tensorData ell E g s A B TA TB).Normalized ell E g s A B TA TB ∧
      (tensorData ell E (f ≫ g) s A C TA TC).Normalized ell E (f ≫ g) s A C TA TC) ∧
    (∀ M : Modules ell E Z s,
      ((adjunction ell E g s).comp (adjunction ell E f s)).unit.app M ≫
          (push ell E f s ⋙ push ell E g s).map ((comp ell E f g s).hom.app M) =
        (adjunction ell E (f ≫ g) s).unit.app M ≫
          (pushComp ell E f g s).hom.app ((pull ell E (f ≫ g) s).obj M)) ∧
    (∀ (M : Modules ell E Z s) (U : Site Z s) (V : Site Y s) (W : Site X s)
      (p : V ⟶ (base g s).obj U) (q : W ⟶ (base f s).obj V)
      (m : M.val.obj (op U)) (a : (coefficients ell E Y s).obj.obj (op V))
      (b : (coefficients ell E X s).obj.obj (op W)),
      ((comp ell E f g s).hom.app M).val.app (op W)
          (generator ell E f s ((pull ell E g s).obj M) V W q
            (generator ell E g s M U V p m a) b) =
        generator ell E (f ≫ g) s M U W
          (q ≫ (base f s).map p ≫ (baseComp f g s).inv.app U) m
          (scalar ell E f s V W q a * b)) ∧
    (∀ (M N : Modules ell E Z s),
      (pull ell E f s).map ((tensorData ell E g s A B TA TB).model.ordinary M N).hom ≫
          ((tensorData ell E f s B C TB TC).model.ordinary
            ((pull ell E g s).obj M) ((pull ell E g s).obj N)).hom ≫
          tensorHom ell E X s ((comp ell E f g s).hom.app M)
            ((comp ell E f g s).hom.app N) =
        (comp ell E f g s).hom.app (tensor ell E Z s M N) ≫
          ((tensorData ell E (f ≫ g) s A C TA TC).model.ordinary M N).hom) ∧
    (∀ P Q : CochainComplex (Modules ell E Z s) ℤ,
      FlatRepresentative ell E Z s P → FlatRepresentative ell E Z s Q →
      (total ell E X s).map (Prod.mkHom (chainComp ell E f g s P)
          (chainComp ell E f g s Q)) ≫
          (tensorData ell E (f ≫ g) s A C TA TC).model.chain P Q =
        (tensorData ell E f s B C TB TC).model.chain
            (((pull ell E g s).mapHomologicalComplex (.up ℤ)).obj P)
            (((pull ell E g s).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          ((pull ell E f s).mapHomologicalComplex (.up ℤ)).map
            ((tensorData ell E g s A B TA TB).model.chain P Q) ≫
          chainComp ell E f g s ((total ell E Z s).obj (P, Q))) ∧
    ∀ F G : Derived ell E Z s,
      (derivedPull ell E f s).map ((tensorData ell E g s A B TA TB).mu.hom.app (F, G)) ≫
          (tensorData ell E f s B C TB TC).mu.hom.app
            ((derivedPull ell E g s).obj F, (derivedPull ell E g s).obj G) ≫
          C.tensor.map (Prod.mkHom ((derivedComp ell E f g s).hom.app F)
            ((derivedComp ell E f g s).hom.app G)) =
        (derivedComp ell E f g s).hom.app (A.tensor.obj (F, G)) ≫
          (tensorData ell E (f ≫ g) s A C TA TC).mu.hom.app (F, G) := by
  have hf := (tensorData_existsUnique ell E f s B C TB TC).exists.choose_spec
  have hg := (tensorData_existsUnique ell E g s A B TA TB).exists.choose_spec
  have hfg := (tensorData_existsUnique ell E (f ≫ g) s A C TA TC).exists.choose_spec
  obtain ⟨ho, hc, hd⟩ := normalizedTensor_composition ell E f g s A B C TA TB TC
    (tensorData ell E f s B C TB TC) (tensorData ell E g s A B TA TB)
    (tensorData ell E (f ≫ g) s A C TA TC) hf hg hfg
    (compositor_generator ell E f g s)
  exact ⟨pullback_compositionLaws ell E _ s,
    ⟨coefficientPullback_isIso ell E f s, coefficientPullback_isIso ell E g s,
      coefficientPullback_isIso ell E (f ≫ g) s⟩,
    ringMap_composition ell E f g s, ⟨hf, hg, hfg⟩,
    compositor_unit ell E f g s, compositor_generator ell E f g s, ho, hc, hd⟩

end WeilConjectures.AmbientPullbackTensor
