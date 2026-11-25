/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctorData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicFiniteCocone
import all WeilConjectures.SmoothPurity.Sf.SfFrameworkCommonStageDescent
import all WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.CategoryTheory.StageSystem.Exact

/-! # LocallyFiniteAdicNormalizedFunctor
Source: Bhatt--Scholze, Section 6.8; native realization proof
(blueprint: lem-sf-locally-finite-adic-normalized-functor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison WeilConjectures.pairShiftIso
  WeilConjectures.pairStageShiftIso

section ConstantEvaluation

universe w a b

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {D : Type a} [Category.{b} D] [HasShift D ℤ]

@[instance_reducible] private instance constTransitionShift {i j : I} (h : i ≤ j) :
    ((StageSystem.const I D).T h).CommShift ℤ :=
  inferInstanceAs ((𝟭 D).CommShift ℤ)

private instance constAssocShift {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    NatTrans.CommShift ((StageSystem.const I D).assoc h h').hom ℤ := by
  exact inferInstanceAs (NatTrans.CommShift (Functor.leftUnitor (𝟭 D)).hom ℤ)

@[instance_reducible] private def constantEvalShift :
    (StageSystem.constEval (I := I) (D := D)).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B f
    induction f using StageSystem.PairCategory.hom_induction with
    | h m hA hB u =>
      change StageSystem.constEval.map
          ((shiftFunctor (StageSystem.const I D).PairCategory n).map
            (StageSystem.PairCategory.mkHom m hA hB u)) ≫ 𝟙 _ =
        𝟙 _ ≫ (shiftFunctor D n).map u
      erw [Category.comp_id, Category.id_comp,
        StageSystem.PairCategory.shiftFunctor_map_mkHom]
      erw [StageSystem.constEval_map_mkHom]
      change ((𝟭 D).commShiftIso n).hom.app A.obj ≫ (shiftFunctor D n).map u ≫
        ((𝟭 D).commShiftIso n).inv.app B.obj = _
      simp only [Functor.commShiftIso_id_hom_app, Functor.commShiftIso_id_inv_app,
        Category.id_comp, Category.comp_id]
      erw [Category.id_comp, Category.comp_id]
      rfl)
  commShiftIso_zero := by
    ext A
    erw [Functor.CommShift.isoZero_hom_app]
    change 𝟙 _ =
      StageSystem.constEval.map
          ((StageSystem.const I D).ι A.stage |>.map
            ((shiftFunctorZero D ℤ).hom.app A.obj)) ≫
        (shiftFunctorZero D ℤ).inv.app A.obj
    change 𝟙 _ = (shiftFunctorZero D ℤ).hom.app A.obj ≫
      (shiftFunctorZero D ℤ).inv.app A.obj
    simp
  commShiftIso_add n m := by
    ext A
    erw [Functor.CommShift.isoAdd_hom_app]
    change 𝟙 _ = (shiftFunctorAdd D n m).hom.app A.obj ≫
      𝟙 _ ≫ (shiftFunctor D m).map (𝟙 _) ≫ (shiftFunctorAdd D n m).inv.app A.obj
    simp

end ConstantEvaluation

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

-- Transport the actual chosen pair shift; a different canonical shift would not suffice.
private theorem coconeShift (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (abRing l X)] [(sections l X).Additive]
    [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
    (C : CoefficientSystem l X) (A : FiniteCocone l X C) :
    letI : ∀ E, (A.Φ E).CommShift ℤ := A.shift
    ∃ s : (StageSystem.descFunctor A.Φ A.ι A.coherence).CommShift ℤ,
      (fun [hs : (StageSystem.descFunctor A.Φ A.ι A.coherence).CommShift ℤ] ↦
        ∀ E : Index l (PadicAlgCl l),
          NatTrans.CommShift
            (StageSystem.ιCompDescFunctorIso A.Φ A.ι A.coherence E).hom ℤ) (hs := s) := by
  letI : ∀ E, (A.Φ E).CommShift ℤ := A.shift
  letI : ∀ {E L} (h : E ≤ L), NatTrans.CommShift (A.ι h).hom ℤ := A.transitionShift
  letI : ∀ E, ((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).Φ E).CommShift ℤ := A.shift
  have hβ : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
      NatTrans.CommShift ((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).β h).hom ℤ := by
    intro E L h
    have hi : NatTrans.CommShift
        ((Functor.rightUnitor (A.Φ E)).hom ≫ (A.ι h).inv) ℤ := inferInstance
    convert hi using 1 <;> first
    | rfl
    | apply heq_of_eq; ext K; simp <;> rfl
  letI : ∀ {i j : Index l (PadicAlgCl l)} (h : i ≤ j),
      NatTrans.CommShift
        ((StageSystem.const (Index l (PadicAlgCl l))
          (DerivedCategory (ProEtale.AdicSheaf l X))).transIso h).hom ℤ :=
    fun {_ _} h ↦ StageSystem.transIso_commShift h
  letI := WeilConjectures.pairCommShift (StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence) hβ
  letI : (StageSystem.constEval (I := Index l (PadicAlgCl l))
      (D := DerivedCategory (ProEtale.AdicSheaf l X))).CommShift ℤ := constantEvalShift
  letI : (StageSystem.descFunctor A.Φ A.ι A.coherence).CommShift ℤ :=
    Functor.CommShift.comp
      (StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).functor StageSystem.constEval
  refine ⟨inferInstance, ?_⟩
  intro E
  apply NatTrans.CommShift.mk
  intro n
  ext K
  change ((GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
      StageSystem.descFunctor A.Φ A.ι A.coherence).commShiftIso n).hom.app K ≫
        (shiftFunctor (DerivedCategory (ProEtale.AdicSheaf l X)) n).map (𝟙 _) =
      𝟙 _ ≫ ((A.Φ E).commShiftIso n).hom.app K
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  erw [CategoryTheory.Functor.commShiftIso_comp_hom_app]
  change ((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).functor ⋙
      StageSystem.constEval).map
        (((GeneralAlgebraicallyClosedCoefficients.inclusion E).commShiftIso n).hom.app K) ≫
      (((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).functor ⋙
        StageSystem.constEval).commShiftIso n).hom.app ⟨E, K⟩ = _
  erw [CategoryTheory.Functor.commShiftIso_comp_hom_app]
  change ((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).functor ⋙ StageSystem.constEval).map
        (((GeneralAlgebraicallyClosedCoefficients.inclusion E).commShiftIso n).hom.app K) ≫
      StageSystem.constEval.map ((WeilConjectures.pairShiftIso
    (StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence) hβ n).hom.app ⟨E, K⟩) ≫
        𝟙 _ = ((A.Φ E).commShiftIso n).hom.app K
  erw [WeilConjectures.pairShiftIso_hom_app]
  erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  change StageSystem.constEval.map ((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).functor.map
        (((GeneralAlgebraicallyClosedCoefficients.inclusion E).commShiftIso n).hom.app K)) ≫
      StageSystem.constEval.map ((StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence).functor.map
        (((GeneralAlgebraicallyClosedCoefficients.inclusion E).commShiftIso n).inv.app K)) ≫
        ((A.Φ E).commShiftIso n).hom.app K ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  erw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- Construct the normalized triangulated functor, without asserting descent on Homs,
its essential image, or smallness.
Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), Proposition 6.8.14(2)
and Remark 6.8.15; steps 2--5 of the native realization proof
(blueprint: lem-sf-locally-finite-adic-normalized-functor).
Proof in words: identify the native coefficient with the sheafification of continuous
functions valued in a finite extension. A finite-dimensional span is contained in the
field generated by a finite basis, and each finite field has finite dimension, so the
locally finite and finite-field-local descriptions coincide. The function coefficient
comparison respects constants, restrictions, and every finite-field inclusion. Use the
finite-level continuous coefficient realizations and inverse-limit residue maps to
construct each CoefficientPresentation, then localize at the uniformizer. Equality of
structural maps is checked on integral residues and after the specified field inclusion.
The unit axiom identifies native internal modules with modules in abelian sheaves;
apply the section-module equivalence and the ring-isomorphism scalar comparison.
Their additive equivalences preserve kernels and cokernels, hence induce exact derived
functors. At each finite field use continuous_rational_derived_realization and the
integral-stratified-perfect characterization. The identity equivalences of the two raw
rationalizations identify their integral localizations and inverse completion maps.
Extend these finite-stage functors to the native coefficient. Scalar coherence and
balanced tensor transitivity flatten b tensor (e tensor k) to be tensor k, with inverse
inserting one. These maps obey the unit and successive-extension associator equations,
including ramified extension. They give a functor on pairs: realize an arrow at a common
field and use this coherence to prove independence of representatives, identities and
composition. The same functor takes an inverse uniformizer power to its inverse, so the
integral comparison is natural on all numerator maps and respects fractions. Triangles
and shifts are represented at finite stage, where exact derived scalar extension
preserves them. Finally the completion-chain comparison followed by this same balanced
associator is the prescribed common_field equation, with the literal object transports
retained. This construction does not use full faithfulness, essential surjectivity, or
smallness. On the empty scheme all maps and tensor formulas use the zero coefficient.
-/
theorem normalizedFunctor_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    Nonempty (NormalizedFunctor l X) := by
  obtain ⟨C⟩ := coefficientSystem_exists l X
  letI := C.commutative
  letI := C.sectionsAdditive
  letI := C.sectionsLimits
  letI := C.sectionsColimits
  obtain ⟨A⟩ := finiteCocone_exists l X C
  letI : ∀ E, (A.Φ E).Additive := A.additive
  letI : ∀ E, (A.Φ E).CommShift ℤ := A.shift
  letI : ∀ {E L} (h : E ≤ L), NatTrans.CommShift (A.ι h).hom ℤ := A.transitionShift
  let J := StageSystem.descFunctor A.Φ A.ι A.coherence
  haveI : J.Additive := by
    constructor
    intro K L f g
    obtain ⟨M, _, hK, hL, hK', hL', u, v, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage f g K.stage
    rw [GeneralAlgebraicallyClosedCoefficients.mkHom_add]
    simp only [J, StageSystem.descFunctor_map_mkHom, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp]
    rfl
  obtain ⟨s, hs⟩ := coconeShift l X C A
  letI : J.CommShift ℤ := s
  haveI (E : Index l (PadicAlgCl l)) :
      NatTrans.CommShift (StageSystem.ιCompDescFunctorIso A.Φ A.ι A.coherence E).hom ℤ := hs E
  have ht : J.IsTriangulated := by
    constructor
    intro T hT
    obtain ⟨E, V, hV, ⟨e⟩⟩ :=
      (GeneralAlgebraicallyClosedCoefficients.distinguished_iff T).mp hT
    haveI : (A.Φ E).IsTriangulated := A.triangulated E
    haveI : (GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ J).IsTriangulated :=
      Functor.isTriangulated_of_iso
        (StageSystem.ιCompDescFunctorIso A.Φ A.ι A.coherence E).symm
    exact Pretriangulated.isomorphic_distinguished _
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ J).map_distinguished V hV) _
      (J.mapTriangle.mapIso e ≪≫
        (Functor.mapTriangleCompIso (GeneralAlgebraicallyClosedCoefficients.inclusion E)
          J).symm.app V)
  set_option backward.isDefEq.respectTransparency false in
  let integral (E : Index l (PadicAlgCl l)) :
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          J ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend ((C.coefficient E).integralMap l X) :=
    NatIso.ofComponents (fun K ↦ (A.integral E).app K) (by
      intro K L f
      change (sections l X).mapDerivedCategory.map
          (J.map (((GeneralAlgebraicallyClosedCoefficients.stageSystem l
            (PadicAlgCl l) X).ι E).map
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).map f))) ≫
          (A.integral E).hom.app L = _
      erw [StageSystem.descFunctor_map_ι]
      exact (A.integral E).hom.naturality f)
  have hi (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E) :
      J.map ((StageSystem.isoToStage
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
        ⟨E, K⟩ h).hom) = (A.ι h).inv.app K := by
    let F := StageSystem.Morphism.ofCocone A.Φ A.ι A.coherence
    have he : J.mapIso
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).transIso
          h).app K) = (A.ι h).app K := by
      apply Iso.ext
      dsimp only [J, StageSystem.descFunctor, Functor.mapIso_hom, Iso.app_hom,
        Functor.comp_map]
      change StageSystem.constEval.map (F.functor.map _) = _
      rw [WeilConjectures.pairFunctor_transIso]
      erw [Functor.map_comp]
      change (A.ι h).hom.app K ≫ 𝟙 _ = _
      exact Category.comp_id _
    exact congrArg Iso.inv he
  refine ⟨{
    toFunctorData := {
      commutative := C.commutative
      sectionsAdditive := C.sectionsAdditive
      sectionsLimits := C.sectionsLimits
      sectionsColimits := C.sectionsColimits
      coefficient := C.coefficient
      coefficient_scalar := C.coefficient_scalar
      J := J
      additive := inferInstance
      shift := s
      triangulated := ht
      integral := integral
    }
    common_field := ?_
  }⟩
  intro E L h K
  dsimp only
  have hn := A.normalization
  unfold FiniteCoconeData.normalized at hn
  have he := congrArg (fun f ↦ (sections l X).mapDerivedCategory.map f)
    (hi E L h ((sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))
  exact (heq_of_eq he).trans (hn E L h K)

end WeilConjectures.LocallyFiniteAdicRealization
