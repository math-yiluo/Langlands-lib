/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.RoosShift.RoosCommShift
import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift

/-! # Signed shifts of the completed scalar Roos complex

Source: Stacks Project, Tags 011G, 014E, 06YS, 06YT and 08TC.
(blueprint: lem-weil-completed-scalar-chain-shift)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite
private def zeroDifferentialFunctor (A : Type a) [Category.{b} A] [Preadditive A] :
    A ⥤ CochainComplex A ℤ where
  obj M :=
    { X := fun _ ↦ M
      d := fun _ _ ↦ 0
      shape := fun _ _ _ ↦ rfl
      d_comp_d' := fun _ _ _ _ _ ↦ CategoryTheory.Limits.zero_comp }
  map f :=
    { f := fun _ ↦ f
      comm' := by intros; simp }
  map_id _ := rfl
  map_comp _ _ := rfl
private theorem mapHC_commShift {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] (F G : A ⥤ B) [F.Additive] [G.Additive]
    (α : F ⟶ G) : NatTrans.CommShift (NatTrans.mapHomologicalComplex α (.up ℤ)) ℤ := by
  constructor
  intro m
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctor_map_f', Category.id_comp, Category.comp_id]
  rfl

private theorem comp_mapCochainShiftIso {A B C : Type*} [Category A] [Category B]
    [Category C] [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (P : CochainComplex A ℤ) (m : ℤ) :
    (((F ⋙ G).mapCochainComplexShiftIso m).app P) =
      (G.mapHomologicalComplex (.up ℤ)).mapIso
        ((F.mapCochainComplexShiftIso m).app P) ≪≫
        ((G.mapCochainComplexShiftIso m).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro i
  change 𝟙 _ = G.map (𝟙 _) ≫ 𝟙 _
  rw [G.map_id]
  exact (Category.id_comp _).symm

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

attribute [local irreducible] integralScalarReduction completedScalarChangeData
  completedDerivedScalarExtension completedIntegralCoefficientSheafUnrestricted

private noncomputable abbrev moduleLevel (n : ℕ) :
    integralTowerModules l E Y ⥤ integralTowerModules l L Y :=
  integralScalarReduction l E L ι Y n ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))
private instance (n : ℕ) : (moduleLevel l E L ι Y n).Additive := by
  unfold moduleLevel
  infer_instance
private noncomputable abbrev levelView (n : ℕ) :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l L Y) ℤ :=
  RoosShift.levelFunctor (integralScalarTowerFunctor l E L ι Y) n

private noncomputable abbrev transitionView (n : ℕ) :
    levelView l E L ι Y (n + 1) ⟶ levelView l E L ι Y n :=
  integralScalarTransition l E L ι Y n

private noncomputable def moduleTransition (n : ℕ) :
    moduleLevel l E L ι Y (n + 1) ⟶ moduleLevel l E L ι Y n where
  app M := ((integralScalarTransition l E L ι Y n).app
    ((zeroDifferentialFunctor _).obj M)).f 0
  naturality := by
    intro M N f
    exact congrArg (fun g ↦ g.f 0) ((integralScalarTransition l E L ι Y n).naturality
      ((zeroDifferentialFunctor _).map f))
attribute [local irreducible] moduleTransition
private noncomputable def degreewiseTransition (n : ℕ) :
    levelView l E L ι Y (n + 1) ⟶ levelView l E L ι Y n :=
  NatTrans.mapHomologicalComplex (moduleTransition l E L ι Y n) (.up ℤ)

private theorem transition_eq (n : ℕ) :
    integralScalarTransition l E L ι Y n =
      degreewiseTransition l E L ι Y n := by
  apply ((integralScalarTransition_existsUnique l E L ι Y n).unique
    ((integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec) _)
  intro P i U s x
  unfold degreewiseTransition moduleTransition
  exact (integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec
    ((zeroDifferentialFunctor _).obj (P.X i)) 0 U s x
private noncomputable instance levelCommShift (n : ℕ) :
    (levelView l E L ι Y n).CommShift ℤ := by
  change ((moduleLevel l E L ι Y n).mapHomologicalComplex (.up ℤ)).CommShift ℤ
  infer_instance
private theorem levelShift_f (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (m : ℤ) (n : ℕ) (i : ℤ) :
    (((levelView l E L ι Y n).commShiftIso m).hom.app P).f i =
      𝟙 ((moduleLevel l E L ι Y n).obj (P.X (i + m))) := by
  rfl

private theorem levelShift_iso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) (n : ℕ) :
    ((levelView l E L ι Y n).commShiftIso m).app P =
      (integralOperationsRestrict l L Y n).mapIso
        (((integralScalarReduction l E L ι Y n).mapCochainComplexShiftIso m).app P) ≪≫
        ((SheafOfModules.restrictScalars
          ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (completedIntegralCommRingProjectionUnrestricted l L Y n))).mapCochainComplexShiftIso
                m).app ((integralScalarFiniteComplex l E L ι Y n).obj P) := by
  exact comp_mapCochainShiftIso (integralScalarReduction l E L ι Y n)
    (SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))) P m

private theorem transition_commShift (n : ℕ) :
    NatTrans.CommShift (transitionView l E L ι Y n) ℤ := by
  rw [show transitionView l E L ι Y n = degreewiseTransition l E L ι Y n from
    transition_eq l E L ι Y n]
  exact mapHC_commShift (moduleLevel l E L ι Y (n + 1))
    (moduleLevel l E L ι Y n) (moduleTransition l E L ι Y n)

private theorem nativeTransition_eq (n : ℕ) :
    RoosShift.transition (integralScalarTowerFunctor l E L ι Y) n =
      transitionView l E L ι Y n := by
  ext P
  simp only [RoosShift.transition, integralScalarTowerFunctor,
    Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ, transitionView]

private instance nativeTransition_commShift (n : ℕ) :
    NatTrans.CommShift (RoosShift.transition (integralScalarTowerFunctor l E L ι Y) n) ℤ := by
  rw [nativeTransition_eq]
  exact transition_commShift l E L ι Y n

private noncomputable instance scalarCoconeShift :
    (integralScalarComplexFunctor l E L ι Y).CommShift ℤ :=
  RoosShift.commShift (integralScalarTowerFunctor l E L ι Y)

private theorem scalarHom_ext (M : integralTowerModules l E Y)
    (N : integralTowerModules l L Y)
    (a b : (completedOrdinaryScalarExtension l E L ι Y).obj M ⟶ N)
    (h : ∀ U s x, a.val.app U (completedScalarTensorSection l E L ι Y M U s x) =
      b.val.app U (completedScalarTensorSection l E L ι Y M U s x)) : a = b := by
  let e := eqToIso ((completedScalarChangeData l E L ι Y).choose_spec.choose M)
  apply (cancel_epi e.inv).mp
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul t x => exact h U t x
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
attribute [local irreducible] completedOrdinaryScalarExtension completedScalarTensorSection
  completedScalarChainComparison

private theorem chainComparison_tensor
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
    (U : Y.ProEtᵒᵖ) (t : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : (P.X i).val.obj U) :
    ((((completedScalarChainComparison l E L ι Y).app P).f i ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
      (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i).val.app U)
        (completedScalarTensorSection l E L ι Y (P.X i) U t x) =
      integralScalarTensorSection l E L ι Y n (P.X i) U
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U t) x := by
  unfold completedScalarChainComparison
  exact (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.1
    P i n U t x

private theorem chainComparison_zeroSecond
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (j : ℤ) :
    ((completedScalarChainComparison l E L ι Y).app P).f j ≫
      (CochainComplex.mappingCocone.snd
        (completedScalarRoosEndomorphism l E L ι Y P)).v j (j - 1) (by omega) = 0 := by
  unfold completedScalarChainComparison
  exact (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.2 P j

private theorem chainFirst_degreewise
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ) :
    ((completedScalarChainComparison l E L ι Y).app P).f i ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
      (Limits.Pi.π
        (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i =
    ((completedScalarChainComparison l E L ι Y).app
      ((zeroDifferentialFunctor _).obj (P.X i))).f 0 ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y
          ((zeroDifferentialFunctor _).obj (P.X i)))).f 0 ≫
      (Limits.Pi.π
        (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj
          ((zeroDifferentialFunctor _).obj (P.X i))).obj (op n)) n).f 0 := by
  apply scalarHom_ext
  intro U t x
  exact (chainComparison_tensor l E L ι Y P i n U t x).trans
    (chainComparison_tensor l E L ι Y
      ((zeroDifferentialFunctor _).obj (P.X i)) 0 n U t x).symm

private theorem chainFirst_shift
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) (n : ℕ) :
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        (((completedScalarChainComparison l E L ι Y).app P) ≫
          CochainComplex.mappingCocone.fst (completedScalarRoosEndomorphism l E L ι Y P) ≫
          Limits.Pi.π (fun n ↦ (levelView l E L ι Y n).obj P) n)⟦m⟧' =
      (completedScalarChainComparison l E L ι Y).app (P⟦m⟧) ≫
        CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧)) ≫
        Limits.Pi.π (fun n ↦ (levelView l E L ι Y n).obj (P⟦m⟧)) n ≫
        ((levelView l E L ι Y n).commShiftIso m).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    levelShift_f]
  exact (chainFirst_degreewise l E L ι Y P (i + m) n).trans
    (chainFirst_degreewise l E L ι Y (P⟦m⟧) i n).symm

private theorem chainFirstProduct_shift
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        (((completedScalarChainComparison l E L ι Y).app P) ≫
          CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι Y P))⟦m⟧' =
      (completedScalarChainComparison l E L ι Y).app (P⟦m⟧) ≫
        CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧)) ≫
        (ProductShift.productShiftIso (levelView l E L ι Y) P m).hom := by
  apply ProductShift.productShift_hom_ext (levelView l E L ι Y) P m
  intro n
  let b := completedScalarChainComparison l E L ι Y
  let φ := completedScalarRoosEndomorphism l E L ι Y
  calc
    _ = (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        (b.app P ≫ CochainComplex.mappingCocone.fst (φ P) ≫
          Limits.Pi.π (fun n ↦ (levelView l E L ι Y n).obj P) n)⟦m⟧' := by
      calc
        _ = _ ≫ ((b.app P ≫ CochainComplex.mappingCocone.fst (φ P))⟦m⟧' ≫
              (Limits.Pi.π (fun n ↦ (levelView l E L ι Y n).obj P) n)⟦m⟧') :=
          Category.assoc _ _ _
        _ = _ := congrArg (fun f ↦
          (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app
            P) ≫ f)
          ((shiftFunctor (CochainComplex (integralTowerModules l L Y) ℤ) m).map_comp
            (b.app P ≫ CochainComplex.mappingCocone.fst (φ P))
            (Limits.Pi.π (fun n ↦ (levelView l E L ι Y n).obj P) n)).symm
    _ = b.app (P⟦m⟧) ≫ CochainComplex.mappingCocone.fst (φ (P⟦m⟧)) ≫
        Limits.Pi.π (fun n ↦ (levelView l E L ι Y n).obj (P⟦m⟧)) n ≫
          ((levelView l E L ι Y n).commShiftIso m).hom.app P :=
      chainFirst_shift l E L ι Y P m n
    _ = _ := by
      have h := ProductShift.productShiftIso_π (levelView l E L ι Y) P m n
      exact congrArg (fun f ↦ b.app (P⟦m⟧) ≫
        CochainComplex.mappingCocone.fst (φ (P⟦m⟧)) ≫ f) h.symm

private theorem chain_comparison_shift
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        ((completedScalarChainComparison l E L ι Y).app P)⟦m⟧' =
      (completedScalarChainComparison l E L ι Y).app (P⟦m⟧) ≫
        ((integralScalarComplexFunctor l E L ι Y).commShiftIso m).hom.app P := by
  exact RoosShift.chain_shift (integralScalarTowerFunctor l E L ι Y)
    (completedOrdinaryScalarComplex l E L ι Y) (completedScalarChainComparison l E L ι Y)
    (chainComparison_zeroSecond l E L ι Y) P m
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P)
    (chainFirstProduct_shift l E L ι Y P m)

/-- The canonical product of the finite tensor and restriction shift isomorphisms.
Source: Stacks 011G and 014E (blueprint: lem-weil-completed-scalar-chain-shift). -/
noncomputable def completedScalarChainProductIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
    (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj (P⟦m⟧)).obj (op n)) ≅
      (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))⟦m⟧ :=
  Limits.Pi.mapIso (fun n ↦ ((integralOperationsRestrict l L Y n).mapIso
      (((integralScalarReduction l E L ι Y n).mapCochainComplexShiftIso m).app P) ≪≫
    ((SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted
            l L Y n))).mapCochainComplexShiftIso m).app
      ((integralScalarFiniteComplex l E L ι Y n).obj P))) ≪≫
    (PreservesProduct.iso (shiftFunctor (CochainComplex (integralTowerModules l L Y) ℤ) m)
      (fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))).symm

/-- The strict Roos complex has a coherent signed shift compatible with its quotient map.
Source: Stacks Project, Tags 011G and 014E; the chain-level steps 2--5 of
lem-weil-point-completed-scalar-shift.
(blueprint: lem-weil-completed-scalar-chain-shift).
Proof: the tensor and restriction shift maps give the displayed level isomorphisms.
The transition maps commute with them: both composites send a sheafified generator
s tensor x to red(s) tensor x. Take their product and the canonical product-shift
comparison. It conjugates 1-s to the shifted 1-s. On its mapping cocone define alpha
by (x,y) -> (x,(-1)^m y). Its source differential is (e dx,-e dy-hx) and its target
differential (e dx,-e dy-e hx), so both composites equal (e dx,-dy-e hx).
The same formula gives the inverse. Product naturality gives naturality in P;
e_0=1 and e_(m+n)=e_m e_n give zero and addition coherence. The canonical chain
comparison has quotient component c and second component zero. Shifting its quotient
formula and using generation by sheafified pure tensors identifies the first
components; the second components both vanish. The two cocone projections give
the displayed chain equality. No resolution or derived descent is involved. -/
theorem completedScalarChainShift :
    ∃ eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ,
      RoosShift.ConeFormula (integralScalarTowerFunctor l E L ι Y)
        (completedScalarChainProductIso l E L ι Y) eC ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ),
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        ((completedScalarChainComparison l E L ι Y).app P)⟦m⟧' =
      (completedScalarChainComparison l E L ι Y).app (P⟦m⟧) ≫
        (Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P) := by
  have hp (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
      completedScalarChainProductIso l E L ι Y P m =
        ProductShift.productShiftIso (levelView l E L ι Y) P m := by
    unfold completedScalarChainProductIso
    simp only [← levelShift_iso]
    rfl
  exact ⟨scalarCoconeShift l E L ι Y,
    RoosShift.commShift_formula (integralScalarTowerFunctor l E L ι Y)
      (completedScalarChainProductIso l E L ι Y) hp,
    chain_comparison_shift l E L ι Y⟩

end WeilConjectures
