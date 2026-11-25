/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemTensorCochainComposition

/-! # Tensor normalization for two composable inverse images

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941, 03DI, 07A7;
blueprint fix-prop-coherence, strict-system realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus CoefficientClosedStructure.tensor
  Functor.mapDerivedCategory SheafOfModules.monoidalCategory
  Functor.leftAdjoint HasDerivedCategory.standard Scheme.residueField
  coefficientSequenceCommRingSheaf

private abbrev Complex (W : Scheme.{u}) :=
  CochainComplex (coefficientSequenceModules l E W) ℤ

private abbrev total (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

private abbrev inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorSequenceInverse l E f

private abbrev onComplex {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (inverse l E f).mapHomologicalComplex (.up ℤ)

private theorem inverse_square {C : Type*} [Category C] {A B D F : C}
    (e : A ≅ B) (d : D ≅ F) (a : B ⟶ F) (b : A ⟶ D)
    (h : e.hom ≫ a = b ≫ d.hom) : a ≫ d.inv = e.inv ≫ b := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (a ≫ d.inv) = (e.hom ≫ a) ≫ d.inv := (Category.assoc _ _ _).symm
    _ = (b ≫ d.hom) ≫ d.inv := congrArg (fun t ↦ t ≫ d.inv) h
    _ = b := by rw [Category.assoc, d.hom_inv_id, Category.comp_id]
    _ = e.hom ≫ (e.inv ≫ b) := (e.hom_inv_id_assoc b).symm

attribute [local irreducible] pullbackTensorSequenceCochain
  pullbackTensorSequenceAdjunction

private abbrev Good (W : Scheme.{u}) (P : Complex l E W) :=
  @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
    (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
    (pullbackTensorSequenceSmall W) (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) P

private theorem system_formula {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l E Y) (hp : Good l E Y P) (hq : Good l E Y Q) :
    (pull l E f).map (pullbackTensorSystemModel l E Y P Q hp hq).hom ≫
        (pullbackTensorSystemComparison l E f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (calculus l E X).systemClosed.tensor.map
          (Prod.mkHom ((inverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((inverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (inverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
        (pullbackTensorSystemModel l E X _ _
          (pullbackTensorSequenceGood l E f P hp)
          (pullbackTensorSequenceGood l E f Q hq)).hom := by
  exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hp hq

attribute [local irreducible] pullbackTensorSystemComparison

private theorem inverse_compositor_model (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Complex l E Z) :
    (pull l E f).map ((inverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
        (inverse l E f).mapDerivedCategoryFactors.hom.app ((onComplex l E g).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).inv.app P) =
      (c.pullComp f g).inv.app (DerivedCategory.Q.obj P) ≫
        (inverse l E (f ≫ g)).mapDerivedCategoryFactors.hom.app P := by
  simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv] using
    inverse_square ((c.pullComp f g).app (DerivedCategory.Q.obj P))
    (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).app P))
    ((pull l E f).map ((inverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
      (inverse l E f).mapDerivedCategoryFactors.hom.app ((onComplex l E g).obj P))
    ((inverse l E (f ≫ g)).mapDerivedCategoryFactors.hom.app P)
    (c.pullComp_model f g P)

private theorem inverse_cochain_composition (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P Q : Complex l E Z) :
    (onComplex l E f).map ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
        (pullbackTensorSequenceCochain l E f).hom.app
          ((onComplex l E g).obj P, (onComplex l E g).obj Q) ≫
        (total l E X).map (Prod.mkHom
          ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).inv.app P)
          ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).inv.app Q)) =
      (NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).inv.app
          ((total l E Z).obj (P, Q)) ≫
        (pullbackTensorSequenceCochain l E (f ≫ g)).hom.app (P, Q) := by
  let a := NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)
  have h := integralSystemTensorCochainComposition l E o c f g P Q
  have h' := inverse_square
    (a.app ((total l E Z).obj (P, Q)))
    ((total l E X).mapIso ((a.app P).prod (a.app Q)))
    ((onComplex l E f).map ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
      (pullbackTensorSequenceCochain l E f).hom.app
        ((onComplex l E g).obj P, (onComplex l E g).obj Q))
    ((pullbackTensorSequenceCochain l E (f ≫ g)).hom.app (P, Q)) h
  simpa only [Functor.mapIso_inv, Iso.prod, Iso.app_inv, Category.assoc] using h'

private theorem tensor_model_naturality (W : Scheme.{u})
    (P Q P' Q' : Complex l E W) (hp : Good l E W P) (hq : Good l E W Q)
    (hp' : Good l E W P') (hq' : Good l E W Q') (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map ((total l E W).map (Prod.mkHom a b)) ≫
        (pullbackTensorSystemModel l E W P' Q' hp' hq').hom =
      (pullbackTensorSystemModel l E W P Q hp hq).hom ≫
        (calculus l E W).systemClosed.tensor.map
          (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  exact (calculus l E W).systemTensorModel.comparison.hom.naturality
    (Prod.mkHom
      (ObjectProperty.homMk (X := ⟨P, hp⟩) (Y := ⟨P', hp'⟩) a)
      (ObjectProperty.homMk (X := ⟨Q, hq⟩) (Y := ⟨Q', hq'⟩) b))

private theorem map_three_pair {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {A B C' D' F' : C}
    (a : A ⟶ B) (b : B ⟶ F') (x : A ⟶ C') (y : C' ⟶ D') (z : D' ⟶ F')
    (h : a ≫ b = x ≫ y ≫ z) :
    T.map a ≫ T.map b = T.map x ≫ T.map y ≫ T.map z := by
  rw [← T.map_comp, h, T.map_comp, T.map_comp]

private theorem composition_on_representatives (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P Q : Complex l E Z)
    (hp : Good l E Z P) (hq : Good l E Z Q) :
    (pull l E f).map ((pullbackTensorSystemComparison l E g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((pull l E g).obj (DerivedCategory.Q.obj P),
            (pull l E g).obj (DerivedCategory.Q.obj Q)) ≫
        (calculus l E X).systemClosed.tensor.map (Prod.mkHom
          ((c.pullComp f g).inv.app (DerivedCategory.Q.obj P))
          ((c.pullComp f g).inv.app (DerivedCategory.Q.obj Q))) =
      (c.pullComp f g).inv.app
          ((calculus l E Z).systemClosed.tensor.obj
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (pullbackTensorSystemComparison l E (f ≫ g)).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let Fa := onComplex l E g
  let Fb := onComplex l E f
  let Fc := onComplex l E (f ≫ g)
  let F := pull l E g
  let G := pull l E f
  let H := pull l E (f ≫ g)
  let U := (calculus l E Y).systemClosed.tensor
  let V := (calculus l E X).systemClosed.tensor
  let cc := (c.pullComp f g).symm
  let aa := (NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).symm
  let rR := (pullbackTensorSystemModel l E Z P Q hp hq).hom
  let rS := (pullbackTensorSystemModel l E Y (Fa.obj P) (Fa.obj Q)
    (pullbackTensorSequenceGood l E g P hp) (pullbackTensorSequenceGood l E g Q hq)).hom
  let rT := (pullbackTensorSystemModel l E X (Fb.obj (Fa.obj P)) (Fb.obj (Fa.obj Q))
    (pullbackTensorSequenceGood l E f _ (pullbackTensorSequenceGood l E g P hp))
    (pullbackTensorSequenceGood l E f _ (pullbackTensorSequenceGood l E g Q hq))).hom
  let rC := (pullbackTensorSystemModel l E X (Fc.obj P) (Fc.obj Q)
    (pullbackTensorSequenceGood l E (f ≫ g) P hp)
    (pullbackTensorSequenceGood l E (f ≫ g) Q hq)).hom
  let e (K : Complex l E Z) := (inverse l E g).mapDerivedCategoryFactors.hom.app K
  let d (K : Complex l E Y) := (inverse l E f).mapDerivedCategoryFactors.hom.app K
  let b (K : Complex l E Z) := (inverse l E (f ≫ g)).mapDerivedCategoryFactors.hom.app K
  let k (K : Complex l E Z) := DerivedCategory.Q.map (aa.hom.app K)
  have : IsIso (Prod.mkHom (b P) (b Q)) := by
    change IsIso ((asIso (b P)).prod (asIso (b Q))).hom
    infer_instance
  have ha := system_formula l E g P Q hp hq
  have hb := system_formula l E f (Fa.obj P) (Fa.obj Q)
    (pullbackTensorSequenceGood l E g P hp) (pullbackTensorSequenceGood l E g Q hq)
  have hc := system_formula l E (f ≫ g) P Q hp hq
  have hs : V.map (Prod.mkHom
      (cc.hom.app (DerivedCategory.Q.obj P)) (cc.hom.app (DerivedCategory.Q.obj Q))) ≫
      V.map (Prod.mkHom (b P) (b Q)) =
      V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) ≫
        V.map (Prod.mkHom (d (Fa.obj P)) (d (Fa.obj Q))) ≫
          V.map (Prod.mkHom (k P) (k Q)) := by
    exact map_three_pair V _ _ _ _ _
      (Prod.ext (inverse_compositor_model l E o c f g P).symm
        (inverse_compositor_model l E o c f g Q).symm)
  have hr : DerivedCategory.Q.map ((total l E X).map
      (Prod.mkHom (aa.hom.app P) (aa.hom.app Q))) ≫ rC =
      rT ≫ V.map (Prod.mkHom (k P) (k Q)) := by
    exact tensor_model_naturality l E X
      (Fb.obj (Fa.obj P)) (Fb.obj (Fa.obj Q)) (Fc.obj P) (Fc.obj Q)
      (pullbackTensorSequenceGood l E f _ (pullbackTensorSequenceGood l E g P hp))
      (pullbackTensorSequenceGood l E f _ (pullbackTensorSequenceGood l E g Q hq))
      (pullbackTensorSequenceGood l E (f ≫ g) P hp)
      (pullbackTensorSequenceGood l E (f ≫ g) Q hq)
      (aa.hom.app P) (aa.hom.app Q)
  have hnat := (pullbackTensorSystemComparison l E f).hom.naturality
    (Prod.mkHom (e P) (e Q))
  change G.map (U.map (Prod.mkHom (e P) (e Q))) ≫
    (pullbackTensorSystemComparison l E f).hom.app _ =
    (pullbackTensorSystemComparison l E f).hom.app _ ≫
      V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) at hnat
  have hf := (inverse l E f).mapDerivedCategoryFactors.hom.naturality
    ((pullbackTensorSequenceCochain l E g).hom.app (P, Q))
  change G.map (DerivedCategory.Q.map
      ((pullbackTensorSequenceCochain l E g).hom.app (P, Q))) ≫ d _ =
    d _ ≫ DerivedCategory.Q.map (Fb.map
      ((pullbackTensorSequenceCochain l E g).hom.app (P, Q))) at hf
  have hga := congrArg G.map ha
  simp only [Functor.map_comp] at hga
  have ht := congrArg DerivedCategory.Q.map (inverse_cochain_composition l E o c f g P Q)
  simp only [Functor.map_comp] at ht
  have hcc := inverse_compositor_model l E o c f g ((total l E Z).obj (P, Q))
  have hn := cc.hom.naturality rR
  dsimp only [Functor.comp_map] at hn
  apply (cancel_epi (G.map (F.map rR))).mp
  apply (cancel_mono (V.map (Prod.mkHom (b P) (b Q)))).mp
  simp only [Category.assoc]
  exact CategoryTheory.ScalarHomTensor.diagram_paste (Cat := System l E X)
    hs hnat.symm hga hb hf hr.symm ht
    hcc hc.symm hn.symm

/-- The section-normalized inverse-image compositor respects the fixed system
tensor comparison for two composable morphisms. No commutative square, right
adjoint, open extension or proper/open map occurs here.
Source: Stacks 03EL, 03D8, 07A4, 07A7 and 0941; fix-prop-coherence,
strict-system realization step 4
(blueprint: lem-sf-integral-system-tensor-composition).

Proof: choose flat-term K-flat representatives for A and B on the sequence site.
On each total tensor summand, the two inverse-image tensor comparisons send a
pure tensor to the two inverse images of its factors. The ordinary compositor is
the adjoint conjugate of restriction along pullbackComp; its unit equation
identifies these sections with those for the composite morphism. Hence both
composites agree on every generalized pure tensor. Tensor generation and the
total-summand injections give equality of chain maps. Exact inverse image preserves
K-flat representatives, so localize this equality using the fixed system tensor
models. Compositors.pullComp_model identifies the localized ordinary compositor
with c.pullComp, and pullbackTensorSystemComparison_existsUnique identifies the
localized tensor maps with the displayed ones. Every object admits such a resolving
representative, and naturality transports the equality to A and B. This proves a
whole-system equality before evaluation. The construction is valid for identity
morphisms and zero inputs; no flatness of a coefficient quotient is needed. -/
theorem integralSystemTensorComposition (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (A B : System l E Z) :
    (c.pullComp f g).hom.app ((calculus l E Z).systemClosed.tensor.obj (A, B)) ≫
        (pull l E f).map ((pullbackTensorSystemComparison l E g).hom.app (A, B)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((pull l E g).obj A, (pull l E g).obj B) =
      (pullbackTensorSystemComparison l E (f ≫ g)).hom.app (A, B) ≫
        (calculus l E X).systemClosed.tensor.map
          (Prod.mkHom ((c.pullComp f g).hom.app A) ((c.pullComp f g).hom.app B)) := by
  let F := pull l E g
  let G := pull l E f
  let H := pull l E (f ≫ g)
  let cc := (c.pullComp f g).symm
  let lhs : (calculus l E Z).systemClosed.tensor ⋙ F ⋙ G ⟶
      (H.prod H) ⋙ (calculus l E X).systemClosed.tensor :=
    whiskerRight (pullbackTensorSystemComparison l E g).hom G ≫
      whiskerLeft (F.prod F) (pullbackTensorSystemComparison l E f).hom ≫
        whiskerRight (NatTrans.prod cc.hom cc.hom) (calculus l E X).systemClosed.tensor
  let rhs : (calculus l E Z).systemClosed.tensor ⋙ F ⋙ G ⟶
      (H.prod H) ⋙ (calculus l E X).systemClosed.tensor :=
    whiskerLeft (calculus l E Z).systemClosed.tensor cc.hom ≫
      (pullbackTensorSystemComparison l E (f ≫ g)).hom
  have hres (M : System l E Z) :
      ∃ (P : Complex l E Z), Good l E Z P ∧ Nonempty (DerivedCategory.Q.obj P ≅ M) := by
    let K := DerivedCategory.Q.objPreimage M
    obtain ⟨P, p, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E Z) K
    have : QuasiIso p := hq
    exact ⟨P, hp, ⟨asIso (DerivedCategory.Q.map p) ≪≫
      DerivedCategory.Q.objObjPreimageIso M⟩⟩
  have hh : lhs = rhs := by
    apply NatTrans.ext
    funext M
    obtain ⟨P, hp, ⟨eP⟩⟩ := hres M.1
    obtain ⟨Q, hq, ⟨eQ⟩⟩ := hres M.2
    let e := eP.prod eQ
    apply (cancel_epi (((calculus l E Z).systemClosed.tensor ⋙ F ⋙ G).map e.hom)).mp
    rw [lhs.naturality, rhs.naturality]
    have h := composition_on_representatives l E o c f g P Q hp hq
    exact congrArg (fun t ↦ t ≫ ((H.prod H) ⋙
      (calculus l E X).systemClosed.tensor).map e.hom) h
  have h := congrArg (fun t ↦ t.app (A, B)) hh
  have h' := inverse_square
    ((c.pullComp f g).app ((calculus l E Z).systemClosed.tensor.obj (A, B))).symm
    ((calculus l E X).systemClosed.tensor.mapIso
      (((c.pullComp f g).app A).prod ((c.pullComp f g).app B))).symm
    ((pullbackTensorSystemComparison l E (f ≫ g)).hom.app (A, B))
    ((pull l E f).map ((pullbackTensorSystemComparison l E g).hom.app (A, B)) ≫
      (pullbackTensorSystemComparison l E f).hom.app
        ((pull l E g).obj A, (pull l E g).obj B))
    (by simpa only [lhs, rhs, cc, F, G, H, Functor.prod_obj, Iso.symm_hom, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, NatTrans.prod, Functor.comp_obj,
      Functor.mapIso_inv, Iso.prod, Iso.app_inv, Category.assoc] using h.symm)
  simpa only [Iso.symm_inv, Functor.mapIso_hom, Iso.prod, Iso.app_hom,
    Category.assoc] using h'.symm

end WeilConjectures.IntegralSystemRealization
