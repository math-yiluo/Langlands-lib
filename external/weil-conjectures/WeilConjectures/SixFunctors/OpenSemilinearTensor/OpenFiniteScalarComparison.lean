/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGenerators
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenFiniteScalarUnitTransport

/-! # Generator-normalized scalar comparison at finite levels

Source: Stacks Project, Modules on Sites, Tags 03DI, 03EK and 0E8I.
(blueprint: lem-sf-open-finite-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Functor Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

section Casts
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

private theorem module_cast_cancel {M N : SheafOfModules.{r} R}
    (h : M = N) (W : Cᵒᵖ) (x : N.val.obj W) :
    (eqToHom h).val.app W ((eqToHom h.symm).val.app W x) = x := by
  subst h
  rfl

end Casts

section ExtensionGenerators
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (Z : C)

private theorem extension_unit
    (M : SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over Z))
    (W : Over Z) (x : M.val.obj (op W)) :
    ((SheafOfModules.localizedSystemAdjunction.{c, v, r} R Z).unit.app M).val.app (op W) x =
      SheafOfModules.ringedSliceExtensionSection.{c, v, r} R Z M W x :=
  (SheafOfModules.localizedSystemAdjunction_existsUnique.{c, v, r} R Z).exists.choose_spec
    M (op W) x

private theorem extension_map
    {M N : SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over Z)}
    (f : M ⟶ N) (W : Over Z) (x : M.val.obj (op W)) :
    ((SheafOfModules.localizedSystemExtension.{c, v, r} R Z).map f).val.app (op W.left)
        (SheafOfModules.ringedSliceExtensionSection.{c, v, r} R Z M W x) =
      SheafOfModules.ringedSliceExtensionSection.{c, v, r} R Z N W (f.val.app (op W) x) := by
  have h := congrArg (fun f ↦ f.val.app (op W) x)
    ((SheafOfModules.localizedSystemAdjunction.{c, v, r} R Z).unit.naturality f)
  change ((SheafOfModules.localizedSystemAdjunction.{c, v, r} R Z).unit.app N).val.app
    (op W) (f.val.app (op W) x) =
      ((SheafOfModules.localizedSystemExtension.{c, v, r} R Z).map f).val.app (op W.left)
        (((SheafOfModules.localizedSystemAdjunction.{c, v, r} R Z).unit.app M).val.app
          (op W) x) at h
  rw [extension_unit, extension_unit] at h
  exact h.symm

private theorem model_unit_raw
    {A B : Sheaf J CommRingCat.{max c v r}} {φ : A ⟶ B}
    (D : SheafOfModules.SystemScalarModel.{c, v, max c v r} φ)
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
    (W : Cᵒᵖ) (x : M.val.obj W) :
    (eqToHom (D.model.obj_eq M)).val.app W
      ((D.ordinaryAdj.unit.app M).val.app W x) =
    SheafOfModules.sliceScalarPure.{c, v, r} φ M W x 1 := by
  rw [D.unit_normalized M W x]
  dsimp only [SheafOfModules.systemModelTmul]
  rw [one_smul]
  exact module_cast_cancel (D.model.obj_eq M) W _

end ExtensionGenerators

namespace WeilConjectures.OpenSemilinearTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  completedIntegralCommRingSheafUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf scalarReductionExtension
  CategoryTheory.MorphismProperty CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  SheafOfModules.sliceScalarAlgebra CategoryTheory.Functor.constComp
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  completedIntegralCommRingProjectionUnrestricted scalarReductionExistence

private abbrev scalarAdj (T : Scheme.{t}) (n : ℕ) :=
  (scalarReductionExtension_adjunction l E T n).choose

private abbrev sliceProjection (n : ℕ) :=
  ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
    (IntegralOpenReduction.openObject j)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)

private theorem extensionSection_map (o : Operations l E j)
    {M N : scalarReductionSource l E U} (f : M ⟶ N) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((IntegralOpenReduction.extension l E j o).map f).val.app (op V)
      (IntegralOpenReduction.extensionSection l E j o M V a x) =
    IntegralOpenReduction.extensionSection l E j o N V a (f.val.app _ x) := by
  change ((SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (IntegralOpenReduction.openObject j)).map (o.integral.functor.map f)).val.app (op V)
      (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)} _ _ _ (Over.mk a)
        (((eqToHom o.integralFunctor.symm).app M).val.app (op (Over.mk a)) x)) = _
  refine (extension_map.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (IntegralOpenReduction.openObject j) (o.integral.functor.map f) (Over.mk a) _).trans ?_
  apply congrArg (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)}
    _ _ _ (Over.mk a))
  exact (congrArg (fun h ↦ h.val.app (op (Over.mk a)) x)
    ((eqToHom o.integralFunctor.symm).naturality f)).symm

private theorem finiteExtensionSection_map (o : Operations l E j) (n : ℕ)
    {M N : normalizedDVRModules l E U n} (f : M ⟶ N) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((IntegralOpenReduction.finiteExtension l E j o n).map f).val.app (op V)
      (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
    IntegralOpenReduction.finiteExtensionSection l E j o n N V a (f.val.app _ x) := by
  change ((SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E X n)
    (IntegralOpenReduction.openObject j)).map ((o.finite n).functor.map f)).val.app (op V)
      (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)} _ _ _ (Over.mk a)
        (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x)) = _
  refine (extension_map.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E X n)
    (IntegralOpenReduction.openObject j) ((o.finite n).functor.map f) (Over.mk a) _).trans ?_
  apply congrArg (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)}
    _ _ _ (Over.mk a))
  exact (congrArg (fun h ↦ h.val.app (op (Over.mk a)) x)
    ((eqToHom (o.finiteFunctor n).symm).naturality f)).symm

private theorem scalarUnit_naturality (T : Scheme.{t}) (n : ℕ)
    {M N : scalarReductionSource l E T} (f : M ⟶ N)
    (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    ((scalarReductionExtension l E T n).map f).val.app V
      (coefficientIntegralScalarUnitSection l E T n M V x) =
    coefficientIntegralScalarUnitSection l E T n N V (f.val.app V x) := by
  exact (congrArg (fun h ↦ h.val.app V x) ((scalarAdj l E T n).unit.naturality f)).symm

private theorem scalarUnit_raw (T : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E T) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (eqToHom ((scalarReductionExistence l E T n).choose_spec.choose M)).val.app V
      (coefficientIntegralScalarUnitSection l E T n M V x) =
    SheafOfModules.sliceScalarPure.{t+1, t, max u (t+1)}
      (completedIntegralCommRingProjectionUnrestricted l E T n) M V x 1 := by
  have h := (scalarReductionExtension_adjunction l E T n).choose_spec M V x
  apply Eq.trans (congrArg
    (fun y ↦ (eqToHom ((scalarReductionExistence l E T n).choose_spec.choose M)).val.app V y)
    h)
  exact module_cast_cancel ((scalarReductionExistence l E T n).choose_spec.choose M) V _

private theorem comparison_ext (o : Operations l E j) (n : ℕ)
    (M : scalarReductionSource l E U) (N : normalizedDVRModules l E X n)
    (f g : (scalarReductionExtension l E X n).obj
      ((IntegralOpenReduction.extension l E j o).obj M) ⟶ N)
    (h : ∀ (V : X.ProEt) (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      f.val.app (op V)
        (coefficientIntegralScalarUnitSection l E X n _ (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x)) =
      g.val.app (op V)
        (coefficientIntegralScalarUnitSection l E X n _ (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x))) : f = g := by
  apply ((scalarAdj l E X n).homEquiv _ _).injective
  apply ((SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (IntegralOpenReduction.openObject j)).homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  rcases W with ⟨⟨V, ⟨⟨⟩⟩, a⟩⟩
  ext x
  simp only [Adjunction.homEquiv_unit]
  change f.val.app (op V)
      (coefficientIntegralScalarUnitSection l E X n _ (op V)
        (((SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
          (completedIntegralCommRingSheafUnrestricted l E X)
          (IntegralOpenReduction.openObject j)).unit.app (o.integral.functor.obj M)).val.app
            (op (Over.mk a)) x)) =
    g.val.app (op V)
      (coefficientIntegralScalarUnitSection l E X n _ (op V)
        (((SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
          (completedIntegralCommRingSheafUnrestricted l E X)
          (IntegralOpenReduction.openObject j)).unit.app (o.integral.functor.obj M)).val.app
            (op (Over.mk a)) x))
  simp only [extension_unit]
  have hx := h V a (((eqToHom o.integralFunctor).app M).val.app (op (Over.mk a)) x)
  change f.val.app (op V) (coefficientIntegralScalarUnitSection l E X n _ (op V)
    (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)} _ _ _ (Over.mk a)
      (((eqToHom o.integralFunctor.symm).app M).val.app (op (Over.mk a))
        (((eqToHom o.integralFunctor).app M).val.app (op (Over.mk a)) x)))) =
    g.val.app (op V) (coefficientIntegralScalarUnitSection l E X n _ (op V)
    (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)} _ _ _ (Over.mk a)
      (((eqToHom o.integralFunctor.symm).app M).val.app (op (Over.mk a))
        (((eqToHom o.integralFunctor).app M).val.app (op (Over.mk a)) x)))) at hx
  have hc : (((eqToHom o.integralFunctor.symm).app M).val.app (op (Over.mk a)))
      ((((eqToHom o.integralFunctor).app M).val.app (op (Over.mk a))) x) = x := by
    exact congrArg (fun f ↦ f.val.app (op (Over.mk a)) x)
      ((eqToIso o.integralFunctor).app M).hom_inv_id
  rw [hc] at hx
  exact hx

private theorem tensorComparison_unique (o : Operations l E j)
    (c d : IntegralOpenReduction.TensorComparison l E j o) : c = d := by
  have hc : c.ordinary = d.ordinary := by
    funext n
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply comparison_ext l E j o n M
    intro V a x
    rw [c.generators, d.generators]
  cases c
  cases d
  cases hc
  rfl

private theorem level_exists (o : Operations l E j) (n : ℕ) :
    ∃ e : IntegralOpenReduction.extension l E j o ⋙ scalarReductionExtension l E X n ≅
        scalarReductionExtension l E U n ⋙ IntegralOpenReduction.finiteExtension l E j o n,
      ∀ (M : scalarReductionSource l E U) (V : X.ProEt)
        (a : V ⟶ IntegralOpenReduction.openObject j)
        (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
        (e.hom.app M).val.app (op V)
          (coefficientIntegralScalarUnitSection l E X n _ (op V)
            (IntegralOpenReduction.extensionSection l E j o M V a x)) =
        IntegralOpenReduction.finiteExtensionSection l E j o n
          ((scalarReductionExtension l E U n).obj M) V a
            (coefficientIntegralScalarUnitSection l E U n M
              (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
  let B := (Functor.const ℕᵒᵖ).obj (integralCoefficientCommRingSheaf l E X n)
  let α := (Functor.const ℕᵒᵖ).map (completedIntegralCommRingProjectionUnrestricted l E X n)
  obtain ⟨p⟩ := SheafOfModules.exists_semilinearSliceScalarGenerators.{t+1, t, max u (t+1)}
    B (IntegralOpenReduction.openObject j) (completedIntegralCommRingSheafUnrestricted l E X) α
  obtain ⟨D⟩ := SheafOfModules.nonempty_systemScalarModel (sliceProjection l E j n)
  obtain ⟨η, hη⟩ := exists_openFiniteScalarUnitTransport l E j o n D
  let L := SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E X n) (IntegralOpenReduction.openObject j)
  let e (M : scalarReductionSource l E U) :
      (scalarReductionExtension l E X n).obj
        ((IntegralOpenReduction.extension l E j o).obj M) ≅
      (IntegralOpenReduction.finiteExtension l E j o n).obj
        ((scalarReductionExtension l E U n).obj M) :=
    eqToIso ((scalarReductionExistence l E X n).choose_spec.choose _) ≪≫
      p.component (o.integral.functor.obj M) 0 ≪≫
        L.mapIso ((eqToIso (D.model.obj_eq _)).symm ≪≫ η.symm.app M)
  have he : ∀ (M : scalarReductionSource l E U) (V : X.ProEt)
      (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      (e M).hom.val.app (op V)
        (coefficientIntegralScalarUnitSection l E X n _ (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x)) =
      IntegralOpenReduction.finiteExtensionSection l E j o n
        ((scalarReductionExtension l E U n).obj M) V a
          (coefficientIntegralScalarUnitSection l E U n M
            (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x) := by
    intro M V a x
    let W : Over (IntegralOpenReduction.openObject j) := Over.mk a
    let G := o.integral.functor.obj M
    let x' : G.val.obj (op W) :=
      ((eqToHom o.integralFunctor.symm).app M).val.app (op W) x
    have hX : (eqToHom ((scalarReductionExistence l E X n).choose_spec.choose _)).val.app
        (op V) (coefficientIntegralScalarUnitSection l E X n _ (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x)) =
        SheafOfModules.sliceScalarPure.{t+1, t, max u (t+1)}
          (completedIntegralCommRingProjectionUnrestricted l E X n) _ (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x) 1 := by
      exact scalarUnit_raw l E X n _ _ _
    have hD : (eqToHom (D.model.obj_eq G)).val.app (op W)
        ((D.ordinaryAdj.unit.app G).val.app (op W) x') =
        SheafOfModules.sliceScalarPure.{t+1, t, max u (t+1)}
          (sliceProjection l E j n) G (op W) x' 1 := by
      exact model_unit_raw.{t+1, t, max u (t+1)} D G (op W) x'
    have htransport : (η.inv.app M).val.app (op W)
        ((D.ordinaryAdj.unit.app G).val.app (op W) x') =
        ((eqToHom (o.finiteFunctor n).symm).app
          ((scalarReductionExtension l E U n).obj M)).val.app (op W)
            (coefficientIntegralScalarUnitSection l E U n M
              (op ((IntegralOpenReduction.sliceSite j).obj W)) x) := by
      exact hη M W x
    change (L.map ((eqToIso (D.model.obj_eq G)).inv ≫ η.inv.app M)).val.app (op V)
      ((p.component G 0).hom.val.app (op V)
        ((eqToHom ((scalarReductionExistence l E X n).choose_spec.choose _)).val.app
          (op V) (coefficientIntegralScalarUnitSection l E X n _ (op V)
            (IntegralOpenReduction.extensionSection l E j o M V a x)))) = _
    refine (congrArg (fun y ↦ (L.map
      ((eqToIso (D.model.obj_eq G)).inv ≫ η.inv.app M)).val.app (op V)
        ((p.component G 0).hom.val.app (op V) y)) hX).trans ?_
    refine (congrArg (fun y ↦ (L.map
      ((eqToIso (D.model.obj_eq G)).inv ≫ η.inv.app M)).val.app (op V) y)
        (p.generator G 0 W x' 1)).trans ?_
    refine (extension_map.{t+1, t, max u (t+1)}
      (integralCoefficientCommRingSheaf l E X n) (IntegralOpenReduction.openObject j)
      ((eqToIso (D.model.obj_eq G)).inv ≫ η.inv.app M) W _).trans ?_
    apply congrArg (SheafOfModules.ringedSliceExtensionSection.{t+1, t, max u (t+1)}
      _ _ _ W)
    have hc : (eqToHom (D.model.obj_eq G).symm).val.app (op W)
        ((eqToHom (D.model.obj_eq G)).val.app (op W)
          ((D.ordinaryAdj.unit.app G).val.app (op W) x')) =
        (D.ordinaryAdj.unit.app G).val.app (op W) x' :=
      module_cast_cancel (D.model.obj_eq G).symm (op W) _
    exact (congrArg (fun y ↦ (η.inv.app M).val.app (op W)
      ((eqToHom (D.model.obj_eq G).symm).val.app (op W) y)) hD).symm.trans
        ((congrArg (fun y ↦ (η.inv.app M).val.app (op W) y) hc).trans htransport)
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro M N f
  apply comparison_ext l E j o n M
  intro V a x
  change (e N).hom.val.app (op V)
    (((scalarReductionExtension l E X n).map
      ((IntegralOpenReduction.extension l E j o).map f)).val.app (op V)
        (coefficientIntegralScalarUnitSection l E X n _ (op V)
          (IntegralOpenReduction.extensionSection l E j o M V a x))) =
    ((IntegralOpenReduction.finiteExtension l E j o n).map
      ((scalarReductionExtension l E U n).map f)).val.app (op V)
        ((e M).hom.val.app (op V)
          (coefficientIntegralScalarUnitSection l E X n _ (op V)
            (IntegralOpenReduction.extensionSection l E j o M V a x)))
  rw [scalarUnit_naturality, extensionSection_map, he, he, finiteExtensionSection_map,
    scalarUnit_naturality]

set_option linter.unusedVariables false in
/-- There is a unique family of finite scalar comparisons preserving every scalar-unit
extension summand. This asserts no compatibility between different coefficient levels.
Source: Stacks 03DI, 03EK and 0E8I; finite-level part of the strict scalar transport
(blueprint: lem-sf-open-finite-scalar-comparison).

Proof: at level n specialize the ringed-slice scalar generator comparison to the
completed coefficient sheaf and its projection to the nth quotient. The component is
linear over the quotient ring, hence is an isomorphism before scalar restriction.
Transport its source by the completed coefficient equivalence and its target by the
finite coefficient equivalence. The equality `o.projections n` identifies the two
scalar restriction functors under these equivalences. Use the unique comparison of
left adjoints preserving units to identify the scalar extensions. The specified
forward-functor equalities say these transports act on the original sections, so the
component formula at coefficient one is exactly `TensorComparison.generators`.
For uniqueness, two such maps agree after precomposition with the scalar-adjunction
unit, since maps out of open extension are determined by their original summands.
Scalar-adjunction injectivity makes the maps equal; natural transformations and their
inverse isomorphisms are therefore equal. Apply this independently at every n. -/
theorem existsUnique_openFiniteScalarComparison (o : Operations l E j) :
    ∃! tc : IntegralOpenReduction.TensorComparison l E j o, True := by
  choose e he using level_exists l E j o
  refine ⟨⟨e, he⟩, trivial, ?_⟩
  intro c _
  exact tensorComparison_unique l E j o c ⟨e, he⟩

end WeilConjectures.OpenSemilinearTensor
