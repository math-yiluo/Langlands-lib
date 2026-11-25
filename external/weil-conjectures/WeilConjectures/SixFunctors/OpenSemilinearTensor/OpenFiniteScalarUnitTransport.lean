/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement

/-! # Unit-normalized finite scalar transport on the open slice

Source: Stacks Project, Modules on Sites, Tags 03DI, 03EK and 0E8I.
(blueprint: lem-sf-open-finite-scalar-unit-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Functor Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

section ScalarRestriction
universe c d v w r
variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

private def scalarRestrictionSquare
    {R S : Sheaf J CommRingCat.{max c d v w r}} {R' S' : Sheaf K CommRingCat.{max c d v w r}}
    (a : R ⟶ S) (b : R' ⟶ S')
    (p : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{max c d v w r} J K).obj R')
    (q : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{max c d v w r} J K).obj S')
    (h : p ≫ (F.sheafPushforwardContinuous CommRingCat.{max c d v w r} J K).map b = a ≫ q) :
    SheafOfModules.restrictScalars.{max c d v w r}
        ((sheafCompose K (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map b) ⋙
      SheafOfModules.pushforward.{max c d v w r} (F := F)
        ((sheafCompose J (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map p) ≅
    SheafOfModules.pushforward.{max c d v w r} (F := F)
        ((sheafCompose J (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map q) ⋙
      SheafOfModules.restrictScalars.{max c d v w r}
        ((sheafCompose J (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map a) := by
  let L := SheafOfModules.restrictScalars.{max c d v w r}
    ((sheafCompose K (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map b) ⋙
    SheafOfModules.pushforward (F := F) (J := J) (K := K)
      (R := (sheafCompose K
        (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).obj R')
      ((sheafCompose J (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map p)
  let T := SheafOfModules.pushforward.{max c d v w r} (F := F) (J := J) (K := K)
    (R := (sheafCompose K
      (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).obj S')
    ((sheafCompose J (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map q) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max c d v w r} RingCat.{max c d v w r})).map a)
  change L ≅ T
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine
      { hom :=
          { val :=
              { app := fun W ↦ ModuleCat.ofHom
                  (X := (L.obj M).val.obj W) (Y := (T.obj M).val.obj W)
                  { toFun := fun x ↦ x
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := ?_ }
                naturality := ?_ } }
        inv :=
          { val :=
              { app := fun W ↦ ModuleCat.ofHom
                  (X := (T.obj M).val.obj W) (Y := (L.obj M).val.obj W)
                  { toFun := fun x ↦ x
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := ?_ }
                naturality := ?_ } }
        hom_inv_id := by ext W x; rfl
        inv_hom_id := by ext W x; rfl }
    · intro r x
      let y : M.val.obj (F.op.obj W) := x
      change (b.hom.app (F.op.obj W)) ((p.hom.app W) r) • y =
        (q.hom.app W) ((a.hom.app W) r) • y
      exact congrArg (fun s : S'.obj.obj (F.op.obj W) ↦ s • y)
        (congrArg (fun f ↦ (f.hom.app W) r) h)
    · intro W W' f
      ext x
      rfl
    · intro r x
      let y : M.val.obj (F.op.obj W) := x
      change (q.hom.app W) ((a.hom.app W) r) • y =
        (b.hom.app (F.op.obj W)) ((p.hom.app W) r) • y
      exact congrArg (fun s : S'.obj.obj (F.op.obj W) ↦ s • y)
        (congrArg (fun f ↦ (f.hom.app W) r) h).symm
    · intro W W' f
      ext x
      rfl
  · intro M N f
    ext W x
    rfl
end ScalarRestriction

namespace WeilConjectures.OpenSemilinearTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  completedIntegralCommRingSheafUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf scalarReductionExtension
  CategoryTheory.MorphismProperty CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  CategoryTheory.Functor.constComp
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  completedIntegralCommRingProjectionUnrestricted scalarReductionExistence

private abbrev scalarAdj (T : Scheme.{t}) (n : ℕ) :=
  (scalarReductionExtension_adjunction l E T n).choose

private abbrev sliceProjection (n : ℕ) :=
  ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
    (IntegralOpenReduction.openObject j)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)

private abbrev sliceRes (n : ℕ) :=
  SheafOfModules.restrictScalars.{max u (t+1)}
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
      (sliceProjection l E j n))

private def restrictionSquare (o : Operations l E j) (n : ℕ) :
    scalarReductionRestriction l E U n ⋙ o.integral.functor ≅
      (o.finite n).functor ⋙ sliceRes l E j n := by
  refine isoWhiskerLeft _ (eqToIso o.integralFunctor) ≪≫ ?_ ≪≫
    (isoWhiskerRight (eqToIso (o.finiteFunctor n)) _).symm
  exact scalarRestrictionSquare (IntegralOpenReduction.sliceSite j)
    (sliceProjection l E j n) (completedIntegralCommRingProjectionUnrestricted l E U n)
    o.completedMap (o.finiteMap n) (o.projections n)

private theorem restrictionSquare_apply (o : Operations l E j) (n : ℕ)
    (N : normalizedDVRModules l E U n) (W : (Over (IntegralOpenReduction.openObject j))ᵒᵖ)
    (x : (o.integral.functor.obj ((scalarReductionRestriction l E U n).obj N)).val.obj W) :
    ((restrictionSquare l E j o n).hom.app N).val.app W x =
      (((eqToHom (o.finiteFunctor n).symm).app N).val.app W)
        ((((eqToHom o.integralFunctor).app
          ((scalarReductionRestriction l E U n).obj N)).val.app W) x) := by
  rfl

attribute [local irreducible] restrictionSquare scalarRestrictionSquare

private theorem transport_unit (o : Operations l E j) (n : ℕ)
    (D : SheafOfModules.SystemScalarModel.{t + 1, t, max u (t + 1)}
      (sliceProjection l E j n))
    (η : scalarReductionExtension l E U n ⋙ (o.finite n).functor ≅
      o.integral.functor ⋙ D.model.E)
    (hη : ∀ M, D.ordinaryAdj.unit.app (o.integral.functor.obj M) ≫
        (sliceRes l E j n).map (η.inv.app M) =
      o.integral.functor.map ((scalarAdj l E U n).unit.app M) ≫
        (restrictionSquare l E j o n).hom.app ((scalarReductionExtension l E U n).obj M))
    (M : scalarReductionSource l E U) (W : Over (IntegralOpenReduction.openObject j))
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj W))) :
    (η.inv.app M).val.app (op W)
        ((D.ordinaryAdj.unit.app (o.integral.functor.obj M)).val.app (op W)
          (((eqToHom o.integralFunctor.symm).app M).val.app (op W) x)) =
      ((eqToHom (o.finiteFunctor n).symm).app
        ((scalarReductionExtension l E U n).obj M)).val.app (op W)
          (coefficientIntegralScalarUnitSection l E U n M
            (op ((IntegralOpenReduction.sliceSite j).obj W)) x) := by
  let G := o.integral.functor.obj M
  let x' : G.val.obj (op W) :=
    ((eqToHom o.integralFunctor.symm).app M).val.app (op W) x
  have ht := congrArg (fun f ↦ f.val.app (op W) x') (hη M)
  change (η.inv.app M).val.app (op W)
    ((D.ordinaryAdj.unit.app G).val.app (op W) x') =
    ((restrictionSquare l E j o n).hom.app _).val.app (op W)
      ((o.integral.functor.map ((scalarAdj l E U n).unit.app M)).val.app (op W) x') at ht
  rw [restrictionSquare_apply] at ht
  have hn := congrArg (fun f ↦ f.val.app (op W) x')
    ((eqToHom o.integralFunctor).naturality ((scalarAdj l E U n).unit.app M))
  change (((eqToHom o.integralFunctor).app _).val.app (op W))
      ((o.integral.functor.map ((scalarAdj l E U n).unit.app M)).val.app (op W) x') =
    ((scalarAdj l E U n).unit.app M).val.app
      (op ((IntegralOpenReduction.sliceSite j).obj W))
      (((eqToHom o.integralFunctor).app M).val.app (op W) x') at hn
  have hc : (((eqToHom o.integralFunctor).app M).val.app (op W)) x' = x := by
    exact congrArg (fun f ↦ f.val.app (op W) x)
      ((eqToIso o.integralFunctor).app M).inv_hom_id
  refine ht.trans (congrArg
    (fun y ↦ (((eqToHom (o.finiteFunctor n).symm).app
      ((scalarReductionExtension l E U n).obj M)).val.app (op W)) y) ?_)
  exact hn.trans (congrArg (fun y ↦ ((scalarAdj l E U n).unit.app M).val.app
    (op ((IntegralOpenReduction.sliceSite j).obj W)) y) hc)

/-- Scalar extension on U and scalar extension on the transported slice have a
comparison which preserves the actual normalized units on original sections.
Source: Stacks 03CZ, 03DI; categorical unit transport across equivalences
(blueprint: lem-sf-open-finite-scalar-unit-transport).

Proof: the projection equality gives the scalar-restriction square. Its maps are
identities on the underlying sections; linearity is exactly that projection equality.
Insert the given forward-functor equalities on the two sides. The normalized comparison
of left adjoints across the two coefficient equivalences produces η with its unit
identity. Evaluate that identity on a slice section. Naturality of the forward-functor
cast moves the integral scalar unit past the cast, and the inverse casts cancel.
The resulting equation is the displayed formula on the original section. -/
theorem exists_openFiniteScalarUnitTransport (o : Operations l E j) (n : ℕ)
    (D : SheafOfModules.SystemScalarModel.{t + 1, t, max u (t + 1)}
      (((ProEt.topology X).overPullback CommRingCat.{max u (t + 1)}
        (IntegralOpenReduction.openObject j)).map
          (completedIntegralCommRingProjectionUnrestricted l E X n))) :
    ∃ η : scalarReductionExtension l E U n ⋙ (o.finite n).functor ≅
        o.integral.functor ⋙ D.model.E,
      ∀ (M : scalarReductionSource l E U)
        (W : Over (IntegralOpenReduction.openObject j))
        (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj W))),
        (η.inv.app M).val.app (op W)
            ((D.ordinaryAdj.unit.app (o.integral.functor.obj M)).val.app (op W)
              (((eqToHom o.integralFunctor.symm).app M).val.app (op W) x)) =
          ((eqToHom (o.finiteFunctor n).symm).app
            ((scalarReductionExtension l E U n).obj M)).val.app (op W)
              (coefficientIntegralScalarUnitSection l E U n M
                (op ((IntegralOpenReduction.sliceSite j).obj W)) x) := by
  obtain ⟨η, _, _, _, hη, _⟩ := exists_equivalenceAdjunctionComparison
    o.integral (o.finite n) (scalarAdj l E U n) D.ordinaryAdj (restrictionSquare l E j o n)
  exact ⟨η, fun M W x ↦ transport_unit l E j o n D η hη M W x⟩

end WeilConjectures.OpenSemilinearTensor
