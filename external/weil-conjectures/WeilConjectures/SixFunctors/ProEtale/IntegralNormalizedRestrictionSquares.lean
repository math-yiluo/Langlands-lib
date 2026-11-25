/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.SixFunctors.ProEtale.IntegralPresentationEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteReductionPullback
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap

/-! # Normalized integral restriction squares -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
-- These instances must remain reducible in dependent coefficient-ring expressions.
set_option linter.style.haveILetI false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u vSite uSite uRing uModule
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

section ConstantUnit
variable {C D B : Type*} [Category C] [Category D] [Category B]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J B] [HasWeakSheafify K B] [F.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ B, F.op.HasPointwiseLeftKanExtension P]

private theorem constantPullback_unit_all {W : C} (hW : IsTerminal W)
    (hFW : IsTerminal (F.obj W)) (M : B) (G : Sheaf J B)
    (a : (constantSheaf J B).obj M ⟶ G) (V : C) :
    ((toSheafify K ((Functor.const Dᵒᵖ).obj M)) ≫
      ((constantPullbackMonoidalIso F J K hW hFW).hom.app M ≫
        (Functor.sheafPullbackConstruction.sheafPullback F B J K).map a).hom).app
          (op (F.obj V)) =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V) ≫ a.hom.app (op V)) ≫
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F B J K).unit.app G).hom.app
          (op V) := by
  let q := toSheafify K ((Functor.const Dᵒᵖ).obj M) ≫
    ((constantPullbackMonoidalIso F J K hW hFW).hom.app M ≫
      (Functor.sheafPullbackConstruction.sheafPullback F B J K).map a).hom
  let r := (toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ a.hom) ≫
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F B J K).unit.app G).hom
  have h := constantPullback_unit_map F J K hW hFW M G a
  change q.app (op (F.obj W)) = r.app (op W) at h
  have hq := constant_naturality q (F.map (hW.from V)).op
  have hr := constant_naturality r (hW.from V).op
  change q.app (op (F.obj V)) = r.app (op V)
  rw [← hq, h]
  exact hr
end ConstantUnit

local instance integralNormalizedRestrictionSquaresInst1
    : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _

private theorem canonicalAbelianMap_unit
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (S : Profinite.{u}) (b : ULift.{u + 1} B) :
    (FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom.app
        (op ((profiniteToProEtOf X).obj S))
        ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app
            (op ((profiniteToProEtOf X).obj S)) b) =
      ((sfbIntegralPointAdjunction.{u} X).unit.app (FiniteDiscreteOrdinary.coefficient B)).hom.app
        (op S) (ULift.up (ContinuousMap.const S b.down)) := by
  let M : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} B)
  let R := FiniteDiscreteOrdinary.coefficient B
  let e : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj M ⟶ R :=
    ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      _ R).symm (FiniteDiscreteOrdinary.pointConstants B)
  let a := constantPointIso.hom.app M ≫ pointUpperStar.map e
  have h₁ := constantPullback_unit_all
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X))
    (Scheme.ProEt.topology specZ.{u}) (Scheme.ProEt.topology X)
    (proEtIsTerminal (proEtTerminal specZ.{u}))
    (proEtIsTerminal ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
      (toSpecZ X)).obj (proEtTerminal specZ.{u}))) M (pointUpperStar.obj R) a
        (profiniteToProEt.obj S)
  have h₂ := constantPullback_unit_all profiniteToProEt
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ.{u})
    (terminalIsTerminal (C := Profinite.{u}))
    ((terminalIsTerminal (C := Profinite.{u})).isTerminalObj profiniteToProEt)
    M R e S
  have he := (sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    _ R |>.apply_symm_apply (FiniteDiscreteOrdinary.pointConstants B)
  rw [Adjunction.homEquiv_unit] at he
  change toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj M) ≫ e.hom = _ at he
  have h₃ := congrArg (fun f ↦ f.app (op S)) he
  simp only [NatTrans.comp_app] at h₃
  rw [h₃] at h₂
  change (toSheafify (Scheme.ProEt.topology specZ.{u})
    ((Functor.const specZ.{u}.ProEtᵒᵖ).obj M)).app (op (profiniteToProEt.obj S)) ≫
      a.hom.app (op (profiniteToProEt.obj S)) = _ at h₂
  have h₄ := congrArg (fun f ↦ f ≫
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) Ab.{u + 1}
      (Scheme.ProEt.topology specZ.{u}) (Scheme.ProEt.topology X)).unit.app
        (pointUpperStar.obj R)).hom.app (op (profiniteToProEt.obj S))) h₂
  have h := congrArg (fun f : M ⟶ _ ↦ f b) (h₁.trans h₄)
  dsimp only [M, R, e] at h
  simp only [FiniteDiscreteOrdinary.canonicalAbelianMap, constantSchemeIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.associator_hom_app, Functor.whiskerRight_app,
    a, M, R, e, upperStarFromPoint, upperStarLowerStarAdjunction, sfbIntegralPointAdjunction,
    Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc,
    Category.comp_id,
    CategoryTheory.comp_apply, FiniteDiscreteOrdinary.pointConstants,
    pointUpperStarLowerStarAdjunction, pointLowerStar,
    Functor.sheafPushforwardContinuous_map_hom_app] at h ⊢
  exact h

private def finiteFunction
    (B : Type u) [TopologicalSpace B] [DiscreteTopology B] [Finite B]
    (S : Profinite.{u}) (f : C(S, B)) :
    S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of B) :=
  let g : S → B := fun x ↦ f x
  have h : @Continuous S B _ ⊥ g := by
    rw [← (@DiscreteTopology.eq_bot B ‹TopologicalSpace B› _)]
    exact f.continuous
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  CompHausLike.ofHom _ (⟨g, h⟩ : C(S, B))

private def finitePointLabels
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B]
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) :
    FiniteDiscreteOrdinary.coefficient B ⟶
      (sfbPullbackFromPointRightAdjoint X).obj (finiteAbSheaf X B) := by
  refine ⟨{
    app := fun S ↦ AddCommGrpCat.ofHom
      { toFun := fun f ↦ finiteRingSection X a B S.unop (finiteFunction B _ f.down)
        map_zero' := ?_
        map_add' := ?_ }
    naturality := ?_ }⟩
  · apply (finiteRingSection_const X a B _ _ 0 (fun _ ↦ rfl)).trans
    exact map_zero _
  · intro f g
    exact finiteRingSection_binary X a B _ (finiteFunction B _ f.down)
      (finiteFunction B _ g.down) (finiteFunction B _ (f + g).down)
      (· + ·) (fun _ ↦ rfl) (fun _ x y ↦ x + y)
      (by intro W Z h x y; exact map_add _ _ _)
      (by intro W x y; exact map_add _ _ _)
  · intro S T f
    ext g
    let h := (finiteRepresentation X a B).inv.naturality ((profiniteToProEtOf X).map f.unop).op
    have hh := congrArg (fun k ↦ k (ULift.up
      ((profiniteToProEtOf X).map (finiteFunction B _ g.down)))) h
    change (finiteRepresentation X a B).inv.app
      (op ((profiniteToProEtOf X).obj T.unop))
        (ULift.up ((profiniteToProEtOf X).map (f.unop ≫ finiteFunction B _ g.down))) =
      (finiteAbSheaf X B).obj.map ((profiniteToProEtOf X).map f.unop).op
        ((finiteRepresentation X a B).inv.app
          (op ((profiniteToProEtOf X).obj S.unop))
            (ULift.up ((profiniteToProEtOf X).map (finiteFunction B _ g.down))))
    change (finiteRepresentation X a B).inv.app
      (op ((profiniteToProEtOf X).obj T.unop))
        (ULift.up ((profiniteToProEtOf X).map f.unop ≫
          (profiniteToProEtOf X).map (finiteFunction B _ g.down))) = _ at hh
    rw [Functor.map_comp]
    exact hh

attribute [local irreducible] finitePointLabels

private def finiteBack
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B]
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) :
    condensedRingObj (FiniteDiscreteOrdinary.coefficient B) X ⟶ finiteAbSheaf X B :=
  ((sfbIntegralPointAdjunction X).homEquiv _ _).symm (finitePointLabels X B a)

private theorem finiteBack_unit
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B]
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (S : Profinite.{u}) (f : ULift.{u + 1} C(S, B)) :
    (finiteBack X B a).hom.app (op ((profiniteToProEtOf X).obj S))
      (((sfbIntegralPointAdjunction X).unit.app
        (FiniteDiscreteOrdinary.coefficient B)).hom.app (op S) f) =
      finiteRingSection X a B S (finiteFunction B _ f.down) := by
  have h := ((sfbIntegralPointAdjunction X).homEquiv _ _).apply_symm_apply
    (finitePointLabels X B a)
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k : FiniteDiscreteOrdinary.coefficient B ⟶
    (sfbPullbackFromPointRightAdjoint X).obj (finiteAbSheaf X B) ↦
      k.hom.app (op S) f) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    CategoryTheory.comp_apply, pointAdj_map_app, finiteBack, finitePointLabels] at hh ⊢
  exact hh

private theorem constant_test_ext
    {B : Ab.{u + 1}} {G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (f g : (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj B ⟶ G)
    {T : X.ProEt} (hT : IsTerminal T)
    (h : (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj B)).app (op T) ≫ f.hom.app (op T) =
      (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj B)).app (op T) ≫ g.hom.app (op T)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _ G.property
  apply NatTrans.ext
  funext V
  have hf := constant_naturality
    (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B) ≫ f.hom)
      (hT.from V.unop).op
  have hg := constant_naturality
    (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B) ≫ g.hom)
      (hT.from V.unop).op
  simp only [NatTrans.comp_app] at hf hg ⊢
  rw [← hf, h]
  exact hg

attribute [local irreducible] finiteBack

private theorem finiteBack_canonical
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B]
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) :
    FiniteDiscreteOrdinary.canonicalAbelianMap B X ≫ finiteBack X B a =
      (sfbConstantRingAbIso X (CommRingCat.of (ULift.{u + 1} B))).inv := by
  apply constant_test_ext X _ _ (finitePointTerminal X)
  ext b
  change (finiteBack X B a).hom.app _
    ((FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom.app _
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app _ b)) = _
  rw [canonicalAbelianMap_unit, finiteBack_unit, finiteRingSection_const X a B _ _ b.down
    (fun _ ↦ rfl)]
  have h := constantRingAb_unit X (CommRingCat.of (ULift.{u + 1} B))
    (op ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj finitePoint))) b
  let c := sfbConstantRingAbIso X (CommRingCat.of (ULift.{u + 1} B))
  have hc := ((sheafToPresheaf _ _).mapIso c).hom_inv_id_app_apply
    (op ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj finitePoint)))
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app _ b)
  exact hc.symm.trans (congrArg (c.inv.hom.app _) h)

private theorem finiteBack_ringIso_private
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B]
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (e : FiniteDiscreteOrdinary.Encoding B X) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.ringIso.inv = finiteBack X B a := by
  let J := Scheme.ProEt.topology X
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  let F := sheafCompose J V
  let c := sfbConstantRingAbIso X (CommRingCat.of (ULift.{u + 1} B))
  have hg : c.inv ≫ F.map e.ringIso.hom =
      FiniteDiscreteOrdinary.canonicalAbelianMap B X := by
    apply constant_test_ext X _ _ (finitePointTerminal X)
    ext b
    let W := op ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj finitePoint))
    have hc : c.inv.hom.app W
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} B)))).app W b) =
        (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} B)))).app W b := by
      have hh := constantRingAb_unit X (CommRingCat.of (ULift.{u + 1} B)) W b
      exact (congrArg (c.inv.hom.app W) hh).symm.trans
        (((sheafToPresheaf J Ab.{u + 1}).mapIso c).hom_inv_id_app_apply W _)
    change (F.map e.ringIso.hom).hom.app W (c.inv.hom.app W _) = _
    erw [hc]
    exact e.normalization W b
  apply (cancel_epi (F.map e.ringIso.hom)).mp
  apply (cancel_epi c.inv).mp
  calc
    c.inv ≫ F.map e.ringIso.hom ≫ F.map e.ringIso.inv = c.inv := by
      rw [← F.map_comp, e.ringIso.hom_inv_id, F.map_id]
      exact Category.comp_id _
    _ = c.inv ≫ F.map e.ringIso.hom ≫ finiteBack X B a := by
      rw [← Category.assoc, hg, finiteBack_canonical]

/-- Public export of the private `finiteBack_ringIso_private`
(used by `import all` importers; linter.privateModule). -/
alias finiteBack_ringIso := finiteBack_ringIso_private

private def continuousRingTopologyIso
    (B : Type u) [Ring B] (t₁ t₂ : TopologicalSpace B) (ht : t₁ = t₂)
    (h₁ : @IsTopologicalRing B t₁ _) (h₂ : @IsTopologicalRing B t₂ _) :
    @Profinite.continuousCoefficientRingSheaf.{u} B t₁ _ h₁ ≅
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} B t₂ _ h₂ where
  hom := ⟨{
    app := fun S ↦ RingCat.ofHom {
      toFun := fun f ↦ ULift.up
        { toFun := @ContinuousMap.toFun S.unop B _ t₁ f.down
          continuous_toFun := ht ▸ (@ContinuousMap.continuous_toFun S.unop B _ t₁ f.down) }
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    naturality := by intro S T f; ext g; rfl }⟩
  inv := by
    letI : TopologicalSpace B := t₁
    exact ⟨{
      app := fun S ↦ RingCat.ofHom {
        toFun := fun f ↦ ULift.up
          { toFun := @ContinuousMap.toFun S.unop B _ t₂ f.down
            continuous_toFun := ht.symm ▸ (@ContinuousMap.continuous_toFun S.unop B _ t₂ f.down) }
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
      naturality := by intro S T f; ext g; rfl }⟩
  hom_inv_id := by ext S f; rfl
  inv_hom_id := by ext S f; rfl

private def integerPointRingIso : DerivedNakayama.integerRingSheaf l E ≅
    letI := spectralNorm.normedField (Padic l) E
    Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers l E) :=
  continuousRingTopologyIso (Padic.coefficientExtensionIntegers l E) _ _
    (congrArg (fun t : TopologicalSpace E ↦ TopologicalSpace.induced
      (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t)
        (DerivedNakayama.coefficientTopology l E).symm) _ _

private def integerPointIso : DerivedNakayama.integerRing l E ≅
    (sfbCondensedIntegers l E).X :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (integerPointRingIso l E)

private instance integerPointIso_hom_mon : IsMonHom (integerPointIso l E).hom :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (integerPointRingIso l E).hom

private instance integerPointIso_inv_mon : IsMonHom (integerPointIso l E).inv :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (integerPointRingIso l E).inv

private theorem point_hom_ext
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    {B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (f g : (upperStarFromPoint X).obj R ⟶ B)
    (h : ∀ (S : Profinite.{u}) (x : R.obj.obj (op S)),
      f.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app R).hom.app (op S) x) =
        g.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app R).hom.app (op S) x)) : f = g := by
  apply ((sfbIntegralPointAdjunction X).homEquiv _ _).injective
  ext S x
  exact h S.unop x

private theorem point_unit_map
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    (f : R ⟶ T) (S : Profinite.{u}) (x : R.obj.obj (op S)) :
    ((upperStarFromPoint X).map f).hom.app (op ((profiniteToProEtOf X).obj S))
        (((sfbIntegralPointAdjunction X).unit.app R).hom.app (op S) x) =
      (((sfbIntegralPointAdjunction X).unit.app T).hom.app (op S)
        (f.hom.app (op S) x)) := by
  have h := (sfbIntegralPointAdjunction X).unit.naturality f
  exact (congrArg (fun k : R ⟶ (sfbPullbackFromPointRightAdjoint X).obj
      ((upperStarFromPoint X).obj T) ↦ k.hom.app (op S) x) h).symm

private theorem integral_projection_back_private (n : ℕ)
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
    (j : sfbIntegralProfinite l E ≅ c.pt)
    (hq : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
      (j.hom ≫ c.π.app (op n)) x =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    (hn : ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E),
      (sfbIntegralFiniteRepresentation l E X a n).hom.app
          (op ((profiniteToProEtOf X).obj S))
        ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
          (op ((profiniteToProEtOf X).obj S))
          (e.hom.hom.app (op ((profiniteToProEtOf X).obj S))
            (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
              (op S) (ULift.up g.hom.hom)))) =
        ULift.up ((profiniteToProEtOf X).map (g ≫ j.hom ≫ c.π.app (op n)))) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    let := DerivedNakayama.quotientDiscrete l E (n + 1)
    (upperStarFromPoint X).map
      ((integerPointIso l E).inv ≫ DerivedNakayama.reductionRing l E (n + 1)) ≫
      finiteBack X (Padic.coefficientExtensionRing l E (n + 1)) a =
    e.hom ≫ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (limit.π (integralCoefficientSheafSystem l E X) (op n)) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let := DerivedNakayama.quotientDiscrete l E (n + 1)
  apply point_hom_ext X
  intro S f
  change (finiteBack X (Padic.coefficientExtensionRing l E (n + 1)) a).hom.app _
    (((upperStarFromPoint X).map
      ((integerPointIso l E).inv ≫ DerivedNakayama.reductionRing l E (n + 1))).hom.app _
        (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) f)) = _
  refine (congrArg ((finiteBack X
    (Padic.coefficientExtensionRing l E (n + 1)) a).hom.app
      (op ((profiniteToProEtOf X).obj S)))
        (point_unit_map X
          ((integerPointIso l E).inv ≫ DerivedNakayama.reductionRing l E (n + 1)) S f)).trans ?_
  refine (finiteBack_unit X (Padic.coefficientExtensionRing l E (n + 1)) a S _).trans ?_
  let g : S ⟶ sfbIntegralProfinite l E := ConcreteCategory.ofHom f.down
  have ht := hn S g
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let V := op ((profiniteToProEtOf X).obj S)
  let z := ((DerivedNakayama.reductionRing l E (n + 1)).hom.app (op S))
    (((integerPointIso l E).inv.hom.app (op S)) f)
  let k := finiteFunction B S z.down
  apply ((finiteRepresentation X a B).app V).toEquiv.injective
  change (finiteRepresentation X a B).hom.app V
      (finiteRingSection X a B S k) = _
  have hk : finiteRingSection X a B S k =
      (finiteRepresentation X a B).inv.app V
        (ULift.up ((profiniteToProEtOf X).map k)) := rfl
  rw [hk, (finiteRepresentation X a B).inv_hom_id_app_apply]
  refine Eq.trans ?_ ht.symm
  apply congrArg ULift.up
  apply congrArg (fun k ↦ (profiniteToProEtOf X).map k)
  apply ConcreteCategory.hom_ext
  intro x
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    ((((integerPointIso l E).inv.hom.app (op S)) f).down x) =
      (g ≫ j.hom ≫ c.π.app (op n)) x
  exact (hq n (g x)).symm

/-- Public export of the private `integral_projection_back_private`
(used by `import all` importers; linter.privateModule). -/
alias integral_projection_back := integral_projection_back_private

end AlgebraicGeometry.ProEtale.IntegralPresentation
