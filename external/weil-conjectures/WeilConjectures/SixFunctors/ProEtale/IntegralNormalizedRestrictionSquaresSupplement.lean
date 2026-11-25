/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Encoding.IntegralPresentationEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Category.Profinite.AsLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientTerminalSupplement
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import Mathlib.Order.CompletePartialOrder

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

local instance : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _

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

section FiniteRingSection
/-! Local copies of the private finite-ring-section API of
`WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap`. -/

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem constantRing_unit {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify J (Type (u + 1))]
    [J.HasSheafCompose (forget CommRingCat.{u + 1})]
    [J.PreservesSheafification (forget CommRingCat.{u + 1})] (R : Type (u + 1)) [CommRing R]
    (V : Cᵒᵖ) (r : R) :
    ((constantCommuteCompose J (forget CommRingCat.{u + 1})).app
      (CommRingCat.of R)).hom.hom.app V
        ((toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app V r) =
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj R)).app V r := by
  have h := sheafComposeIso_inv_fac J
    (forget CommRingCat.{u + 1}) ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))
  have h' : Functor.whiskerRight (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) (forget CommRingCat.{u + 1}) ≫
      ((constantCommuteCompose J
        (forget CommRingCat.{u + 1})).hom.app (CommRingCat.of R)).hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj R) := by
    rw [constantCommuteCompose_hom_app_hom]
    set_option backward.isDefEq.respectTransparency false in
      rw [← Category.assoc, h, ← toSheafify_naturality]
    rfl
  exact congrArg (fun t ↦ t.app V r) h'

private theorem constantRing_binary {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify J (Type (u + 1))]
    [J.HasSheafCompose (forget CommRingCat.{u + 1})]
    [J.PreservesSheafification (forget CommRingCat.{u + 1})] (R : Type (u + 1)) [CommRing R]
    (V : Cᵒᵖ) (B₀ : Type (u + 1)) (p q : B₀ → R)
    (b : ((constantSheaf J
      (Type (u + 1))).obj B₀).obj.obj V)
    (opR : R → R → R)
    (opS : ∀ W : Cᵒᵖ,
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.obj W →
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.obj W →
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.obj W)
    (hnat : ∀ {W Z : Cᵒᵖ} (f : W ⟶ Z) x y,
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.map f (opS W x y) =
      opS Z (((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.map f x)
        (((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.map f y))
    (hu : ∀ W x y, (toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W (opR x y) =
      opS W ((toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W x)
        ((toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W y)) :
    let F := constantSheaf J (Type (u + 1))
    let k := (constantCommuteCompose J
      (forget CommRingCat.{u + 1})).app (CommRingCat.of R)
    k.inv.hom.app V ((F.map (TypeCat.ofHom (fun b : B₀ ↦ opR (p b) (q b)))).hom.app V b) =
      opS V (k.inv.hom.app V ((F.map (TypeCat.ofHom p)).hom.app V b))
        (k.inv.hom.app V ((F.map (TypeCat.ofHom q)).hom.app V b)) := by
  intro F k
  let P := (Functor.const Cᵒᵖ).obj B₀
  let B := (constantSheaf J CommRingCat.{u + 1}).obj
    (CommRingCat.of R)
  have hunit (W : Cᵒᵖ) (r : R) :
      k.inv.hom.app W ((toSheafify J
        ((Functor.const Cᵒᵖ).obj R)).app W r) =
        (toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W r := by
    have h := congrArg (fun z ↦ k.inv.hom.app W z) (constantRing_unit.{u} J R W r)
    exact h.symm.trans
      (((sheafToPresheaf J (Type (u + 1))).mapIso k
        ).hom_inv_id_app_apply W _)
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose _ (forget CommRingCat.{u + 1})).obj B).property).isSeparated _
      (Presheaf.imageSieve_mem J (toSheafify _ P) b)).ext
  rintro W f ⟨r, hr⟩
  change (toSheafify J P).app (op W) r =
    (F.obj B₀).obj.map f.op b at hr
  change B.obj.map f.op _ = B.obj.map f.op _
  set_option backward.isDefEq.respectTransparency false in
    rw [hnat]
  have hres (g : B₀ → R) :
      B.obj.map f.op (k.inv.hom.app V ((F.map (TypeCat.ofHom g)).hom.app V b)) =
        (toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app (op W) (g r) := by
    have h₁ := NatTrans.naturality_apply k.inv.hom f.op
      ((F.map (TypeCat.ofHom g)).hom.app V b)
    have h₂ := NatTrans.naturality_apply (F.map (TypeCat.ofHom g)).hom f.op b
    change k.inv.hom.app (op W)
        ((F.obj R).obj.map f.op ((F.map (TypeCat.ofHom g)).hom.app V b)) =
      B.obj.map f.op (k.inv.hom.app V ((F.map (TypeCat.ofHom g)).hom.app V b)) at h₁
    change (F.map (TypeCat.ofHom g)).hom.app (op W)
        ((F.obj B₀).obj.map f.op b) =
      (F.obj R).obj.map f.op ((F.map (TypeCat.ofHom g)).hom.app V b) at h₂
    rw [← h₁, ← h₂, ← hr]
    have h₃ := congrArg (fun t ↦ t.app (op W) r)
      (toSheafify_naturality J
        ((Functor.const Cᵒᵖ).map (TypeCat.ofHom g)))
    change (toSheafify J
        ((Functor.const Cᵒᵖ).obj R)).app (op W) (g r) =
      (F.map (TypeCat.ofHom g)).hom.app _ ((toSheafify _ P).app _ r) at h₃
    rw [← h₃, hunit]
  rw [hres, hres, hres]
  exact hu _ _ _

private theorem constantRing_const {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify J (Type (u + 1))]
    [J.HasSheafCompose (forget CommRingCat.{u + 1})]
    [J.PreservesSheafification (forget CommRingCat.{u + 1})] (R : Type (u + 1))
    [CommRing R] (V : Cᵒᵖ) (B₀ : Type (u + 1)) (r : R)
    (b : ((constantSheaf J
      (Type (u + 1))).obj B₀).obj.obj V) :
    let F := constantSheaf J (Type (u + 1))
    let k := (constantCommuteCompose J
      (forget CommRingCat.{u + 1})).app (CommRingCat.of R)
    k.inv.hom.app V ((F.map (TypeCat.ofHom (fun _ : B₀ ↦ r))).hom.app V b) =
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app V r := by
  exact constantRing_binary.{u} J R V B₀ (fun _ ↦ r) (fun _ ↦ r) b
    (fun _ _ ↦ r)
    (fun W _ _ ↦ (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W r)
    (by
      intro W Z f x y
      change (sheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).map f _ = _
      exact (NatTrans.naturality_apply
        (toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) f r).symm)
    (by intro W x y; rfl)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def finiteLabelSection (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : FintypeCat.{u}) (V : X.ProEtᵒᵖ)
    (f : V.unop ⟶ (profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj R)) :
    ((sfbFiniteConstantSets X).obj R).obj V :=
  (a.inv.app R).app V (ULift.up f)

private theorem finiteLabelSection_map (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    {R T : FintypeCat.{u}} (b : R ⟶ T) (V : X.ProEtᵒᵖ)
    (f : V.unop ⟶ (profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj R)) :
    ((sfbFiniteConstantSets X).map b).app V (finiteLabelSection X a R V f) =
      finiteLabelSection X a T V
        (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map b)) := by
  exact (congrArg (fun t ↦ t.app V (ULift.up f)) (a.inv.naturality b)).symm

private theorem finiteRing_binary (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R]
    (V : X.ProEtᵒᵖ)
    (f : V.unop ⟶ (profiniteToProEtOf X).obj
      (FintypeCat.toProfinite.obj (FintypeCat.of (R × R))))
    (opR : R → R → R)
    (opS : ∀ W : X.ProEtᵒᵖ,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W)
    (hnat : ∀ {W Z : X.ProEtᵒᵖ} (g : W ⟶ Z) x y,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map g (opS W x y) =
      opS Z (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map g x)
        (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map g y))
    (hu : ∀ W x y, (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W
          (ULift.up (opR x.down y.down)) =
      opS W ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W x)
        ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W y)) :
    let k := (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget CommRingCat.{u + 1})).app (CommRingCat.of (ULift.{u + 1} R))
    k.inv.hom.app V (finiteLabelSection X a (FintypeCat.of R) V
      (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map
        (FintypeCat.homMk (fun p : R × R ↦ opR p.1 p.2))))) =
      opS V (k.inv.hom.app V (finiteLabelSection X a (FintypeCat.of R) V
        (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map
          (FintypeCat.homMk Prod.fst)))))
        (k.inv.hom.app V (finiteLabelSection X a (FintypeCat.of R) V
          (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map
            (FintypeCat.homMk Prod.snd))))) := by
  intro k
  rw [← finiteLabelSection_map, ← finiteLabelSection_map, ← finiteLabelSection_map]
  exact constantRing_binary.{u} (Scheme.ProEt.topology X) (ULift.{u + 1} R) V
    (ULift.{u + 1} (R × R))
    (fun p ↦ ULift.up p.down.1) (fun p ↦ ULift.up p.down.2)
    (finiteLabelSection X a (FintypeCat.of (R × R)) V f)
    (fun x y ↦ ULift.up (opR x.down y.down)) opS hnat hu

private noncomputable def finitePair (S : Profinite.{u}) (R : FintypeCat.{u})
    (f g : S ⟶ FintypeCat.toProfinite.obj R) :
    S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of (R × R)) := by
  letI := FintypeCat.botTopology R
  letI := FintypeCat.discreteTopology R
  let h : C(S, R × R) :=
    ⟨fun s ↦ (f s, g s), f.hom.hom.continuous.prodMk g.hom.hom.continuous⟩
  have htop : (inferInstance : TopologicalSpace (R × R)) = ⊥ := DiscreteTopology.eq_bot
  exact ConcreteCategory.ofHom
    (show C(S, FintypeCat.toProfinite.obj (FintypeCat.of (R × R))) from
      ⟨fun s ↦ (f s, g s), by
        change @Continuous _ (R × R) _ ⊥ (fun s ↦ (f s, g s))
        rw [← htop]
        exact h.continuous⟩)

private noncomputable def finiteRingSection (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (S : Profinite.{u})
    (f : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of R)) :
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} R))).obj.obj
        (op ((profiniteToProEtOf X).obj S)) :=
  (((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget CommRingCat.{u + 1})).app (CommRingCat.of (ULift.{u + 1} R))).inv.hom.app
      (op ((profiniteToProEtOf X).obj S)))
    (finiteLabelSection X a (FintypeCat.of R) (op ((profiniteToProEtOf X).obj S))
      ((profiniteToProEtOf X).map f))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] finiteRingSection profiniteToProEtOf

private theorem finiteRingSection_binary (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (S : Profinite.{u})
    (f g h : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of R))
    (opR : R → R → R) (hh : ∀ s, h s = opR (f s) (g s))
    (opS : ∀ W : X.ProEtᵒᵖ,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W)
    (hnat : ∀ {W Z : X.ProEtᵒᵖ} (q : W ⟶ Z) x y,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map q (opS W x y) =
      opS Z (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map q x)
        (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map q y))
    (hu : ∀ W x y, (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W
          (ULift.up (opR x.down y.down)) =
      opS W ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W x)
        ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W y)) :
    finiteRingSection X a R S h =
      opS (op ((profiniteToProEtOf X).obj S))
        (finiteRingSection X a R S f) (finiteRingSection X a R S g) := by
  let U := profiniteToProEtOf X
  let pair := finitePair S (FintypeCat.of R) f g
  have hfst : pair ≫ FintypeCat.toProfinite.map (FintypeCat.homMk Prod.fst) = f := by
    ext s
    rfl
  have hsnd : pair ≫ FintypeCat.toProfinite.map (FintypeCat.homMk Prod.snd) = g := by
    ext s
    rfl
  have hop : pair ≫ FintypeCat.toProfinite.map
      (FintypeCat.homMk (fun p : R × R ↦ opR p.1 p.2)) = h := by
    ext s
    exact (hh s).symm
  have ht := finiteRing_binary X a R (op (U.obj S)) (U.map pair) opR opS hnat hu
  have hf' : U.map pair ≫ U.map
      (FintypeCat.toProfinite.map (FintypeCat.homMk Prod.fst)) = U.map f :=
    (U.map_comp _ _).symm.trans (congrArg U.map hfst)
  have hg' : U.map pair ≫ U.map
      (FintypeCat.toProfinite.map (FintypeCat.homMk Prod.snd)) = U.map g :=
    (U.map_comp _ _).symm.trans (congrArg U.map hsnd)
  have hh' : U.map pair ≫ U.map
      (FintypeCat.toProfinite.map (FintypeCat.homMk
        (fun p : R × R ↦ opR p.1 p.2))) = U.map h :=
    (U.map_comp _ _).symm.trans (congrArg U.map hop)
  dsimp only [U] at hf' hg' hh' ht
  simp only [hf', hg', hh'] at ht
  unfold finiteRingSection
  exact ht

private theorem finiteRingSection_const (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (S : Profinite.{u})
    (f : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of R)) (r : R)
    (hf : ∀ s, f s = r) :
    finiteRingSection X a R S f =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app
          (op ((profiniteToProEtOf X).obj S)) (ULift.up r) := by
  let b : FintypeCat.of R ⟶ FintypeCat.of R := FintypeCat.homMk (fun _ ↦ r)
  have hcomp : f ≫ FintypeCat.toProfinite.map b = f := by
    ext s
    exact (hf s).symm
  have hm := finiteLabelSection_map X a b (op ((profiniteToProEtOf X).obj S))
    ((profiniteToProEtOf X).map f)
  rw [← Functor.map_comp, hcomp] at hm
  unfold finiteRingSection
  rw [← hm]
  exact constantRing_const.{u} (Scheme.ProEt.topology X) (ULift.{u + 1} R) _
    (ULift.{u + 1} R) (ULift.up r) _

set_option backward.isDefEq.respectTransparency false
end FiniteRingSection

private theorem pointAdj_map_app (X : Scheme.{u})
    {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (t : F ⟶ G)
    (S : Profinite.{u}) :
    ((sfbPullbackFromPointRightAdjoint X).map t).hom.app (op S) =
      t.hom.app (op ((profiniteToProEtOf X).obj S)) := rfl

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

private theorem finiteBack_ringIso
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

private def reconstructedCommRingIso
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅ R := by
  let J := Scheme.ProEt.topology X
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R₀
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj A =
      R₀.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R₀.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  apply (fullyFaithfulSheafToPresheaf J CommRingCat.{u + 1}).preimageIso
  refine NatIso.ofComponents (fun Z ↦ ?_) (fun f ↦ ?_)
  · let RZ : CommRingCat.{u + 1} :=
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A).obj.obj Z
    let eZ : RZ ≃+* R.obj.obj Z :=
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_mul' := by
          intro a b
          change (((sheafToPresheaf J Ab.{u + 1}).monObjObj A).mul.app Z).hom
            (a ⊗ₜ[ℤ] b) = (show R₀.obj.obj Z from a) * (show R₀.obj.obj Z from b)
          have hm := congrArg (fun m : MonObj A.obj ↦ m.mul) hmon
          rw [hm]
          rfl }
    exact @RingEquiv.toCommRingCatIso RZ (R.obj.obj Z) _ _ eZ
  · ext a
    rfl

private def sectionRingIso
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : R ≅ S) [IsMonHom e.hom] [IsMonHom e.inv] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S where
  hom := CondensedRing.sectionRingMap X e.hom
  inv := CondensedRing.sectionRingMap X e.inv
  hom_inv_id := by
    ext V x
    exact congrArg (fun f : R ⟶ R ↦ f.hom.app V x) e.hom_inv_id
  inv_hom_id := by
    ext V x
    exact congrArg (fun f : S ⟶ S ↦ f.hom.app V x) e.inv_hom_id

private theorem sectionRingComparison
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (Q : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Q))]
    (b : R ≅ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Q))
    [IsMonHom b.hom] [IsMonHom b.inv] :
    ∃ α : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R ≅ Q,
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map α.hom = b.hom := by
  let α := sectionRingIso X b ≪≫ reconstructedCommRingIso X Q
  refine ⟨α, ?_⟩
  ext V x
  rfl

private theorem integralRingComparison
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    ∃ α : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.ring l E X) ≅ completedIntegralCommRingSheafUnrestricted l E X,
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map α.hom =
        (upperStarFromPoint X).map (integerPointIso l E).hom ≫ e.hom := by
  let b : AdicCompletion.ring l E X ≅ sfbCompletedIntegersAb l E X :=
    (upperStarFromPoint X).mapIso (integerPointIso l E) ≪≫ e
  let : IsMonHom b.hom := by
    change IsMonHom ((upperStarFromPoint X).map (integerPointIso l E).hom ≫ e.hom)
    infer_instance
  let : IsMonHom b.inv := by
    change IsMonHom (e.inv ≫ (upperStarFromPoint X).map (integerPointIso l E).inv)
    infer_instance
  let : IsCommMonObj (sfbCompletedIntegersAb l E X) :=
    Sheaf.isCommMonObj_sheafCompose_obj (Scheme.ProEt.topology X)
      (completedIntegralCoefficientSheafUnrestricted l E X) (fun U a b ↦ by
        let := completedIntegralCoefficientCommRingUnrestricted l E X U
        exact mul_comm a b)
  let : IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (completedIntegralCommRingSheafUnrestricted l E X))) := inferInstanceAs
              (IsCommMonObj (sfbCompletedIntegersAb l E X))
  obtain ⟨α, hα⟩ := sectionRingComparison X
    (completedIntegralCommRingSheafUnrestricted l E X) b
  exact ⟨α, hα⟩

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

private theorem integral_projection_back (n : ℕ)
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

private theorem rotate_square
    {C : Type*} [Category C] {A B C₀ D : C}
    (α : A ≅ B) (c : C₀ ≅ D) (q : A ⟶ D) (π : B ⟶ C₀)
    (h : q ≫ c.inv = α.hom ≫ π) : α.inv ≫ q = π ≫ c.hom := by
  apply (cancel_epi α.hom).mp
  apply (cancel_mono c.inv).mp
  simpa only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

private theorem normalizedRingComparison :
    ∃ α : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (AdicCompletion.ring l E X) ≅
          completedIntegralCommRingSheafUnrestricted l E X,
      ∀ n : ℕ,
        letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
        ∀ e : FiniteDiscreteOrdinary.Encoding
            (Padic.coefficientExtensionRing l E (n + 1)) X,
          α.inv ≫ CondensedRing.sectionRingMap X (AdicCompletion.quotient l E X n) =
            completedIntegralCommRingProjectionUnrestricted l E X n ≫ e.ringIso.hom := by
  obtain ⟨a, c, j, hq, _, _, _, _, e, ⟨he, hei, hn⟩, _⟩ :=
    sfb_integral_coefficient_limit l E X
  let := he
  let := hei
  obtain ⟨α, hα⟩ := integralRingComparison l E X e
  refine ⟨α, fun n ↦ ?_⟩
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro en
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let := DerivedNakayama.quotientDiscrete l E (n + 1)
  have hb := integral_projection_back l E X n a c j hq e (fun S g ↦ hn S g n)
  apply rotate_square α en.ringIso
  let F := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})
  apply F.map_injective
  rw [F.map_comp, F.map_comp, hα, finiteBack_ringIso X _ a en]
  have hh := congrArg (fun f ↦ (upperStarFromPoint X).map
    (integerPointIso l E).hom ≫ f) hb
  have hcancel : (upperStarFromPoint X).map (integerPointIso l E).hom ≫
      (upperStarFromPoint X).map
        ((integerPointIso l E).inv ≫ DerivedNakayama.reductionRing l E (n + 1)) =
      (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1)) := by
    rw [← Functor.map_comp, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hcancel] at hh
  change (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1)) ≫
    finiteBack X (Padic.coefficientExtensionRing l E (n + 1)) a = _
  exact hh

private def restrictionRoundTrip
    {C : Type uSite} [Category.{vSite} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{uRing}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{uModule} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{uModule} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle
    {C : Type uSite} [Category.{vSite} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{uRing}} (c : R ≅ S) (M : SheafOfModules.{uModule} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private def restrictionEquivalence
    {C : Type uSite} [Category.{vSite} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{uRing}} (c : R ≅ S) :
    SheafOfModules.{uModule} S ≌ SheafOfModules.{uModule} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private def scalarRestrictionSquare
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S T U : Sheaf J RingCat.{u + 1}}
    (q : R ⟶ S) (t : T ⟶ R) (c : U ⟶ S) (π : T ⟶ U)
    (h : t ≫ q = π ≫ c) :
    SheafOfModules.restrictScalars q ⋙ SheafOfModules.restrictScalars t ≅
      SheafOfModules.restrictScalars c ⋙ SheafOfModules.restrictScalars π := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      have hh := congrArg (fun f : T ⟶ S ↦ f.hom.app V r) h
      let L := M.val.obj V
      change (c.hom.app V (π.hom.app V r)) • (show L from m) =
        (q.hom.app V (t.hom.app V r)) • (show L from m)
      exact congrArg (fun z : S.obj.obj V ↦ z • (show L from m)) hh.symm
    · intro V W f
      ext x
      rfl
  · intro M N f
    ext V x
    rfl

private def scalarSquare (n : ℕ) (A : Encoding l E X) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X,
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map A.ringIso.inv ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (CondensedRing.sectionRingMap X (AdicCompletion.quotient l E X n)) =
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.ringIso.hom →
    (Mod.comap (AdicCompletion.quotient l E X n) ⋙
      ((InternalAbelianSheafModule.sectionModuleEquivalence
        (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)).functor ⋙
          SheafOfModules.restrictScalars
            ((sheafCompose (Scheme.ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map A.ringIso.inv)) ≅
      FiniteDiscreteOrdinary.sectionEncoding _ X e.ringIso ⋙
        scalarReductionRestriction.{u, u} l E X n) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro e h
  let J := Scheme.ProEt.topology X
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let q := F.map (CondensedRing.sectionRingMap X (AdicCompletion.quotient l E X n))
  let t := F.map A.ringIso.inv
  let c := F.map e.ringIso.hom
  let π := F.map (completedIntegralCommRingProjectionUnrestricted l E X n)
  let a := CondensedRing.sectionModuleComapIso X (AdicCompletion.quotient l E X n)
  let s := scalarRestrictionSquare q t c π h
  let V := (InternalAbelianSheafModule.sectionModuleEquivalence J
    (AdicCompletion.finiteRing l E X n)).functor
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight a (SheafOfModules.restrictScalars t) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft V s ≪≫
        (Functor.associator _ _ _).symm

/-- The integral-limit comparison admits identity-on-sections finite restriction squares.
Source: blueprint integral-criterion-reductions, coefficient comparison; Stacks 06YY;
Bhatt--Scholze, the integral-limit coefficient identification
(blueprint: lem-pe-integral-normalized-restriction-squares).

Proof: reconstruct commutative section rings from the monoidal integral-limit comparison.
Its nth projection is the pulled-back quotient map. Use the normalized finite-discrete
encodings of each positive quotient. Section reconstruction followed by scalar transport
along the inverse integral comparison is an additive equivalence. On a finite-level module,
the two restricted scalar actions agree because the integral comparison followed by its nth
projection is the original quotient. The identity of its underlying abelian sheaf is therefore
linear in both directions and gives the square. Its naturality is the identity on every
module morphism. The displayed equation accounts for the recorded equalities of the concrete
section-action functors; no derived functor or completeness hypothesis is used. -/
theorem integral_completion_normalized_squares :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∃ (A : Encoding l E X) (e : ∀ n : ℕ,
      FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X)
      (a : ∀ n : ℕ,
      Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
        (e n).ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n),
      ∀ (n : ℕ) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)),
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
          ((a n).hom.app M) =
        (SheafOfModules.toSheaf
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
            (eqToIso (congrArg (fun F ↦ F.obj
              ((Mod.comap (AdicCompletion.quotient l E X n)).obj M)) A.functor_eq)).hom ≫
          (SheafOfModules.toSheaf (integralCoefficientSheaf.{u, u} l E X n)).map
            (eqToIso (congrArg (fun F ↦ F.obj M) (e n).ordinary_functor)).inv := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨α, hα⟩ := normalizedRingComparison l E X
  let J := Scheme.ProEt.topology X
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let m := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    J (AdicCompletion.ring l E X)).trans
      (restrictionEquivalence (F.mapIso α.symm))
  let : m.functor.Additive := by
    change ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      J (AdicCompletion.ring l E X)).functor ⋙
        SheafOfModules.restrictScalars (F.map α.inv)).Additive
    infer_instance
  let A : Encoding l E X := { ringIso := α, modules := m, functor_eq := rfl }
  have he (n : ℕ) : Nonempty (FiniteDiscreteOrdinary.Encoding
      (Padic.coefficientExtensionRing l E (n + 1)) X) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    let := DerivedNakayama.quotientDiscrete l E (n + 1)
    exact FiniteDiscreteOrdinary.encoding_exists _ X
  let e (n : ℕ) : FiniteDiscreteOrdinary.Encoding
      (Padic.coefficientExtensionRing l E (n + 1)) X := Classical.choice (he n)
  have hsq (n : ℕ) : F.map A.ringIso.inv ≫
      F.map (CondensedRing.sectionRingMap X (AdicCompletion.quotient l E X n)) =
        F.map (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
          F.map (e n).ringIso.hom := by
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (hα n (e n))).trans (F.map_comp _ _))
  let a (n : ℕ) : Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
      (e n).ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n :=
    Functor.isoWhiskerLeft _ (eqToIso A.functor_eq) ≪≫
      scalarSquare l E X n A (e n) (hsq n) ≪≫
        Functor.isoWhiskerRight (eqToIso (e n).ordinary_functor).symm
          (scalarReductionRestriction.{u, u} l E X n)
  refine ⟨A, e, a, ?_⟩
  intro n M
  dsimp only [a, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, Functor.map_comp]
  ext U x
  dsimp only [scalarSquare, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rfl

end AlgebraicGeometry.ProEtale.IntegralPresentation
