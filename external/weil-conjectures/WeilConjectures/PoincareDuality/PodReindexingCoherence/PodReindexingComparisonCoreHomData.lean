/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafHomComplexComparison

/-! Hom-side component data for the core reindexing comparison.
(blueprint: lem-pod-reindexing-comparison-core-hom-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  homComplexFunctor homComplexπ WeilConjectures.podReindexingCoefficient
  derivedInternalHomOfUniverses WeilConjectures.podReindexingHomModel

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

structure ComparisonCoreHomData {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) where
  chain : ∀ P I : K l E Y s,
    (podReindexingComplexFunctor l E g s).obj (hom l E Y s P I) ≅
      hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I)
  chain_projection : ∀ (P I : K l E Y s) (r p : ℤ) (U V : X.ProEt) (a : V ⟶ U)
    (f : ((hom l E Y s P I).X r).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj V))),
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) r p (p+r) rfl).val.app (op U)
        (((chain P I).hom.f r).val.app (op U) f)).app (op (Over.mk a))).hom x =
      (((proj l E Y s P I r p (p+r) rfl).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) f).app
          (op (Over.mk ((proEtaleIsoPostcompose g).map a)))).hom x
  derived : podReindexingDerivedHom l E Y s ⋙ podReindexingDerivedFunctor l E g s ≅
    ((podReindexingDerivedFunctor l E g s).op.prod (podReindexingDerivedFunctor l E g s)) ⋙
      podReindexingDerivedHom l E X s
  derived_model : ∀ (P I : K l E Y s) (hI : I.IsKInjective),
    ∃ hFI : CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I),
      derived.hom.app (op ((podReindexingQ l E Y s).obj P),
        (podReindexingQ l E Y s).obj I) =
      (podReindexingDerivedFunctor l E g s).map
        (@podReindexingHomModel l _ E _ _ _ Y s P I hI).hom ≫
      (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s P I) ≫
      (podReindexingQ l E X s).map (chain P I).hom ≫
      (@podReindexingHomModel l _ E _ _ _ X s
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) hFI).inv ≫
      ((podReindexingDerivedHom l E X s).mapIso
        (((podReindexingDerivedFactors l E g s).app P).op.prod
          ((podReindexingDerivedFactors l E g s).app I).symm)).hom

/-- The Hom-side fields can be chosen simultaneously.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX and 0A8X
(blueprint: lem-pod-reindexing-comparison-core-hom-data).
-/
theorem comparison_core_hom_data_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    Nonempty (ComparisonCoreHomData l E g s SX SY TX TY) := by
  let F := podReindexingFunctor l E g s
  have : PreservesLimitsOfSize.{0, 0} F :=
    (podReindexing_resolution_preservation.{u, 0, 0} l E g s).2.2.2.2.1
  obtain ⟨_, η, χ, δ, _, hη, hχ, _, _, hδ⟩ :=
    podReindexing_hom_resolution_model l E g s
  have hηnat : ∀ (M M' N N' : podReindexingModules l E Y s)
      (a : M' ⟶ M) (b : N ⟶ N'),
      F.map (SheafOfModules.homObjMap (R := podReindexingRing l E Y s) a b) ≫
          (η M' N').hom =
        (η M N).hom ≫ SheafOfModules.homObjMap (R := podReindexingRing l E X s)
          (F.map a) (F.map b) := by
    intro M M' N N' a b
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨U⟩ := U
    obtain ⟨⟨V, ⟨⟨⟩⟩, c⟩⟩ := V
    change (((η M' N').hom.val.app (op U)
      ((SheafOfModules.homObjMap a b).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) f)).app (op (Over.mk c))).hom x = _
    rw [hη]
    change (b.val.app (op ((proEtaleIsoPostcompose g).obj V))).hom
      ((f.app (op (Over.mk ((proEtaleIsoPostcompose g).map c)))).hom
        ((a.val.app (op ((proEtaleIsoPostcompose g).obj V))).hom x)) =
      (b.val.app (op ((proEtaleIsoPostcompose g).obj V))).hom
        ((((η M N).hom.val.app (op U) f).app (op (Over.mk c))).hom
          ((a.val.app (op ((proEtaleIsoPostcompose g).obj V))).hom x))
    rw [hη]
    rfl
  let h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := podReindexingRing l E Y s))
      ⋙ F ≅ (F.op.prod F) ⋙
        Functor.uncurry.obj (SheafOfModules.homFunctor (R := podReindexingRing l E X s)) :=
    NatIso.ofComponents (fun A ↦ η A.1.unop A.2) (by
      intro A B f
      simpa only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
        Functor.op_map, Quiver.Hom.unop_op, SheafOfModules.homFunctor_map_app,
        SheafOfModules.homFunctor_obj_map, ← Functor.map_comp,
        SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]
        using hηnat A.1.unop B.1.unop A.2 B.2 f.1.unop f.2)
  obtain ⟨chain, hchain⟩ := sheafHomComplexComparison.{u + 1, u, u, u + 1, u, u} F h
  have hmatch : ∀ (P I : K l E Y s) (hI : I.IsKInjective),
      (chain.app (op P, I)).hom = (χ P I hI).hom := by
    intro P I hI
    apply HomologicalComplex.hom_ext
    intro r
    apply homComplex_hom_ext
    intro p q hpq
    subst q
    exact (hchain P I r p (p+r) rfl).trans (hχ P I hI r p).symm
  refine ⟨{ chain := fun P I ↦ chain.app (op P, I)
            chain_projection := ?_
            derived := δ
            derived_model := ?_ }⟩
  · intro P I r p U V a f x
    have hc := hchain P I r p (p+r) rfl
    have he := congrArg (fun t ↦ ((t.val.app (op U) f).app (op (Over.mk a))).hom x) hc
    exact he.trans (hη (P.X p) (I.X (p+r)) U V a
      ((proj l E Y s P I r p (p+r) rfl).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) f) x)
  · intro P I hI
    simpa only [hmatch P I hI] using hδ P I hI

end WeilConjectures.PodReindexingCoherence
