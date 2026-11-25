/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.OrdinaryImmersionChart.OrdinaryImmersionChartModels
import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.SignedLineModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SignedLineSheafPullbackForgetComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerRepresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence

/-! Ordinary completed coefficient geometry, before passage to derived categories.

The coefficient comparison below follows the finite-tower representation argument at
`max u (t + 1)`, so the coefficient and scheme universes remain independent. Its
projection equations identify the resulting cone morphism with the recorded
`completedRingMap`. The general-universe module inverse-image comparison then
reduces left exactness to abelian inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OrdinaryImmersionChart

attribute [local semireducible] Rings

private instance setPullLimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (proEtaleBaseChange f) (Type (max u (t + 1))) (ProEt.topology Y)
        (ProEt.topology X)) := by
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
    AB5OfSize_of_univLE.{t, t + 1, max u (t + 1), max u (t + 1)} _
  infer_instance

private instance abPullLimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (proEtaleBaseChange f) AddCommGrpCat.{max u (t + 1)} (ProEt.topology Y)
        (ProEt.topology X)) := by
  let : HasColimitsOfSize.{t, t + 1} AddCommGrpCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : AB5OfSize.{t, t + 1} AddCommGrpCat.{max u (t + 1)} :=
    AB5OfSize_of_univLE.{t, t + 1, max u (t + 1), max u (t + 1)} _
  infer_instance

private instance ringForgetSheafification (Y : Scheme.{t}) :
    (ProEt.topology Y).PreservesSheafification
      (CategoryTheory.forget CommRingCat.{max u (t + 1)}) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let J := (equivSmallModel.{max u (t + 1)} Y.ProEt).inverse.inducedTopology
    (ProEt.topology Y)
  let : J.PreservesSheafification
      (CategoryTheory.forget CommRingCat.{max u (t + 1)}) := by
    dsimp only [J]
    exact GrothendieckTopology.instPreservesSheafification _ _
  exact GrothendieckTopology.PreservesSheafification.transport
    (ProEt.topology Y) J (equivSmallModel.{max u (t + 1)} Y.ProEt).inverse
    (Type (max u (t + 1))) (CategoryTheory.forget CommRingCat.{max u (t + 1)})

private instance abForgetSheafification (Y : Scheme.{t}) :
    (ProEt.topology Y).PreservesSheafification
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let J := (equivSmallModel.{max u (t + 1)} Y.ProEt).inverse.inducedTopology
    (ProEt.topology Y)
  let : J.PreservesSheafification
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) := by
    dsimp only [J]
    exact GrothendieckTopology.instPreservesSheafification _ _
  exact GrothendieckTopology.PreservesSheafification.transport
    (ProEt.topology Y) J (equivSmallModel.{max u (t + 1)} Y.ProEt).inverse
    (Type (max u (t + 1))) (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})

private noncomputable def finiteTowerLabels
    (Q : ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    ℕᵒᵖ ⥤ FintypeCat.{t} where
  obj n := FintypeCat.of (Shrink.{t} (Q.obj n))
  map {n m} a := FintypeCat.homMk fun x ↦
    equivShrink.{t} (Q.obj m) ((Q.map a) ((equivShrink.{t} (Q.obj n)).symm x))
  map_id n := by
    apply FintypeCat.hom_ext
    intro x
    change equivShrink.{t} (Q.obj n)
      ((Q.map (𝟙 n)) ((equivShrink.{t} (Q.obj n)).symm x)) = x
    simp
  map_comp {n m k} a b := by
    apply FintypeCat.hom_ext
    intro x
    change equivShrink.{t} (Q.obj k)
      ((Q.map (a ≫ b)) ((equivShrink.{t} (Q.obj n)).symm x)) =
        equivShrink.{t} (Q.obj k) ((Q.map b) ((equivShrink.{t} (Q.obj m)).symm
          (equivShrink.{t} (Q.obj m) ((Q.map a)
            ((equivShrink.{t} (Q.obj n)).symm x)))))
    simp

private noncomputable def finiteTowerLabelIso
    (Q : ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    finiteTowerLabels.{t, u} Q ⋙ CategoryTheory.forget FintypeCat.{t} ⋙
        uliftFunctor.{max u (t + 1), t} ≅ Q ⋙ CategoryTheory.forget CommRingCat.{max u (t + 1)} :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    (Equiv.ulift.trans (equivShrink.{t} (Q.obj n)).symm)) (by
      intro n m a
      ext x
      change (equivShrink.{t} (Q.obj m)).symm
        (equivShrink.{t} (Q.obj m)
          ((Q.map a) ((equivShrink.{t} (Q.obj n)).symm x.down))) = _
      simp only [Equiv.symm_apply_apply]
      rfl)

private instance liftSheafification (Y : Scheme.{t}) :
    (ProEt.topology Y).PreservesSheafification
      uliftFunctor.{max u (t + 1), t + 1} := by
  let J := ProEt.topology Y
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : J.WEqualsLocallyBijective (Type (max u (t + 1))) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  constructor
  intro P Q f hf
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  let g := Functor.whiskerRight f uliftFunctor.{max u (t + 1), t + 1}
  have : Presheaf.IsLocallyInjective J g := by
    constructor
    intro X x y h
    have hh : f.app X x.down = f.app X y.down := congrArg ULift.down h
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J f x.down y.down hh)
    intro W a ha
    exact ULift.ext ha
  have : Presheaf.IsLocallySurjective J g := by
    constructor
    intro X x
    apply J.superset_covering _ (Presheaf.imageSieve_mem J f x.down)
    intro W a ha
    obtain ⟨y, hy⟩ := ha
    exact ⟨ULift.up y, ULift.ext hy⟩
  exact J.W_of_isLocallyBijective g

private noncomputable def liftedYoneda (Y : Scheme.{t}) :
    (ProEt.topology Y).uliftYoneda.{t + 1} ⋙
        sheafCompose (ProEt.topology Y) uliftFunctor.{max u (t + 1), t + 1} ≅
      (ProEt.topology Y).uliftYoneda.{max u (t + 1)} :=
  NatIso.ofComponents (fun X ↦
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun V ↦ Equiv.toIso
        (Equiv.ulift.trans (Equiv.ulift.trans Equiv.ulift.symm)))))

private noncomputable def liftedLabels :
    uliftFunctor.{t + 1, t} ⋙ uliftFunctor.{max u (t + 1), t + 1} ≅
      uliftFunctor.{max u (t + 1), t} :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso
    (Equiv.ulift.trans (Equiv.ulift.trans Equiv.ulift.symm)))

private noncomputable def finiteRepresentable (Y : Scheme.{t}) :
    CategoryTheory.forget FintypeCat.{t} ⋙ uliftFunctor.{max u (t + 1), t} ⋙
        constantSheaf (ProEt.topology Y) (Type (max u (t + 1))) ≅
      proEtaleFiniteCopiesFunctor Y ⋙
        (ProEt.topology Y).uliftYoneda.{max u (t + 1)} := by
  let J := ProEt.topology Y
  let L := uliftFunctor.{max u (t + 1), t + 1}
  let e := proEtaleFiniteConstantRepresentableIso Y
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (CategoryTheory.forget FintypeCat.{t})
        liftedLabels.{t, u}.symm) (constantSheaf J (Type (max u (t + 1)))) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.forget FintypeCat.{t} ⋙ uliftFunctor.{t + 1, t})
      (constantCommuteCompose J L).symm ≪≫
    Functor.isoWhiskerRight e (sheafCompose J L) ≪≫
    Functor.isoWhiskerLeft (proEtaleFiniteCopiesFunctor Y) (liftedYoneda.{t, u} Y)

private theorem finiteTowerRepresentation {X Y : Scheme.{t}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    ∃ (D : ℕᵒᵖ ⥤ Y.ProEt) (c : Cone D),
      Nonempty (IsLimit c) ∧ Nonempty (IsLimit ((proEtaleBaseChange f).mapCone c)) ∧
      Nonempty (D ⋙ (ProEt.topology Y).uliftYoneda.{max u (t + 1)} ≅
        Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)} ⋙
          sheafCompose (ProEt.topology Y)
            (CategoryTheory.forget CommRingCat.{max u (t + 1)})) := by
  let P := finiteTowerLabels.{t, u} Q ⋙ FintypeCat.toProfinite
  let G := AlgebraicGeometry.ProEtale.profiniteToProEtOf Y
  let c := G.mapCone (limit.cone P)
  let : PreservesLimit P (G ⋙ ProEt.forget Y) := testObject_preservesLimit Y P
  have hc : IsLimit c :=
    isLimitOfReflects (ProEt.forget Y) (isLimitOfPreserves (G ⋙ ProEt.forget Y) (limit.isLimit P))
  have hfc : IsLimit ((proEtaleBaseChange f).mapCone c) := by
    apply isLimitOfReflects (ProEt.forget X)
    exact isLimitOfPreserves ((G ⋙ ProEt.forget Y) ⋙ Over.pullback f) (limit.isLimit P)
  refine ⟨P ⋙ G, c, ⟨hc⟩, ⟨hfc⟩, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (finiteTowerLabels.{t, u} Q) (finiteTestObjectIso Y))
      (ProEt.topology Y).uliftYoneda.{max u (t + 1)} ≪≫
    Functor.isoWhiskerLeft (finiteTowerLabels.{t, u} Q) (finiteRepresentable Y).symm ≪≫
    Functor.isoWhiskerRight (finiteTowerLabelIso.{t, u} Q)
      (constantSheaf (ProEt.topology Y) (Type (max u (t + 1)))) ≪≫
    Functor.isoWhiskerLeft Q
      (constantCommuteCompose (ProEt.topology Y)
        (CategoryTheory.forget CommRingCat.{max u (t + 1)})).symm

private instance ringColimits :
    HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
  hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _

private instance ringForgetKan {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (CategoryTheory.forget CommRingCat.{max u (t + 1)}).PreservesLeftKanExtensions
      (proEtaleBaseChange f).op := by
  intro P
  let U := CategoryTheory.forget CommRingCat.{max u (t + 1)}
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : PreservesFilteredColimitsOfSize.{t, t + 1} U :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t, max u (t + 1)} _
  let : ∀ Z, Functor.PreservesPointwiseLeftKanExtensionAt U P
      (proEtaleBaseChange f).op Z := by intro Z; infer_instance
  infer_instance

private noncomputable def ringPullForget {X Y : Scheme.{t}} (f : X ⟶ Y) :
    completedRingPull.{t, u} f ⋙
        sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat) ≅
      sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat) ⋙
        Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange f)
          (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X) :=
  CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
      (CategoryTheory.forget CommRingCat.{max u (t + 1)})

private noncomputable def representableInverse {X Y : Scheme.{t}} (f : X ⟶ Y) :
    proEtaleBaseChange f ⋙ (ProEt.topology X).uliftYoneda.{max u (t + 1)} ≅
      (ProEt.topology Y).uliftYoneda.{max u (t + 1)} ⋙
        Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange f)
          (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X) := by
  let e := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u (t + 1)}
    (proEtaleBaseChange f)
  exact Functor.isoWhiskerLeft
      (proEtaleBaseChange f ⋙ (ProEt.topology X).uliftYoneda.{max u (t + 1)})
      (sheafificationNatIso (ProEt.topology X) (Type (max u (t + 1)))) ≪≫
    Functor.isoWhiskerRight e (presheafToSheaf (ProEt.topology X)
      (Type (max u (t + 1))))

private theorem finiteTowerPreserved {X Y : Scheme.{t}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    PreservesLimit (Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)})
      (completedRingPull.{t, u} f) := by
  obtain ⟨D, c, ⟨hc⟩, ⟨hfc⟩, ⟨e⟩⟩ := finiteTowerRepresentation f Q
  let F := proEtaleBaseChange f
  let Ly := (ProEt.topology Y).uliftYoneda.{max u (t + 1)}
  let Lx := (ProEt.topology X).uliftYoneda.{max u (t + 1)}
  let P := Functor.sheafPullbackConstruction.sheafPullback F (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)
  let Ry := sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{max u (t + 1)})
  let Rx := sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{max u (t + 1)})
  let S := Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}
  let : PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}) :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _
  let : PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}) :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _
  let : PreservesLimit D F := preservesLimit_of_preserves_limit_cone hc hfc
  let : PreservesLimit D (F ⋙ Lx) := inferInstance
  let : PreservesLimit D (Ly ⋙ P) := preservesLimit_of_natIso D (representableInverse f)
  let : PreservesLimit (D ⋙ Ly) P :=
    preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Ly hc)
      (isLimitOfPreserves (Ly ⋙ P) hc)
  let Iy := sheafToPresheaf (ProEt.topology Y) (Type (max u (t + 1)))
  let Ix := sheafToPresheaf (ProEt.topology X) (Type (max u (t + 1)))
  let : PreservesLimitsOfShape ℕᵒᵖ (Ry ⋙ Iy) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat)))
  let : PreservesLimitsOfShape ℕᵒᵖ Ry :=
    preservesLimitsOfShape_of_reflects_of_preserves Ry Iy
  let : PreservesLimitsOfShape ℕᵒᵖ (Rx ⋙ Ix) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat)))
  let : PreservesLimitsOfShape ℕᵒᵖ Rx :=
    preservesLimitsOfShape_of_reflects_of_preserves Rx Ix
  let : ReflectsLimitsOfShape ℕᵒᵖ Rx := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimit (S ⋙ Ry) P := preservesLimit_of_iso_diagram P e
  let : PreservesLimit S (Ry ⋙ P) := inferInstance
  let : PreservesLimit S (completedRingPull.{t, u} f ⋙ Rx) :=
    preservesLimit_of_natIso S (ringPullForget f).symm
  exact preservesLimit_of_reflects_of_preserves (completedRingPull.{t, u} f) Rx

private noncomputable def quotientTower (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)} :=
  Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (fun n ↦ CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

private noncomputable abbrev quotientDiagram (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{t}) :=
  quotientTower.{t, u} l E ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}

private noncomputable abbrev quotientForget (Y : Scheme.{t}) :=
  sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})

private theorem constantMapIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) : IsIso (completedRingConstantMap f A) := by
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let adjY := constantSheafAdj (ProEt.topology Y) CommRingCat.{max u (t + 1)} hT
  let adjX := constantSheafAdj (ProEt.topology X) CommRingCat.{max u (t + 1)} hGT
  let adj := (adjY.comp (completedRingAdj.{t, u} f)).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X) (op T))
  have he : completedRingConstantMap f A =
      (adj.leftAdjointUniq adjX).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (completedRingAdj.{t, u} f)).homEquiv _ _
      (completedRingConstantMap f A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((completedRingAdj.{t, u} f).homEquiv _ _
        (((completedRingAdj.{t, u} f).homEquiv _ _).symm
          (coefficientProEtaleDirectRingMap f A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{max u (t + 1)} hT).comp
      (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)})).homEquiv _ _
        (coefficientProEtaleDirectRingMap f A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{max u (t + 1)} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

private noncomputable def quotientDiagramForgetIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t}) :
    quotientDiagram l E Y ⋙ quotientForget.{t, u} Y ≅ integralCoefficientSheafSystem l E Y := by
  let a : quotientDiagram l E Y ⋙ quotientForget.{t, u} Y ⟶
      integralCoefficientSheafSystem l E Y :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [quotientDiagram, quotientTower, integralCoefficientSheafSystem,
        Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id,
        Category.id_comp]
      rfl)
  let (n : ℕᵒᵖ) : IsIso (a.app n) := by
    change IsIso (𝟙 (integralCoefficientSheaf l E Y n.unop))
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

private noncomputable def coefficientCone
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t}) :
    Cone (quotientDiagram l E Y) where
  pt := completedIntegralCommRingSheafUnrestricted l E Y
  π := NatTrans.ofOpSequence (completedIntegralCommRingProjectionUnrestricted l E Y) (by
    intro n
    apply (quotientForget.{t, u} Y).map_injective
    change 𝟙 _ ≫ limit.π (integralCoefficientSheafSystem l E Y) (op n) =
      limit.π _ (op (n + 1)) ≫ (quotientForget Y).map
        ((quotientDiagram l E Y).map (homOfLE (Nat.le_succ n)).op)
    simp only [quotientDiagram, quotientTower, Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
    simpa only [integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ, integralCoefficientSheafTransition,
      quotientForget] using
        (limit.w (integralCoefficientSheafSystem l E Y)
          (homOfLE (Nat.le_succ n)).op).symm)

private noncomputable def coefficientConeIsLimit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t}) :
    IsLimit (coefficientCone l E Y) := by
  let F := quotientForget.{t, u} Y
  let c := F.mapCone (coefficientCone l E Y)
  let e := quotientDiagramForgetIso l E Y
  have h : (Cone.postcompose e.hom).obj c ≅
      limit.cone (integralCoefficientSheafSystem l E Y) := by
    refine Cone.ext (Iso.refl _) ?_
    intro n
    change 𝟙 (completedIntegralCoefficientSheafUnrestricted l E Y) ≫
        limit.π (integralCoefficientSheafSystem l E Y) n =
      limit.π (integralCoefficientSheafSystem l E Y) n ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  apply isLimitOfReflects F
  exact (IsLimit.postcomposeHomEquiv e c)
    (IsLimit.ofIsoLimit (limit.isLimit _) h.symm)

private theorem completedCoefficientMapIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) : IsIso (completedRingMap l E f) := by
  let L := completedRingPull.{t, u} f
  let Q := quotientTower.{t, u} l E
  let (n : ℕᵒᵖ) : Finite (Q.obj n) := by
    let := Padic.finite_coefficientExtensionRing l E (n.unop + 1) (Nat.succ_le_succ (Nat.zero_le _))
    exact inferInstanceAs (Finite (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))
  let : PreservesLimit (quotientDiagram l E Y) L := finiteTowerPreserved f Q
  let a : quotientDiagram l E Y ⋙ L ⟶ quotientDiagram l E X :=
    { app n := completedRingConstantMap f (Q.obj n)
      naturality n m h := completedConstant_naturality f (Q.map h) }
  let (n : ℕᵒᵖ) : IsIso (a.app n) := constantMapIso f (Q.obj n)
  let : IsIso a := NatIso.isIso_of_isIso_app a
  let c := (Cone.postcompose a).obj (L.mapCone (coefficientCone l E Y))
  have hc : IsLimit c := (IsLimit.postcomposeHomEquiv (asIso a) _).symm
    (isLimitOfPreserves L (coefficientConeIsLimit l E Y))
  let m : c ⟶ coefficientCone l E X :=
    { hom := completedRingMap l E f
      w n := completedMap_projection l E f n.unop }
  let : IsIso m := hc.hom_isIso (coefficientConeIsLimit l E X) m
  exact inferInstanceAs (IsIso ((Cone.forget (quotientDiagram l E X)).map m))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary module pullback over the profinite completed coefficient ring is exact.
Source: Stacks Tags 03D2 and 04JC; profinite coefficient inverse image.
(blueprint: lem-tw-ordinary-completed-pullback-exact).

Proof. The finite quotient rings of the valuation ring are finite. The profinite
coefficient inverse-image theorem identifies the inverse image of their limit with
the limit of the inverse images. Its projection equations identify its comparison
with completedRingMap. Thus that structural map is invertible. Module inverse
image over the inverse-image ring is exact: its underlying abelian sheaf is the
exact abelian inverse image, and the forgetful functor reflects finite exactness.
The inverse-image comparison respects the ring adjunction units, so it gives the
unit presentation required by the general-universe module inverse-image theorem.
That theorem identifies the specified module pullback, after forgetting, with
abelian inverse image. Reflect its preservation of finite limits through module
forgetting and unfold the recorded pull. Finite colimits are supplied separately
by the adjunction adj. -/
theorem ordinaryCompletedPullbackExact {T W : Scheme.{t}} (g : T ⟶ W) :
    PreservesFiniteLimits (pull l E g) := by
  let F := proEtaleBaseChange g
  let J := ProEt.topology W
  let K := ProEt.topology T
  let U := CategoryTheory.forget CommRingCat.{max u (t + 1)}
  let O := completedIntegralCommRingSheafUnrestricted l E W
  let B := completedIntegralCommRingSheafUnrestricted l E T
  let c := completedRingMap l E g
  have hc : IsIso c := completedCoefficientMapIso l E g
  let := hc
  let : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  let : HasColimitsOfSize.{t, t + 1} AddCommGrpCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits _
  let : U.PreservesLeftKanExtensions F.op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{t, t + 1} U :=
      preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t, max u (t + 1)} _
    let : ∀ X, Functor.PreservesPointwiseLeftKanExtensionAt U P F.op X := by
      intro X
      infer_instance
    infer_instance
  let Ua := CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}
  let : Ua.PreservesLeftKanExtensions F.op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{t, t + 1} Ua :=
      preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t, max u (t + 1)} _
    let : ∀ X, Functor.PreservesPointwiseLeftKanExtensionAt Ua P F.op X := by
      intro X
      infer_instance
    infer_instance
  let e := CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso J K F U
  let d := (completedRingAdj.{t, u} g).homEquiv O B c
  let v := (sheafCompose J U).map d
  let ec : (sheafCompose K U).obj B ≅
      (Functor.sheafPullbackConstruction.sheafPullback F
        (Type (max u (t + 1))) J K).obj ((sheafCompose J U).obj O) :=
    ((sheafCompose K U).mapIso (asIso c)).symm ≪≫ e.app O
  have he : v ≫ (F.sheafPushforwardContinuous (Type (max u (t + 1))) J K).map ec.hom =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
        (Type (max u (t + 1))) J K).unit.app ((sheafCompose J U).obj O) := by
    have hu := CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso_unit
      J K F U O
    have hd : v = (sheafCompose J U).map ((completedRingAdj.{t, u} g).unit.app O) ≫
        (F.sheafPushforwardContinuous (Type (max u (t + 1))) J K).map
          ((sheafCompose K U).map c) := by
      rfl
    have hcc : (sheafCompose K U).map c ≫ ec.hom = e.hom.app O := by
      dsimp only [ec, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
      rw [← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
      rfl
    rw [hd, Category.assoc, ← Functor.map_comp, hcc]
    exact hu
  let pr : CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation
      (F := F) ((sheafCompose J (CategoryTheory.forget RingCat.{max u (t + 1)})).obj (Rings l E W))
      ((sheafCompose K (CategoryTheory.forget RingCat.{max u (t + 1)})).obj (Rings l E T)) :=
    { unit := v
      iso := ec
      equation := fun X x ↦ congrArg (fun q ↦ q.hom.app X x) he }
  let := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  let : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback F
        (Type (max u (t + 1))) J K) := by infer_instance
  obtain ⟨em, _⟩ :=
    SheafOfModules.SignedLinePullbackConstruction.inverseImage_underlying_of_ring_presentation
      (directRingMap l E g) pr rfl
  let : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback F
        AddCommGrpCat.{max u (t + 1)} J K) :=
    by infer_instance
  let : PreservesFiniteLimits (SheafOfModules.pullback (directRingMap l E g) ⋙
      SheafOfModules.toSheaf (Rings l E T)) := preservesFiniteLimits_of_natIso em.symm
  unfold pull
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (Rings l E T))

end WeilConjectures.OrdinaryImmersionChart
