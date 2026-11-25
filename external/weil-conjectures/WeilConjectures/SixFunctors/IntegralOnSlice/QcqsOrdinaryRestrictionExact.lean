/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryFiniteCoefficientMaps
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleImmersionAlgebraicLimitsOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedPullbackUnderlyingOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-! # Limit preservation for ordinary qcqs restriction

Source: Stacks Tags 09AA, 09BL and 03CO. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

private instance commRingWeakSheafify (Z : Scheme.{t}) :
    HasWeakSheafify (ProEt.topology Z) CommRingCat.{max u (t + 1)} :=
  (integralCoefficientRingSheafify.{t, u} Z).isRightAdjoint

private instance abelianWeakSheafify (Z : Scheme.{t}) :
    HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)} :=
  (integralCoefficientAbSheafify.{t, u} Z).isRightAdjoint

private theorem coefficientDirectMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (g : A ⟶ B) :
    coefficientProEtaleDirectRingMap f A ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map g) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map g ≫
        coefficientProEtaleDirectRingMap f B := by
  let a := sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _ (coefficientProEtaleDirectRingMap f A ≫ _) =
    a.homEquiv _ _ ((presheafToSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map
      ((Functor.const Y.ProEtᵒᵖ).map g) ≫ coefficientProEtaleDirectRingMap f B)
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left]
  change (a.homEquiv _ _ ((a.homEquiv _ _).symm _)) ≫ _ =
    ((Functor.const Y.ProEtᵒᵖ).map g) ≫
      (a.homEquiv _ _ ((a.homEquiv _ _).symm _))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify _ _ ≫ sheafifyMap _ ((Functor.const X.ProEtᵒᵖ).map g)) = _
  rw [← toSheafify_naturality]
  rfl

private theorem ordinaryFiniteRingMap_transition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ordinaryFiniteRingMap l E f (n + 1) ≫
        (ordinaryRingPush.{t, u} f).map (integralCoefficientSheafTransition l E X n) =
      integralCoefficientSheafTransition l E Y n ≫ ordinaryFiniteRingMap l E f n := by
  let H := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  exact congrArg H.map (coefficientDirectMap_naturality f
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))

private theorem ordinaryCoefficientMap_isIso_of_preservesLimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    [PreservesLimitsOfSize.{0, 0} (ordinaryRingInverse.{t, u} f)] :
    IsIso (ordinaryCoefficientMap l E f) := by
  let G := ordinaryRingPush.{t, u} f
  let L := ordinaryRingInverse.{t, u} f
  let a := Adjunction.ofIsRightAdjoint G
  let α : integralCoefficientSheafSystem l E Y ⋙ L ⟶
      integralCoefficientSheafSystem l E X :=
    NatTrans.ofOpSequence
      (fun n ↦ (a.homEquiv _ _).symm (ordinaryFiniteRingMap l E f n)) (by
        intro n
        simp only [Functor.comp_map, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        rw [← a.homEquiv_naturality_left_symm,
          ← a.homEquiv_naturality_right_symm]
        exact congrArg _ (ordinaryFiniteRingMap_transition l E f n).symm)
  have : ∀ n, IsIso (α.app n) := fun n ↦ ordinaryFiniteCoefficientMap_isIso l E f n.unop
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e := IsLimit.conePointsIsoOfNatIso
    (isLimitOfPreserves L (limit.isLimit (integralCoefficientSheafSystem l E Y)))
    (limit.isLimit (integralCoefficientSheafSystem l E X)) (asIso α)
  have he : ordinaryCoefficientMap l E f = e.hom := by
    apply limit.hom_ext
    intro n
    have hp : ordinaryCompletedRingMap l E f ≫
        G.map (limit.π (integralCoefficientSheafSystem l E X) n) =
        limit.π (integralCoefficientSheafSystem l E Y) n ≫
          ordinaryFiniteRingMap l E f n.unop :=
      (ordinaryCompletedRingMap_existsUnique l E f).exists.choose_spec n.unop
    calc
      _ = L.map (limit.π (integralCoefficientSheafSystem l E Y) n) ≫ α.app n := by
        change (a.homEquiv _ _).symm (ordinaryCompletedRingMap l E f) ≫
            limit.π (integralCoefficientSheafSystem l E X) n =
          L.map (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
            (a.homEquiv _ _).symm (ordinaryFiniteRingMap l E f n.unop)
        rw [← a.homEquiv_naturality_right_symm,
          hp, a.homEquiv_naturality_left_symm]
        rfl
      _ = _ := (IsLimit.conePointsIsoOfNatIso_hom_comp
        (isLimitOfPreserves L (limit.isLimit (integralCoefficientSheafSystem l E Y)))
        (limit.isLimit (integralCoefficientSheafSystem l E X)) (asIso α) n).symm
  rw [he]
  infer_instance

private abbrev abelianPush {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

private theorem abelianPush_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (abelianPush.{t, u} f).IsRightAdjoint := by
  let : HasColimitsOfSize.{t + 1, t + 1} AddCommGrpCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _
  let : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : LocallySmall.{t + 1} X.ProEt := ⟨fun _ _ ↦ inferInstance⟩
  have : ∀ V : X.ProEtᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange f).op V)
        AddCommGrpCat.{max u (t + 1)} := fun _ ↦
    hasColimitsOfShape_of_essentiallySmall.{t + 1} _ _
  have : ∀ F : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{max u (t + 1)},
      (proEtaleBaseChange f).op.HasLeftKanExtension F := fun _ ↦ inferInstance
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange f) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology Y) (ProEt.topology X)).isRightAdjoint

private theorem weaklyEtale_limits
    {D : Type*} [Category D] [HasLimitsOfSize.{0, 0} D]
    {X Y : Scheme.{t}} (f : X ⟶ Y) [WeaklyEtale f]
    (L : Sheaf (ProEt.topology Y) D ⥤ Sheaf (ProEt.topology X) D)
    (a : L ⊣ (proEtaleBaseChange f).sheafPushforwardContinuous D
      (ProEt.topology Y) (ProEt.topology X)) : PreservesLimitsOfSize.{0, 0} L := by
  let b := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) _root_.trivial).sheafPushforwardContinuous
      (E := D) (ProEt.topology X) (ProEt.topology Y)
  let U := MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{t})
    (inferInstance : WeaklyEtale f)
  let R := U.sheafPushforwardContinuous D (ProEt.topology X) (ProEt.topology Y)
  let : PreservesLimitsOfSize.{0, 0} (R ⋙ sheafToPresheaf (ProEt.topology X) D) :=
    inferInstanceAs (PreservesLimitsOfSize.{0, 0}
      (sheafToPresheaf (ProEt.topology Y) D ⋙
        (Functor.whiskeringLeft X.ProEtᵒᵖ Y.ProEtᵒᵖ D).obj U.op))
  let : PreservesLimitsOfSize.{0, 0} R :=
    preservesLimits_of_reflects_of_preserves R (sheafToPresheaf (ProEt.topology X) D)
  exact preservesLimits_of_natIso (a.leftAdjointUniq b).symm

private theorem composite_limits
    {D : Type*} [Category D]
    {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Lf : Sheaf (ProEt.topology Y) D ⥤ Sheaf (ProEt.topology X) D)
    (af : Lf ⊣ (proEtaleBaseChange f).sheafPushforwardContinuous D
      (ProEt.topology Y) (ProEt.topology X))
    (Lg : Sheaf (ProEt.topology Z) D ⥤ Sheaf (ProEt.topology Y) D)
    (ag : Lg ⊣ (proEtaleBaseChange g).sheafPushforwardContinuous D
      (ProEt.topology Z) (ProEt.topology Y))
    (L : Sheaf (ProEt.topology Z) D ⥤ Sheaf (ProEt.topology X) D)
    (a : L ⊣ (proEtaleBaseChange (f ≫ g)).sheafPushforwardContinuous D
      (ProEt.topology Z) (ProEt.topology X))
    [PreservesLimitsOfSize.{0, 0} Lf] [PreservesLimitsOfSize.{0, 0} Lg] :
    PreservesLimitsOfSize.{0, 0} L := by
  let e := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    D (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  exact preservesLimits_of_natIso (a.leftAdjointUniq ((ag.comp af).ofNatIsoRight e)).symm

private theorem moduleForget_limits {X : Scheme.{t}}
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}) :
    PreservesLimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{max u (t + 1)} R) := by
  let H := SheafOfModules.forget.{max u (t + 1)} R ⋙
    PresheafOfModules.toPresheaf.{max u (t + 1)} R.obj
  have hH : PreservesLimitsOfSize.{max u (t + 1), max u (t + 1)} H := by
    dsimp [H]
    infer_instance
  let : PreservesLimitsOfSize.{0, 0}
      (SheafOfModules.toSheaf.{max u (t + 1)} R ⋙ sheafToPresheaf _ _) :=
    @preservesSmallestLimits_of_preservesLimits _ _ _ _ H hH
  exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Ordinary restriction preserves all limits indexed by small categories, and its
specified completed coefficient map is invertible.

Source: Stacks Tags 09AA(1), 09BL, 09AE and 03CO; Bhatt--Scholze Lemma 6.5.8(1).
(blueprint: lem-fix-qcqs-ordinary-restriction-exact).
Proof: for an immersion inverse image on set sheaves preserves all limits. For a
weakly etale map it is slice restriction and also preserves all limits. Compose
the two inverse images, using uniqueness of adjoints to identify the composite
with the inverse image adjoint to the actual direct image of s ≫ i. The finite
coefficient maps are the constant-section isomorphisms and commute with every
quotient transition. Preservation of the inverse limit identifies their limit
with ordinaryCoefficientMap, by the finite-projection uniqueness of
ordinaryCompletedRingMap. Thus this map is invertible. Module pullback along an
invertible coefficient map is inverse image with its transported scalar action.
The conservative, limit-preserving underlying abelian sheaf functor identifies
its limits with the limits of inverse image. All constructions may be performed
on the coefficientProEtaleSiteModel and transported back, so site and coefficient
universes remain independent. No nonempty-source assumption is needed: over the
empty scheme the sheaf category and all its diagrams are terminal. -/
theorem qcqsOrdinaryRestrictionExact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace T] [QuasiSeparatedSpace T]
    (s : S ⟶ V) (i : V ⟶ T) [WeaklyEtale s] [IsImmersion i] :
    PreservesLimitsOfSize.{0, 0} (ordinaryPull l E (s ≫ i)) ∧
    IsIso (ordinaryCoefficientMap l E (s ≫ i)) := by
  let hf := abelianPush_isRightAdjoint.{t, u} s
  let hg := abelianPush_isRightAdjoint.{t, u} i
  let hc := abelianPush_isRightAdjoint.{t, u} (s ≫ i)
  let Bf := (abelianPush.{t, u} s).leftAdjoint
  let Bg := (abelianPush.{t, u} i).leftAdjoint
  let B := (abelianPush.{t, u} (s ≫ i)).leftAdjoint
  let af := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} s)
  let ag := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} i)
  let a := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} (s ≫ i))
  let rf := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} s)
  let rg := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} i)
  let rc := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} (s ≫ i))
  obtain ⟨hRg, hBg⟩ := proEtale_immersion_algebraicInverse_limits i
    (ordinaryRingInverse.{t, u} i) rg Bg ag
  let := hRg
  let := hBg
  let := weaklyEtale_limits s (ordinaryRingInverse.{t, u} s) rf
  let := weaklyEtale_limits s Bf af
  let := composite_limits s i (ordinaryRingInverse.{t, u} s) rf
    (ordinaryRingInverse.{t, u} i) rg (ordinaryRingInverse.{t, u} (s ≫ i)) rc
  let := composite_limits s i Bf af Bg ag B a
  have hcoeff := ordinaryCoefficientMap_isIso_of_preservesLimits l E (s ≫ i)
  let := hcoeff
  let R := completedIntegralCoefficientSheafUnrestricted l E T
  let A := completedIntegralCoefficientSheafUnrestricted l E S
  let F := ordinaryPull l E (s ≫ i)
  have : IsIso ((rc.homEquiv R A).symm (ordinaryCompletedRingMap l E (s ≫ i))) :=
    hcoeff
  obtain ⟨e⟩ := proEtale_ringedPullback_underlying_of_isIso (s ≫ i)
    (ordinaryRingInverse.{t, u} (s ≫ i)) rc B a R A
    (ordinaryCompletedRingMap l E (s ≫ i)) F (ordinaryAdjunction l E (s ≫ i))
  let := moduleForget_limits R
  let := moduleForget_limits A
  let V := SheafOfModules.toSheaf.{max u (t + 1)} A
  let : ReflectsLimitsOfSize.{0, 0} V := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{0, 0} (F ⋙ V) := preservesLimits_of_natIso e.symm
  exact ⟨preservesLimits_of_reflects_of_preserves F V, hcoeff⟩

end WeilConjectures.IntegralOnSlice
