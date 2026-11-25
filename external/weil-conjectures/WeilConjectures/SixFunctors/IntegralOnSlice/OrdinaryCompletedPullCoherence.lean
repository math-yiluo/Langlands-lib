/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import all WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence

/-! # Ordinary completed-coefficient module pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def ordinaryRingComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryRingPush.{t, u} f ⋙ ordinaryRingPush.{t, u} g ≅
      ordinaryRingPush.{t, u} (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    RingCat.{max u (t + 1)} (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

private theorem ordinaryRingMapComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryCompletedRingMap l E g ≫
        (ordinaryRingPush.{t, u} g).map (ordinaryCompletedRingMap l E f) ≫
        (ordinaryRingComp.{t, u} f g).hom.app
          (completedIntegralCoefficientSheafUnrestricted l E X) =
      ordinaryCompletedRingMap l E (f ≫ g) := by
  apply (ordinaryCompletedRingMap_existsUnique l E (f ≫ g)).unique ?_
    (ordinaryCompletedRingMap_existsUnique l E (f ≫ g)).exists.choose_spec
  intro n
  let πX : completedIntegralCoefficientSheafUnrestricted l E X ⟶
      integralCoefficientSheaf l E X n :=
    limit.π (integralCoefficientSheafSystem l E X) (op n)
  let πZ : completedIntegralCoefficientSheafUnrestricted l E Z ⟶
      integralCoefficientSheaf l E Z n :=
    limit.π (integralCoefficientSheafSystem l E Z) (op n)
  have hn := (ordinaryRingComp.{t, u} f g).hom.naturality πX
  change (ordinaryRingPush.{t, u} g).map ((ordinaryRingPush.{t, u} f).map πX) ≫
      (ordinaryRingComp.{t, u} f g).hom.app _ =
    (ordinaryRingComp.{t, u} f g).hom.app _ ≫
      (ordinaryRingPush.{t, u} (f ≫ g)).map πX at hn
  let πY : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
      integralCoefficientSheaf l E Y n :=
    limit.π (integralCoefficientSheafSystem l E Y) (op n)
  have hf : ordinaryCompletedRingMap l E f ≫ (ordinaryRingPush.{t, u} f).map πX =
      πY ≫ ordinaryFiniteRingMap l E f n :=
    (ordinaryCompletedRingMap_existsUnique l E f).exists.choose_spec n
  have hg : ordinaryCompletedRingMap l E g ≫ (ordinaryRingPush.{t, u} g).map πY =
      πZ ≫ ordinaryFiniteRingMap l E g n :=
    (ordinaryCompletedRingMap_existsUnique l E g).exists.choose_spec n
  let G := ordinaryRingPush.{t, u} g
  let A := (ordinaryRingComp.{t, u} f g).hom.app
    (integralCoefficientSheaf l E X n)
  change (ordinaryCompletedRingMap l E g ≫ G.map (ordinaryCompletedRingMap l E f) ≫
    (ordinaryRingComp.{t, u} f g).hom.app
      (completedIntegralCoefficientSheafUnrestricted l E X)) ≫
    (ordinaryRingPush.{t, u} (f ≫ g)).map πX = πZ ≫ ordinaryFiniteRingMap l E (f ≫ g) n
  calc
    _ = ordinaryCompletedRingMap l E g ≫
        G.map (ordinaryCompletedRingMap l E f ≫
          (ordinaryRingPush.{t, u} f).map πX) ≫ A := by
      simp only [Category.assoc]
      rw [← hn]
      simp only [G, A, Functor.map_comp, Category.assoc]
    _ = ordinaryCompletedRingMap l E g ≫
        G.map (πY ≫ ordinaryFiniteRingMap l E f n) ≫ A := by
      rw [hf]
    _ = (ordinaryCompletedRingMap l E g ≫ G.map πY) ≫
        G.map (ordinaryFiniteRingMap l E f n) ≫ A := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (πZ ≫ ordinaryFiniteRingMap l E g n) ≫
        G.map (ordinaryFiniteRingMap l E f n) ≫ A := by
      rw [hg]
    _ = πZ ≫ ordinaryFiniteRingMap l E (f ≫ g) n := by
      rw [Category.assoc]
      congr 1
      let F := sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
      exact congrArg F.map (completedDirect_comp f g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

private def ordinaryPushComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryPush l E f ⋙ ordinaryPush l E g ≅ ordinaryPush l E (f ≫ g) := by
  letI := Functor.isContinuous_comp (proEtaleBaseChange g) (proEtaleBaseChange f)
    (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  exact SheafOfModules.pushforwardComp (ordinaryCompletedRingMap l E g)
      (ordinaryCompletedRingMap l E f) ≪≫
    SheafOfModules.pushforwardCongr₂ _
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g)
      (ordinaryRingMapComp l E f g)

private def ordinarySiteId (X : Scheme.{t}) : proEtaleBaseChange (𝟙 X) ≅ 𝟭 X.ProEt :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk
    (asIso (pullback.fst V.hom (𝟙 X))) (by
      change pullback.fst V.hom (𝟙 X) ≫ V.hom = pullback.snd V.hom (𝟙 X)
      simpa using (pullback.condition (f := V.hom) (g := 𝟙 X)))) (by
        intro V W a
        apply MorphismProperty.Over.Hom.ext
        change pullback.lift (pullback.fst V.hom (𝟙 X) ≫ a.left) _ _ ≫
          pullback.fst W.hom (𝟙 X) = pullback.fst V.hom (𝟙 X) ≫ a.left
        exact pullback.lift_fst _ _ _)

private def ordinaryRingId (X : Scheme.{t}) :
    ordinaryRingPush.{t, u} (𝟙 X) ≅ 𝟭 (Sheaf (ProEt.topology X)
      RingCat.{max u (t + 1)}) :=
  Functor.sheafPushforwardContinuousId' (ordinarySiteId X) _ _

private theorem ordinaryFiniteRingMapId (X : Scheme.{t}) (n : ℕ) :
    ordinaryFiniteRingMap l E (𝟙 X) n ≫
        (ordinaryRingId.{t, u} X).hom.app (integralCoefficientSheaf l E X n) = 𝟙 _ := by
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let e := Functor.sheafPushforwardContinuousId' (ordinarySiteId X)
    CommRingCat.{max u (t + 1)} (ProEt.topology X)
  have hc : coefficientProEtaleDirectRingMap (𝟙 X) A ≫
      e.hom.app ((constantSheaf (ProEt.topology X) _).obj A) = 𝟙 _ := by
    apply ((sheafificationAdjunction (ProEt.topology X) _).homEquiv _ _).injective
    apply NatTrans.ext
    funext V
    change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app V ≫
      (coefficientProEtaleDirectRingMap (𝟙 X) A).hom.app V ≫ _ =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app V
    rw [← Category.assoc, completedDirect_unit]
    have hn := (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
        ((ordinarySiteId X).inv.app V.unop).op
    change 𝟙 _ ≫ _ = _ at hn
    exact hn.symm.trans (Category.id_comp _)
  let F := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  exact congrArg F.map hc

private theorem ordinaryRingMapId (X : Scheme.{t}) :
    ordinaryCompletedRingMap l E (𝟙 X) =
      (ordinaryRingId.{t, u} X).inv.app
        (completedIntegralCoefficientSheafUnrestricted l E X) := by
  symm
  apply (ordinaryCompletedRingMap_existsUnique l E (𝟙 X)).unique ?_
    (ordinaryCompletedRingMap_existsUnique l E (𝟙 X)).exists.choose_spec
  intro n
  rw [← NatTrans.naturality]
  congr 1
  apply (cancel_mono ((ordinaryRingId.{t, u} X).hom.app _)).mp
  rw [Iso.inv_hom_id_app]
  exact (ordinaryFiniteRingMapId l E X n).symm

private def ordinaryPushId (X : Scheme.{t}) :
    ordinaryPush l E (𝟙 X) ≅ 𝟭 (Mod l E X none) :=
  SheafOfModules.pushforwardCongr₂ (ordinaryCompletedRingMap l E (𝟙 X))
    (ordinarySiteId X).symm
    (by
      rw [ordinaryRingMapId]
      exact Iso.inv_hom_id_app (ordinaryRingId.{t, u} X) _) ≪≫
      SheafOfModules.pushforwardId _

/-- Identity and composition comparisons for the actual ordinary module pullbacks.
Source: Stacks, Modules on Sites, Tags 03D2 and 03D7.
(blueprint: lem-fix-ordinary-completed-pull-coherence).
Proof: base change on pro-etale sites has the identity and associativity comparisons
of fiber products. For each finite constant coefficient sheaf the direct ring maps
respect these comparisons: both maps send a constant section to that same section.
The finite quotient maps are jointly monic on the completed ring, so the same
identities hold for ordinaryCompletedRingMap. Module pushforward therefore respects
identity and composition, by its sectionwise definition and the ring-map identities.
Transport these comparisons through ordinaryAdjunction. Uniqueness of left adjoints
identifies the identity pullback with the identity and the composite pullback with
successive pullbacks. This argument concerns module sheaves, without deriving or
completing any module, and also applies to empty schemes. -/
theorem ordinaryCompletedPullCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ X : Scheme.{t}, Nonempty (ordinaryPull l E (𝟙 X) ≅ 𝟭 (Mod l E X none))) ∧
    (∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Nonempty (ordinaryPull l E (f ≫ g) ≅ ordinaryPull l E g ⋙ ordinaryPull l E f)) := by
  constructor
  · intro X
    exact ⟨(ordinaryAdjunction l E (𝟙 X)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (ordinaryPushId l E X).symm)⟩
  · intro X Y Z f g
    exact ⟨(ordinaryAdjunction l E (f ≫ g)).leftAdjointUniq
      (((ordinaryAdjunction l E g).comp (ordinaryAdjunction l E f)).ofNatIsoRight
        (ordinaryPushComp l E f g))⟩

end WeilConjectures.IntegralOnSlice
