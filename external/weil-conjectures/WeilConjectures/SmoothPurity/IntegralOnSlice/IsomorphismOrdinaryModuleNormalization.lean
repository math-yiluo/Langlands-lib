/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback

/-! # Ordinary pullback and normalized sectionwise inverse image

Source: Stacks Tags 03D2 and 03EL; expanded clause 4 of
prose-10-21.
(blueprint: lem-pur-isomorphism-ordinary-module-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralOnSlice

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
attribute [local instance_reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring
attribute [local instance_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem ordinarySectionwiseRingMap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let a := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    a.unit.app (completedIntegralCoefficientSheafUnrestricted l E Y) ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (inverseImageCompletedCoefficientMap l E g) = ordinaryCompletedRingMap l E g := by
  dsimp only
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let G := ordinaryRingPush.{u, u} g
  let F := isoSectionwiseInverseImage g RingCat.{u + 1}
  let : G.IsRightAdjoint := shAdj.isRightAdjoint
  refine (isLimitOfPreserves G
    (limit.isLimit (integralCoefficientSheafSystem l E X))).hom_ext
      (f := shAdj.unit.app (completedIntegralCoefficientSheafUnrestricted l E Y) ≫
        G.map (inverseImageCompletedCoefficientMap l E g))
      (f' := ordinaryCompletedRingMap l E g) ?_
  intro n
  change (_ ≫ _) ≫ G.map (limit.π (integralCoefficientSheafSystem l E X) n) =
    ordinaryCompletedRingMap l E g ≫ G.map
      (limit.π (integralCoefficientSheafSystem l E X) n)
  erw [(ordinaryCompletedRingMap_existsUnique l E g).exists.choose_spec n.unop]
  rw [Category.assoc, ← G.map_comp]
  have hc : inverseImageCompletedCoefficientMap l E g ≫
      limit.π (integralCoefficientSheafSystem l E X) n =
    F.map (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
      inverseImageFiniteCoefficientMap l E g n.unop := by
    exact limit.lift_π _ n
  erw [hc, G.map_comp, ← Category.assoc, ← shAdj.unit.naturality,
    Category.assoc, WeilConjectures.sectionwiseConstantDirectMap]
  rfl

private theorem ordinarySectionwiseAdjunctionNormalized {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj RY ⟶ RX)
    [IsIso c] :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    ∃ a : isoSectionwiseModuleInverseImage.{u, u} g c ⊣
      SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
        (shAdj.unit.app RY ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map c),
      ∀ (M : SheafOfModules.{u + 1} RY) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = M.val.map (adj.counit.app U.unop).op x := by
  dsimp only
  let F := proEtaleIsoPostcompose g
  let G := proEtaleBaseChange g
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ := shAdj.unit.app RY ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map c
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, proEtaleSheafDirectImage, ProEtale.lowerStar, G,
      proEtaleBaseChange]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (F.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((F.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((F.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  exact ⟨SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂, fun _ _ _ ↦ rfl⟩

private def ordinarySectionwiseAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralModules l E g ⊣ ordinaryPush l E g :=
  ((ordinarySectionwiseAdjunctionNormalized g
    (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (inverseImageCompletedCoefficientMap l E g)).choose).ofNatIsoRight
      (SheafOfModules.pushforwardCongr (ordinarySectionwiseRingMap l E g))

private def ordinarySectionwiseIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ordinaryPull l E g ≅ inverseImageIntegralModules l E g :=
  (ordinaryAdjunction l E g).leftAdjointUniq (ordinarySectionwiseAdjunction l E g)

private theorem ordinarySectionwiseIso_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((ordinarySectionwiseIso l E g).hom.app M).val.app
        (op ((proEtaleBaseChange g).obj V))
      (((ordinaryAdjunction l E g).unit.app M).val.app (op V) x) =
      M.val.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          (inferInstance : WeaklyEtale g) trivial).counit.app V).op x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ordinaryAdjunction l E g) (ordinarySectionwiseAdjunction l E g) M
  have h' := congrArg (fun a ↦ a.val.app (op V) x) h
  exact h'.trans
    ((ordinarySectionwiseAdjunctionNormalized g
      (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficientSheafUnrestricted l E X)
      (inverseImageCompletedCoefficientMap l E g)).choose_spec M (op V) x)

/-- Ordinary pullback agrees with sectionwise inverse image, with the unit fixed.
Source: Stacks Tag 03D2, via the site adjunction and left-adjoint uniqueness.
(blueprint: lem-pur-isomorphism-ordinary-module-normalization).
Proof: the completed coefficient maps agree by all finite projections. Transport the
sectionwise module adjunction along this equality. Its unit is restriction along the
site counit, and left-adjoint uniqueness gives the asserted normalized isomorphism. -/
theorem isomorphismOrdinaryModuleNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃ b : ordinaryPull l E g ≅ inverseImageIntegralModules l E g,
    ∀ (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)),
      (b.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (((ordinaryAdjunction l E g).unit.app M).val.app (op V) x) =
      M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
        (inferInstance : WeaklyEtale g) trivial).counit.app V).op x := by
  exact ⟨ordinarySectionwiseIso l E g, ordinarySectionwiseIso_unit l E g⟩

end WeilConjectures.IntegralOnSlice
