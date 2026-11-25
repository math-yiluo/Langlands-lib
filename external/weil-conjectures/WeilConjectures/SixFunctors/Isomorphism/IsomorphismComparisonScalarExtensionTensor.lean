/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization

/-!
# Coefficient compatibility: the tensor isomorphism under inverse image

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
The actual tensor isomorphism b on sheaves and the maps α and β of the comparison square.
Split from `WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension`
for compile time.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem tensorModel_hom_ext (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) (f g : A ⟶ B)
    (h : ∀ (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      g.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))) : f = g := by
  subst A
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact h U a x
  | add z z' hz hz' => simp only [map_add, hz, hz']

section TensorComparison

open AlgebraicGeometry

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem constantTransport_natural
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a)) ≫
        isoSectionwiseConstantMap.{u, u} g B =
      isoSectionwiseConstantMap.{u, u} g A ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let I := isoSectionwiseInverseImage g RingCat.{u + 1}
  let cA := isoSectionwiseConstantMap.{u, u} g A
  let cB := isoSectionwiseConstantMap.{u, u} g B
  let aY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a)
  let aX := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a
  change I.map aY ≫ cB = cA ≫ W.map aX
  apply (cancel_epi (inv cA)).1
  rw [IsIso.inv_hom_id_assoc]
  let f := inv cA ≫ I.map aY ≫ cB
  change f = W.map aX
  rw [← W.map_preimage f]
  apply congrArg W.map
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B).property
  ext U x
  change (W.map (W.preimage f)).hom.app U _ = _
  rw [W.map_preimage]
  have hcA := (isoSectionwiseConstantMap_existsUnique.{u, u} g A).exists.choose_spec
  have hcB := (isoSectionwiseConstantMap_existsUnique.{u, u} g B).exists.choose_spec
  have hi := congrArg (fun k ↦ k.hom.app U) (IsIso.hom_inv_id cA)
  have hi' := ConcreteCategory.congr_hom hi
    ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x)
  change (inv cA).hom.app U (cA.hom.app U _) = _ at hi'
  erw [hcA U.unop x] at hi'
  have hy := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app (op ((proEtaleIsoPostcompose g).obj U.unop)))
      (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))) x
  have hx := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app U)
      (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))) x
  change cB.hom.app U (aY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
    ((inv cA).hom.app U _)) = _
  erw [hi']
  change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) (a x) =
    aY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) x) at hy
  erw [← hy, hcB U.unop (a x)]
  exact hx
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarTransport_square
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι Y)) ≫
        inverseImageCompletedCoefficientMap l L g =
      inverseImageCompletedCoefficientMap l E g ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι X) := by
  let I := isoSectionwiseInverseImage g RingCat.{u + 1}
  let WX := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let WY := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted l F W n) =
        limit.π (integralCoefficientSheafSystem l F W) (op n) := by
    ext U x
    rfl
  have hscalar (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W) ≫
          limit.π (integralCoefficientSheafSystem l L W) (op n) =
        limit.π (integralCoefficientSheafSystem l E W) (op n) ≫
          (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (integralScalarQuotientSheafMap l E L ι W n) := by
    have h := congrArg
      (fun a ↦ (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)
      ((integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n)
    simpa only [integralScalarRho, integralCompletedScalarMap,
      CategoryTheory.Functor.map_comp, hproj] using h
  have hc (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      inverseImageCompletedCoefficientMap l F g ≫
          limit.π (integralCoefficientSheafSystem l F X) (op n) =
        I.map (limit.π (integralCoefficientSheafSystem l F Y) (op n)) ≫
          inverseImageFiniteCoefficientMap l F g n := by
    exact limit.lift_π _ (op n)
  apply limit.hom_ext
  intro n
  change (I.map (WY.map (integralCompletedScalarMap l E L ι Y)) ≫
      inverseImageCompletedCoefficientMap l L g) ≫
      limit.π (integralCoefficientSheafSystem l L X) (op n.unop) =
    (inverseImageCompletedCoefficientMap l E g ≫
      WX.map (integralCompletedScalarMap l E L ι X)) ≫
      limit.π (integralCoefficientSheafSystem l L X) (op n.unop)
  rw [Category.assoc, hc L n.unop, ← Category.assoc, ← I.map_comp,
    hscalar Y n.unop, I.map_comp, Category.assoc]
  rw [Category.assoc, hscalar X n.unop]
  have hce := hc E n.unop
  erw [reassoc_of% hce]
  congr 1
  exact constantTransport_natural g _

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
attribute [local irreducible] integralCompletedScalarMap inverseImageCompletedCoefficientMap

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryScalarAdjunction (W : AlgebraicGeometry.Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι W ⊣
      SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W)),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = integralOrdinaryTensorSection l E L ι W M U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι W)
  obtain ⟨a, ha⟩ := h (integralOrdinaryScalar l E L ι W)
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose
  refine ⟨a, ?_⟩
  intro M U x
  have h := ha M ((integralOrdinaryScalar l E L ι W).obj M)
    (eqToHom ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl] at h
  rw [Adjunction.homEquiv_id] at h
  exact h
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem sectionwiseModuleAdjunctionNormalized {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
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

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem sectionwiseRestrictionSquare
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY SY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX SX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (φY : RY ⟶ SY) (φX : RX ⟶ SX)
    (cR : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        RY ⟶
      RX)
    (cS : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        SY ⟶
      SX)
    (hφ : (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        φY ≫ cS =
      cR ≫ φX) :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    let H := proEtaleSheafDirectImage g RingCat.{u + 1}
    let ψR := shAdj.unit.app RY ≫ H.map cR
    let ψS := shAdj.unit.app SY ≫ H.map cS
    ∃ e : SheafOfModules.restrictScalars
          φX ⋙
          SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψR ≅
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψS ⋙
          SheafOfModules.restrictScalars
            φY,
      ∀ (M : SheafOfModules.{u + 1} SX)
        (V : Y.ProEtᵒᵖ) (x : M.val.obj ((proEtaleBaseChange g).op.obj V)),
        (e.hom.app M).val.app V x = x := by
  dsimp only
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let H := proEtaleSheafDirectImage g RingCat.{u + 1}
  let WY := 𝟭 (Sheaf (ProEt.topology Y) RingCat.{u + 1})
  let WX := 𝟭 (Sheaf (ProEt.topology X) RingCat.{u + 1})
  let ψR := shAdj.unit.app (WY.obj RY) ≫ H.map cR
  let ψS := shAdj.unit.app (WY.obj SY) ≫ H.map cS
  have hψ : ψR ≫ H.map (WX.map φX) = WY.map φY ≫ ψS := by
    dsimp only [ψR, ψS, WY, WX, Functor.id_obj, Functor.id_map]
    rw [Category.assoc, ← H.map_comp, ← hφ, H.map_comp, ← Category.assoc]
    erw [← shAdj.unit.naturality]
    rfl
  let A := SheafOfModules.restrictScalars (WX.map φX) ⋙
    SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψR
  let B := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψS ⋙
    SheafOfModules.restrictScalars (WY.map φY)
  let e : A ≅ B := NatIso.ofComponents (fun M ↦ by
    refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
    · let P := (A.obj M).val.obj V
      let Q := (B.obj M).val.obj V
      refine
        { hom := ModuleCat.ofHom (X := P) (Y := Q)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          inv := ModuleCat.ofHom (X := Q) (Y := P)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          hom_inv_id := by ext; rfl
          inv_hom_id := by ext; rfl }
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change (WX.map φX).hom.app ((proEtaleBaseChange g).op.obj V)
            (ψR.hom.app V r) • m' = ψS.hom.app V ((WY.map φY).hom.app V r) • m'
        congr 1
        exact congrArg (fun k ↦ k.hom.app V r) hψ
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change ψS.hom.app V ((WY.map φY).hom.app V r) • m' =
          (WX.map φX).hom.app ((proEtaleBaseChange g).op.obj V) (ψR.hom.app V r) • m'
        congr 1
        exact (congrArg (fun k ↦ k.hom.app V r) hψ).symm
    · intro V W i
      ext m
      rfl) (by
        intro M N f
        ext V m
        rfl)
  exact ⟨e, fun _ _ _ ↦ rfl⟩

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem tensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  change k (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) =
    a • k ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    change a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      (a * 1) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact k.hom.map_smul a _

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    integralOrdinaryTensorSection l E L ι W M U a x =
      a • integralOrdinaryTensorSection l E L ι W M U 1 x := by
  exact tensorSection_smul W (integralCompletedScalarMap l E L ι W) M _
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M) U a x

universe v

private theorem unit_triangle_normalization
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (H : D ⥤ C) (a : F ⊣ H)
    (M N : Dᵒᵖ ⥤ Type v) (τ : F.op ⋙ M ⟶ F.op ⋙ N)
    (v : ∀ V : Dᵒᵖ, M.obj V → N.obj V)
    (hbase : ∀ (V : Dᵒᵖ) (x : M.obj V),
      τ.app (op (H.obj V.unop)) (M.map (a.counit.app V.unop).op x) =
        N.map (a.counit.app V.unop).op (v V x)) :
    ∀ (U : C) (y : M.obj (op (F.obj U))), τ.app (op U) y = v (op (F.obj U)) y := by
  intro U y
  let h := a.unit.app U
  let y' := M.map (a.counit.app (F.obj U)).op y
  have hn := ConcreteCategory.congr_hom (τ.naturality h.op) y'
  change τ.app (op U) (M.map (F.map h).op y') =
    N.map (F.map h).op (τ.app (op (H.obj (F.obj U))) y') at hn
  rw [hbase (op (F.obj U)) y] at hn
  have ht : (a.counit.app (F.obj U)).op ≫ (F.map h).op = 𝟙 _ := by
    dsimp only [h, Functor.id_obj, Functor.comp_obj]
    rw [← op_comp]
    change (F.map (a.unit.app U) ≫ a.counit.app (F.obj U)).op = (𝟙 (F.obj U)).op
    exact congrArg (fun f : F.obj U ⟶ F.obj U ↦ f.op) (a.left_triangle_components U)
  have hm := ConcreteCategory.congr_hom
    (M.map_comp (a.counit.app (F.obj U)).op (F.map h).op) y
  have hn' := ConcreteCategory.congr_hom (N.map_comp (a.counit.app (F.obj U)).op (F.map h).op)
    (v (op (F.obj U)) y)
  rw [ht, M.map_id] at hm
  rw [ht, N.map_id] at hn'
  change y = M.map (F.map h).op y' at hm
  change v (op (F.obj U)) y =
    N.map (F.map h).op (N.map (a.counit.app (F.obj U)).op (v (op (F.obj U)) y)) at hn'
  rw [← hm, ← hn'] at hn
  exact hn

private theorem adjointSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    {R₁ : B ⥤ A} {R₂ : D ⥤ B} {S₁ : C ⥤ A} {S₂ : D ⥤ C}
    (aR : F₁ ⊣ R₁) (aX : F₂ ⊣ R₂) (aY : G₁ ⊣ S₁) (aS : G₂ ⊣ S₂)
    (s : R₂ ⋙ R₁ ≅ S₂ ⋙ S₁) :
    ∃ b : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂, ∀ M,
      ((aR.comp aX).ofNatIsoRight s).unit.app M ≫
        (S₂ ⋙ S₁).map (b.hom.app M) = (aY.comp aS).unit.app M := by
  let a := (aR.comp aX).ofNatIsoRight s
  exact ⟨a.leftAdjointUniq (aY.comp aS), fun M ↦
    a.unit_leftAdjointUniq_hom_app (aY.comp aS) M⟩

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem sectionwiseTensorUnit
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY SY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX SX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (φY : RY ⟶ SY) (φX : RX ⟶ SX)
    (cR : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        RY ⟶
      RX)
    [IsIso cR]
    (cS : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        SY ⟶
      SX)
    [IsIso cS]
    (hφ : (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        φY ≫ cS =
      cR ≫ φX)
    (FX : SheafOfModules.{u + 1} RX ⥤
      SheafOfModules.{u + 1} SX)
    (FY : SheafOfModules.{u + 1} RY ⥤
      SheafOfModules.{u + 1} SY)
    (aX : FX ⊣ SheafOfModules.restrictScalars φX)
    (aY : FY ⊣ SheafOfModules.restrictScalars φY) :
    ∃ b : isoSectionwiseModuleInverseImage.{u, u} g cR ⋙ FX ≅
        FY ⋙ isoSectionwiseModuleInverseImage.{u, u} g cS,
      ∀ (M : SheafOfModules.{u + 1} RY) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app
            (op U) y) =
          (aY.unit.app M).val.app (op ((proEtaleIsoPostcompose g).obj U)) y := by
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  obtain ⟨aR, haR⟩ := sectionwiseModuleAdjunctionNormalized g
    RY
    RX cR
  obtain ⟨aS, haS⟩ := sectionwiseModuleAdjunctionNormalized g
    SY
    SX cS
  obtain ⟨s, hs⟩ := sectionwiseRestrictionSquare g RY SY RX SX φY φX cR cS hφ
  obtain ⟨b, hb⟩ := adjointSquare aR aX aY aS s
  have hOne (M : SheafOfModules.{u + 1} RY)
      (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
      (b.hom.app M).val.app ((proEtaleBaseChange g).op.obj V)
        ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app
          ((proEtaleBaseChange g).op.obj V) (M.val.map (adj.counit.app V.unop).op x)) =
      (FY.obj M).val.map (adj.counit.app V.unop).op ((aY.unit.app M).val.app V x) := by
    have h := hb M
    have h' := congrArg (fun k ↦ k.val.app V x) h
    change (b.hom.app M).val.app ((proEtaleBaseChange g).op.obj V)
      ((s.hom.app (FX.obj ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M))).val.app V
        ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app
          ((proEtaleBaseChange g).op.obj V) ((aR.unit.app M).val.app V x))) =
      (aS.unit.app (FY.obj M)).val.app V ((aY.unit.app M).val.app V x) at h'
    rw [hs, haR, haS] at h'
    exact h'
  refine ⟨b, ?_⟩
  intro M U y
  let F := proEtaleIsoPostcompose g
  let M' := M.val.presheaf ⋙ forget Ab
  let N' := (FY.obj M).val.presheaf ⋙ forget Ab
  let τ : F.op ⋙ M' ⟶ F.op ⋙ N' :=
    { app := fun V ↦ TypeCat.ofHom (fun x ↦ (b.hom.app M).val.app V
        ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app V x))
      naturality := by
        intro V V' f
        apply ConcreteCategory.hom_ext
        intro x
        have hu := PresheafOfModules.naturality_apply
          (aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val f x
        have hb' := PresheafOfModules.naturality_apply (b.hom.app M).val f
          ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app V x)
        change (b.hom.app M).val.app V'
          ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app V'
            (((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M).val.map f x)) = _
        erw [hu]
        exact hb' }
  exact unit_triangle_normalization F (proEtaleBaseChange g) adj M' N' τ
    (fun V x ↦ (aY.unit.app M).val.app V x) (hOne M) U y

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem tensorIso_one_exists
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃ b : inverseImageIntegralModules l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U) 1 y) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) 1 y := by
  obtain ⟨aY, haY⟩ := ordinaryScalarAdjunction l E L ι Y
  obtain ⟨aX, haX⟩ := ordinaryScalarAdjunction l E L ι X
  obtain ⟨b, hb⟩ := sectionwiseTensorUnit g
    (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficientSheafUnrestricted l L Y)
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (completedIntegralCoefficientSheafUnrestricted l L X)
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap l E L ι Y))
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap l E L ι X))
    (inverseImageCompletedCoefficientMap l E g) (inverseImageCompletedCoefficientMap l L g)
    (scalarTransport_square l E L ι g)
    (integralOrdinaryScalar l E L ι X) (integralOrdinaryScalar l E L ι Y) aX aY
  refine ⟨b, ?_⟩
  intro M U y
  have h := hb M U y
  erw [haX, haY] at h
  exact h

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
/-- The sectionwise tensor comparison is uniquely fixed on every local pure tensor.
Here U maps to (U,g∘u), so the underlying section y is literally y₀, and the target
scalar c_L(g⁻¹a₀) is the displayed completed coefficient map applied to a₀.
Source: inverse-image tensor comparison and Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: inverse-image tensor compatibility sends the transported pure tensor to the
same tensor on (U,g∘u). The coefficient projection equations make it balanced over
R_E, and c_L gives its R_L-linearity. The reverse tensor rule is its inverse.
Restrictions and module maps commute with the formula. Sheafification extends
these maps; local generation by pure tensors proves uniqueness. -/
theorem isomorphismScalarTensor_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! b : inverseImageIntegralModules l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U)
            ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a) y) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a y := by
  obtain ⟨b, hb⟩ := tensorIso_one_exists l E L ι g
  refine ⟨b, ?_, ?_⟩
  · intro M U y a
    let c := inverseImageCompletedCoefficientMap l L g
    let z : (((inverseImageIntegralModules l L g).obj
        ((integralOrdinaryScalar l E L ι Y).obj M)).val.obj (op U)) :=
      integralOrdinaryTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U)) 1 y
    calc
      _ = c.hom.app (op U) a • ((b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U) 1 y)) := by
        rw [ordinaryTensorSection_smul]
        exact ((b.hom.app M).val.app (op U)).hom.map_smul _ _
      _ = c.hom.app (op U) a • z := congrArg (fun z ↦ c.hom.app (op U) a • z) (hb M U y)
      _ = a • integralOrdinaryTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) 1 y := by
        change (inv c).hom.app (op U) (c.hom.app (op U) a) •
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) 1 y = _
        have hi := congrArg (fun f ↦ f.hom.app (op U) a) (IsIso.hom_inv_id c)
        change (inv c).hom.app (op U) (c.hom.app (op U) a) = a at hi
        rw [hi]
      _ = _ := (ordinaryTensorSection_smul l E L ι Y M _ a y).symm
  · intro b' hb'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply tensorModel_hom_ext X (integralCompletedScalarMap l E L ι X)
      ((inverseImageIntegralModules l E g).obj M) _ _
      ((integralOrdinaryScalarWitness l E L ι X).choose_spec.choose _)
    intro U a x
    change (b'.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) U a x) =
      (b.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) U a x)
    have h' : (b'.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) U 1 x) =
      integralOrdinaryTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x := by
      simpa only [map_one] using hb' M U.unop x 1
    calc
      _ = a • ((b'.hom.app M).val.app U
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)) := by
        rw [ordinaryTensorSection_smul]
        exact ((b'.hom.app M).val.app U).hom.map_smul a
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)
      _ = a • ((b.hom.app M).val.app U
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)) := by
        rw [h', hb]
      _ = _ := by
        conv_rhs => rw [ordinaryTensorSection_smul]
        exact (((b.hom.app M).val.app U).hom.map_smul a
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)).symm

end TensorComparison

/-- The actual tensor isomorphism b on sheaves, fixed by its local tensor rule.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarTensor {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  (isomorphismScalarTensor_existsUnique l E L ι g).exists.choose

/-- Exact inverse image and finite-free extension descend this same tensor isomorphism.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarTensorDerived {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralDerived l E g ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ inverseImageIntegralDerived l L g :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
    (integralOrdinaryScalar l E L ι X)) ≪≫
    Functor.mapDerivedCategoryNatIso (isomorphismScalarTensor l E L ι g) ≪≫
    (Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L ι Y)
      (inverseImageIntegralModules l L g)).symm

/-- Both inputs to the X-side completion comparisons lie in the recorded bounded
constructible, derived-complete category. Source: Bhatt--Scholze 6.5.9(4), and the
isomorphism-derived-pullback assertion
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the sectionwise inverse-image equivalence transports the coefficient actions,
finite quotient reductions, and their constructible partitions. Exactness transports
cohomology and its common finite interval. It commutes with the quotient-unit Roos
triangle, giving completeness of inverse image. The recorded completed pullback is
naturally identified with that inverse image on these objects by
lem-weil-isomorphism-derived-pullback. This identification preserves the constructible
and completeness predicates, giving the second clause. -/
theorem isomorphismComparisonInputs_constructible
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (_hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((inverseImageIntegralDerived l E g).obj K) ∧
      sfIntegralConstructible l E X ((integralDerivedPullback l E g).obj K) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (_hX x).map (IsLocalRing.residue (X.presheaf.stalk x)) |>.invertible
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (_hY y).map (IsLocalRing.residue (Y.presheaf.stalk y)) |>.invertible
  have hF := ((integralOperations_preserve_constructible l E g).1 K _hK).1
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨D, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let T := (D.coefficient E).system Y
  let := (D.coefficient E).complete Y ⟨K, _hK⟩
  have hu : IsIso (S.adjunction.unit.app K) := by
    have h := T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction K
    rw [← h]
    infer_instance
  let := hu
  obtain ⟨κ, hk, _, hn, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g _hX _hY
  obtain ⟨θ, hθ⟩ := hn S hS
  have : IsIso (κ.app K) := by
    rw [hθ K]
    infer_instance
  let := sfIntegralConstructible_isClosedUnderIsomorphisms l E X
  exact ⟨(sfIntegralConstructible l E X).prop_of_iso (asIso (κ.app K)).symm hF, hF⟩

/-- α is tensor associativity followed by the strict quotient completion comparisons:
the recorded `scalarPullbackCompleted` of the scalar-operation lemma, whose completeness
inputs come from hK and the constructibility theorem above.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismComparisonScalarAlpha {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E g).obj K) ⟶
      (integralDerivedPullback l L g).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarPullbackCompleted l E L ι g K hK.1
    (isomorphismComparisonInputs_constructible l E g hX hY K hK).2.1).hom

/-- β = G_L(χ_Y) ∘ b ∘ χ_X⁻¹, using the specified completion comparison.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismComparisonScalarBeta {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).obj ((inverseImageIntegralDerived l E g).obj K) ⟶
      (inverseImageIntegralDerived l L g).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarCompletionIso l E L ι X ((inverseImageIntegralDerived l E g).obj K)
    ((isomorphismComparisonInputs_constructible l E g hX hY K hK).1.1)).inv ≫
    (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
    (inverseImageIntegralDerived l L g).map ((scalarCompletion l E L ι Y).app K)

end WeilConjectures
