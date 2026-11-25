/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Isomorphism pullback and termwise inverse image

Source: Weil blueprint, ordinary compact cohomology, order 1510, coefficient-object
paragraph; Stacks Project, Tags 015F, 06YS and 08TC; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-weil-isomorphism-derived-pullback).

The integral structure isomorphism is fixed by all its finite quotient projections.
Termwise inverse image transports the module action by restriction along its inverse;
it does not apply a completed tensor product to each term.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite quotient transition with commutativity retained.
Source: Stacks Tag 03CO (blueprint: lem-weil-isomorphism-derived-pullback). -/
private def completedCommTransition (Y : Scheme.{u}) (n : ℕ) :
    integralCoefficientCommRingSheaf l E Y (n + 1) ⟶
      integralCoefficientCommRingSheaf l E Y n :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))

/-- The finite quotient tower with commutativity retained.
Source: Stacks Tag 03CO (blueprint: lem-weil-isomorphism-derived-pullback). -/
private def completedCommDiagram (Y : Scheme.{u}) :=
  Functor.ofOpSequence (completedCommTransition l E Y)

/-- The recorded completed ring and its finite quotient projections.
Source: Stacks Tag 03CO (blueprint: lem-weil-isomorphism-derived-pullback). -/
private def completedCommCone (Y : Scheme.{u}) : Cone (completedCommDiagram l E Y) where
  pt := completedIntegralCommRingSheafUnrestricted l E Y
  π := NatTrans.ofOpSequence (completedIntegralCommRingProjectionUnrestricted l E Y)
    (fun n ↦ by
      apply (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
      simp only [Functor.map_comp, Functor.const_obj_map, completedCommDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      change limit.π (integralCoefficientSheafSystem l E Y) (op n) =
        limit.π (integralCoefficientSheafSystem l E Y) (op (n + 1)) ≫ _
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        integralCoefficientSheafTransition, completedCommTransition]
        using (limit.w (integralCoefficientSheafSystem l E Y)
          (homOfLE (Nat.le_add_right n 1)).op).symm)

/-- The completed commutative-ring cone is limiting by reflection to ring sheaves.
Source: Stacks Tag 03CO (blueprint: lem-weil-isomorphism-derived-pullback). -/
private def completedCommConeIsLimit (Y : Scheme.{u}) :
    IsLimit (completedCommCone l E Y) := by
  apply isLimitOfReflects (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let V := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e : completedCommDiagram l E Y ⋙ V ⟶ integralCoefficientSheafSystem l E Y :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [Functor.comp_map, completedCommDiagram, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
      rfl)
  have : ∀ n, IsIso (e.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso e := NatIso.isIso_of_isIso_app e
  apply (IsLimit.postcomposeHomEquiv (asIso e) _).toFun
  exact IsLimit.ofIsoLimit (limit.isLimit (integralCoefficientSheafSystem l E Y))
    (Cone.ext (Iso.refl _) (fun n ↦ by
      simp only [Iso.refl_hom, Category.id_comp, Cone.postcompose_obj_π,
        NatTrans.comp_app, asIso_hom, e, NatTrans.ofOpSequence_app,
        completedCommCone, Functor.mapCone_π_app, Category.comp_id]
      rfl))

/-- The completed coefficient comparison is uniquely determined by its composites with
all finite quotient projections. These equations specify exactly the inverse-limit
comparison followed by the limit of the canonical constant-coefficient comparisons.
Source: blueprint order 1510; Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof: by lem-weil-proetale-isomorphism-inverse-image, inverse image preserves limits.
Its canonical limit comparison followed by the limit of the finite constant-ring
isomorphisms gives the required isomorphism. Naturality of those constant comparisons
makes a morphism of towers. Composing with the nth projection gives the displayed
identity. Joint monicity of limit projections proves uniqueness, also for inverses. -/
theorem isomorphismCompletedCoefficientComparison_existsUnique
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E Y) ≅
        completedIntegralCommRingSheafUnrestricted l E X,
      ∀ n : ℕ, c.hom ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
        (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
          proEtaleCoefficientInverseImageMap g (Padic.coefficientExtensionRing l E (n + 1)) := by
  let F := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let : F.IsEquivalence :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g CommRingCat.{u + 1}).1
  let a : completedCommDiagram l E Y ⋙ F ⟶ completedCommDiagram l E X :=
    NatTrans.ofOpSequence
      (fun n ↦ proEtaleCoefficientInverseImageMap g
        (Padic.coefficientExtensionRing l E (n + 1))) (fun n ↦ by
          simpa only [completedCommDiagram, Functor.comp_map,
            Functor.ofOpSequence_map_homOfLE_succ, completedCommTransition] using
            ((proEtaleIso_constantComparison g CommRingCat.{u + 1}).2 _ _
              (CommRingCat.ofHom
                ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
                  ((Padic.coefficientExtensionTransition l E (n + 1)).comp
                    (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))).symm)
  have : ∀ n, IsIso (a.app n) := fun n ↦
    (proEtaleIso_constantComparison g CommRingCat.{u + 1}).1 _
  have : IsIso a := NatIso.isIso_of_isIso_app _
  let hc := (IsLimit.postcomposeHomEquiv (asIso a) _).symm
    (isLimitOfPreserves F (completedCommConeIsLimit l E Y))
  let c := hc.conePointUniqueUpToIso (completedCommConeIsLimit l E X)
  refine ⟨c, ?_, ?_⟩
  · intro n
    exact hc.conePointUniqueUpToIso_hom_comp (completedCommConeIsLimit l E X) (op n)
  · intro d hd
    apply Iso.ext
    apply (completedCommConeIsLimit l E X).hom_ext
    intro n
    exact (hd n.unop).trans
      (hc.conePointUniqueUpToIso_hom_comp (completedCommConeIsLimit l E X) n).symm

/-- The uniquely normalized completed coefficient isomorphism c_O_E.
Source: blueprint order 1510; Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismCompletedCoefficientComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ≅
      completedIntegralCommRingSheafUnrestricted l E X :=
  (isomorphismCompletedCoefficientComparison_existsUnique l E g).exists.choose

/-- Inverse image of module sheaves, with the scalar action transported through c.
The inverse image is the recorded module inverse image, and restriction along c.inv
makes it an S-module without replacing it by a tensor model.
Source: Stacks Tags 00YV and 03D2; blueprint order 1510
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismTermwiseModuleInverseImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules Y R ⥤ proEtaleRingModules X S :=
  proEtaleModuleInverseImage g R ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)

/-- Exactness of the termwise coefficient transport used in this node.
Source: Stacks Tag 015F; blueprint order 1510
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof: lem-weil-proetale-isomorphism-inverse-image identifies inverse image with
relabelling along the covering-preserving site equivalence. Relabel the action maps
as well as the underlying abelian sheaves. Restriction along c.inv only transports
the scalars, so it preserves sums of maps, kernels and cokernels. Relabelling back
is its inverse, proving exactness and additivity. -/
theorem isomorphismTermwiseModuleInverseImage_exact {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (isomorphismTermwiseModuleInverseImage g R S c).Additive ∧
      PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) ∧
      PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c) := by
  set_option backward.defeqAttrib.useBackward false in
    set_option backward.isDefEq.respectTransparency false in
      let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
        integralCoefficientAbSheafify.{u, u} Y
      let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
        integralCoefficientAbSheafify.{u, u} X
      let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
        integralCoefficientAbLocallyBijective.{u, u} Y
      let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
        integralCoefficientAbLocallyBijective.{u, u} X
      let A := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
      let B := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
      let T := isomorphismTermwiseModuleInverseImage g R S c
      let V := SheafOfModules.toSheaf B
      obtain ⟨e⟩ := (proEtale_moduleInverseImage_comparison g R).1
      let d : T ⋙ V ≅ SheafOfModules.toSheaf A ⋙
          proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} := e
      let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g AddCommGrpCat.{u + 1}).1
      let : PreservesFiniteLimits (T ⋙ V) := preservesFiniteLimits_of_natIso d.symm
      let : PreservesFiniteColimits (T ⋙ V) := preservesFiniteColimits_of_natIso d.symm
      let : (T ⋙ V).Additive := Functor.additive_of_preserves_binary_products _
      let : T.Additive := Functor.additive_of_comp_faithful T V
      exact ⟨inferInstance, preservesFiniteLimits_of_reflects_of_preserves T V,
        preservesFiniteColimits_of_reflects_of_preserves T V⟩

/-- Additivity for termwise inverse image. Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
instance isomorphismTermwiseModuleInverseImage_additive {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (isomorphismTermwiseModuleInverseImage g R S c).Additive :=
  (isomorphismTermwiseModuleInverseImage_exact g R S c).1

/-- Left exactness for termwise inverse image. Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
instance isomorphismTermwiseModuleInverseImage_preservesFiniteLimits {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) :=
  (isomorphismTermwiseModuleInverseImage_exact g R S c).2.1

/-- Right exactness for termwise inverse image. Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
instance isomorphismTermwiseModuleInverseImage_preservesFiniteColimits {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c) :=
  (isomorphismTermwiseModuleInverseImage_exact g R S c).2.2

/-- Termwise integral inverse image in the ambient derived category over the completed
coefficient sheaf. The scalar action uses the specified limit comparison c_O_E.
Source: blueprint order 1510; Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback). -/
def isomorphismIntegralTermwiseInverseImage {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
  (isomorphismTermwiseModuleInverseImage g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (isomorphismCompletedCoefficientComparison l E g)).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionwiseModuleAdjunction {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj RY ⟶ RX)
    [IsIso c] :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    Nonempty (isoSectionwiseModuleInverseImage.{u, u} g c ⊣
      SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
        (shAdj.unit.app RY ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map c)) := by
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
  exact ⟨SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionwiseConstantDirectMap {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{u + 1}) :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    shAdj.unit.app ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf _ CommRingCat.{u + 1}).obj A)) ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (isoSectionwiseConstantMap.{u, u} g A) =
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A) := by
  dsimp only
  let W := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let f := shAdj.unit.app (W.obj ((constantSheaf _ CommRingCat.{u + 1}).obj A)) ≫
    (proEtaleSheafDirectImage g RingCat.{u + 1}).map
      (isoSectionwiseConstantMap.{u, u} g A)
  change f = W.map (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A)
  let f' : W.obj ((constantSheaf _ CommRingCat.{u + 1}).obj A) ⟶
      W.obj ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
        ((constantSheaf _ CommRingCat.{u + 1}).obj A)) := f
  change f' = W.map _
  rw [← W.map_preimage f']
  congr 1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology Y) _ _
    ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      ((constantSheaf _ CommRingCat.{u + 1}).obj A)).property
  ext U a
  have hc := (isoSectionwiseConstantMap_existsUnique.{u, u} g A).exists.choose_spec
  have hn : toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A) ≫
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A).hom =
      Functor.whiskerLeft (proEtaleBaseChange g).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)) := by
    exact toSheafify_sheafifyLift _ _ _
  have hr := congrArg (fun k ↦ (k.app U) a) hn
  change (W.map (W.preimage f')).hom.app U _ = _
  rw [W.map_preimage f']
  change (isoSectionwiseConstantMap.{u, u} g A).hom.app
      (op ((proEtaleBaseChange g).obj U.unop))
      (((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A).obj.map
        ((adj.counit.app U.unop).op) _ ) = _
  have hy := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).naturality
      (adj.counit.app U.unop).op) a
  change _ = (((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A).obj.map
    (adj.counit.app U.unop).op) _ at hy
  erw [← hy]
  exact (hc ((proEtaleBaseChange g).obj U.unop) a).trans hr.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedDirectProjection {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :
    proEtaleRingDirectImageMap g (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X)
        (isomorphismCompletedCoefficientComparison l E g) ≫
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (completedIntegralCommRingProjectionUnrestricted l E X n) =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  have hc : (isomorphismCompletedCoefficientComparison l E g).hom ≫
      completedIntegralCommRingProjectionUnrestricted l E X n = _ :=
    (isomorphismCompletedCoefficientComparison_existsUnique l E g).exists.choose_spec n
  change adj.unit.app _ ≫ _ ≫ _ = _
  erw [← Functor.map_comp, hc, Functor.map_comp, ← Category.assoc,
    ← adj.unit.naturality, Category.assoc]
  congr 1
  exact ((adj.homEquiv _ _).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedSectionwiseDirectMap {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    shAdj.unit.app (completedIntegralCoefficientSheafUnrestricted l E Y) ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (ProEtale.inverseImageCompletedCoefficientMap l E g) =
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleRingDirectImageMap g (completedIntegralCommRingSheafUnrestricted l E Y)
          (completedIntegralCommRingSheafUnrestricted l E X)
          (isomorphismCompletedCoefficientComparison l E g)) := by
  dsimp only
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let G := proEtaleSheafDirectImage g RingCat.{u + 1}
  let F := isoSectionwiseInverseImage g RingCat.{u + 1}
  let V := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let : G.IsRightAdjoint := shAdj.isRightAdjoint
  apply (isLimitOfPreserves G (limit.isLimit
    (integralCoefficientSheafSystem l E X))).hom_ext
  intro n
  change (_ ≫ _) ≫ G.map (limit.π _ n) = _ ≫ G.map (limit.π _ n)
  rw [Category.assoc, ← G.map_comp]
  have hc : ProEtale.inverseImageCompletedCoefficientMap l E g ≫
      limit.π (integralCoefficientSheafSystem l E X) n =
      F.map (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
        ProEtale.inverseImageFiniteCoefficientMap l E g n.unop := by
    exact limit.lift_π _ n
  erw [hc, G.map_comp, ← Category.assoc, ← shAdj.unit.naturality,
    Category.assoc, sectionwiseConstantDirectMap]
  have hd := congrArg V.map (completedDirectProjection l E g n.unop)
  exact hd.symm

private theorem integralReconstructionUnit_isIso (Y : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E Y)
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso (S.adjunction.unit.app K.obj) := by
  obtain ⟨D, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let T := (D.coefficient E).system Y
  let := (D.coefficient E).complete Y K
  let e := T.adjunction.leftAdjointUniq S.adjunction
  have h := T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction K.obj
  rw [← h]
  infer_instance

private theorem integralSectionwiseComparison {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    Nonempty (ProEtale.inverseImageIntegralDerived l E g ≅
      isomorphismIntegralTermwiseInverseImage l E g) := by
  set_option backward.defeqAttrib.useBackward false in
    set_option backward.isDefEq.respectTransparency false in
    let R := completedIntegralCommRingSheafUnrestricted l E Y
    let S := completedIntegralCommRingSheafUnrestricted l E X
    let c := isomorphismCompletedCoefficientComparison l E g
    obtain ⟨θ, _, _, hθ⟩ :=
      SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0} c
    let b : proEtaleRingModulePullback g R S c ≅
        isomorphismTermwiseModuleInverseImage g R S c :=
      NatIso.ofComponents (fun M ↦ θ ((proEtaleModuleInverseImage g R).obj M))
        (fun f ↦ hθ _ _ ((proEtaleModuleInverseImage g R).map f))
    obtain ⟨a⟩ := sectionwiseModuleAdjunction g
      (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficientSheafUnrestricted l E X)
      (ProEtale.inverseImageCompletedCoefficientMap l E g)
    let d := SheafOfModules.pushforwardCongr (completedSectionwiseDirectMap l E g)
    let e := (a.ofNatIsoRight d).leftAdjointUniq (proEtaleRingModuleAdjunction g R S c)
    let : (isomorphismTermwiseModuleInverseImage g R S c).Additive :=
      isomorphismTermwiseModuleInverseImage_additive g R S c
    let : PreservesFiniteLimits (isomorphismTermwiseModuleInverseImage g R S c) :=
      isomorphismTermwiseModuleInverseImage_preservesFiniteLimits g R S c
    let : PreservesFiniteColimits (isomorphismTermwiseModuleInverseImage g R S c) :=
      isomorphismTermwiseModuleInverseImage_preservesFiniteColimits g R S c
    exact ⟨Functor.mapDerivedCategoryNatIso (e ≪≫ b)⟩

private theorem integralConstantMembership (Y : Scheme.{u}) :
    sfIntegralConstructible l E Y (integralConstantCoefficientObject l E Y) ∧
      IsDerivedCompleteUnrestricted l E Y (integralConstantCoefficientObject l E Y) := by
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  exact ⟨(integralConstantCoefficient_constructible l E Y D hl).2.1,
    (integralConstantCoefficient_constructible l E Y D hl).2.2.1⟩

/-- Completed integral coefficients: termwise inverse image preserves the recorded
uniformly bounded constructible derived-complete subcategory, and agrees naturally
there with the specified completed derived pullback. The last clause is its
specialization to the completed coefficient sheaf in degree zero.
The natural isomorphism has source the recorded constructible integral pullback
and is stated in the full category D^b_c(X,O_E).
Source: blueprint order 1510; Bhatt--Scholze Definition 3.5.2; Stacks Tag 08TC
(blueprint: lem-weil-isomorphism-derived-pullback).
Proof:
1. Use the completed comparison fixed by the finite quotient projections. Exact
   relabelling transports module actions, tensor products and cohomology. It
   preserves flat terms and K-flatness by relabelling an acyclic test complex back.
2. Choose a K-flat resolution with flat terms (lem-pc-kflat-resolution). Tensor
   relabelling and the coefficient projection equations identify every finite
   reduction with the reduction of the relabelled resolution, including the maps
   x ↦ x tensor 1 and x tensor a ↦ x tensor rho(a). The identifications respect
   resolution comparisons by lem-weil-integral-reduction-tower-well-defined.
3. Exact countable products (lem-weil-proetale-countable-products-exact) represent
   derived products by lemma-reduction-derived-nakayama. For B(P)=product Res_n P_n,
   C(P)=Cone(1-s)[-1] has differential d(y,x)=(-d y-(1-s)x,d x). The quotient
   maps a:P→B(P) satisfy (1-s)a=0, so x ↦ (0,a(x)) is the canonical comparison.
   The L=E case of lem-weil-finite-free-completed-scalar-comparison says this
   comparison eta is natural and invertible on derived-complete objects.
4. Relabelling both coordinates commutes with this cone and its product
   projections, giving theta:Lg* K ≅ F C(P) for the actual construction of
   def-pur-integral-derived-operations. The normalized descent in
   lem-pur-integral-operations-well-defined gives naturality independent of
   resolutions. Compose theta with the inverse of F(eta) to get lambda.
5. Transport the defining Roos triangle and its quotient-unit first map to show
   completeness of FK. Every reduction is the finite inverse image of the old
   reduction. The finite case preserves constructibility and each vanishing
   degree, so the same single interval works for all reductions, exactly as in
   def-weil-derived-complete-integral-detailed. Fullness gives the required iso.
6. Specialize to the completed regular module in degree zero, whose membership
   is lem-weil-constant-coefficient-objects-constructible. Its auxiliary finite
   field can be chosen of any prime characteristic different from l; it imposes
   no structure morphism or restriction on X or Y. -/
theorem isomorphismIntegralDerivedPullback_termwise {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ h : ∀ K : DerivedCategory (scalarReductionSource l E Y),
      sfIntegralConstructible l E Y K →
        sfIntegralConstructible l E X ((isomorphismIntegralTermwiseInverseImage l E g).obj K),
    Nonempty (constructibleIntegralPullback l E g ≅
      (sfIntegralConstructible l E X).lift
        ((sfIntegralConstructible l E Y).ι ⋙ isomorphismIntegralTermwiseInverseImage l E g)
        (fun K ↦ h K.obj K.property)) ∧
    Nonempty ((integralDerivedPullback l E g).obj (integralConstantCoefficientObject l E Y) ≅
      (isomorphismIntegralTermwiseInverseImage l E g).obj
        (integralConstantCoefficientObject l E Y)) := by
  have hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (Invertible.ne_zero (l : X.residueField x))
  have hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := by
    intro y
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (Invertible.ne_zero (l : Y.residueField y))
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨θ, _, hθ, _⟩ := isomorphismDerivedPullbackComparisonNormalization l E g hX hY
    S hS (integralConstantCoefficientObject l E Y) (integralConstantMembership l E Y).2
  let I := (sfIntegralConstructible l E Y).ι
  let G := ProEtale.inverseImageIntegralDerived l E g
  let : ∀ K : sfIntegralConstructibleCategory l E Y,
      IsIso ((Functor.whiskerLeft I S.adjunction.unit).app K) :=
    fun K ↦ integralReconstructionUnit_isIso l E Y S K
  let : IsIso (Functor.whiskerLeft I S.adjunction.unit) :=
    NatIso.isIso_of_isIso_app _
  let a : I ⋙ integralDerivedPullback l E g ≅
      (I ⋙ (S.reduction ⋙ coefficientSequenceLimit l E Y)) ⋙ G :=
    NatIso.ofComponents (fun K ↦ θ K.obj) (fun f ↦ hθ _ _ f.hom)
  obtain ⟨b⟩ := integralSectionwiseComparison l E g
  let e : I ⋙ integralDerivedPullback l E g ≅
      I ⋙ isomorphismIntegralTermwiseInverseImage l E g :=
    a ≪≫ Functor.isoWhiskerRight (asIso (Functor.whiskerLeft I S.adjunction.unit)).symm G ≪≫
      Functor.isoWhiskerLeft I b
  let P := sfIntegralConstructible l E X
  let h := fun K (hK : sfIntegralConstructible l E Y K) ↦
    P.prop_of_iso (e.app ⟨K, hK⟩)
      ((integralOperations_preserve_constructible l E g).1 K hK).1
  refine ⟨h, ⟨?_, ?_⟩⟩
  · exact ⟨NatIso.ofComponents (fun K ↦ P.isoMk (e.app K)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact e.hom.naturality f)⟩
  · exact ⟨e.app ⟨integralConstantCoefficientObject l E Y,
      (integralConstantMembership l E Y).1⟩⟩

end WeilConjectures
