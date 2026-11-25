/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.NativeOpenTensorPrimitives.CoefNativeOpenTensorPrimitives
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeFiniteTensorSupport
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization

/-! # Existence of finite native open tensor data

This is the finite coefficient-stage part of the construction in
[sites-cohomology.tex, Tag 0GL1], separated from the sequence-site datum.
(blueprint: lem-coef-native-open-tensor-finite-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
set_option relaxedAutoImplicit false
universe u u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.CoefSupportOpenTensor

private theorem adjoint_tensor_natural
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (G : B ⥤ A) (adj : F ⊣ G)
    (ρ : ∀ M N : B, G.obj (M ⊗ N) ≅ G.obj M ⊗ G.obj N)
    (hρ : ∀ {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      G.map (f ⊗ₘ g) ≫ (ρ M' N').hom =
        (ρ M N).hom ≫ (G.map f ⊗ₘ G.map g))
    {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N') :
    F.map (f ⊗ₘ G.map g) ≫
        (adj.homEquiv _ _).symm ((adj.unit.app M' ⊗ₘ 𝟙 (G.obj N')) ≫
          (ρ (F.obj M') N').inv) =
      (adj.homEquiv _ _).symm ((adj.unit.app M ⊗ₘ 𝟙 (G.obj N)) ≫
        (ρ (F.obj M) N).inv) ≫ (F.map f ⊗ₘ g) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  have hi : (G.map (F.map f) ⊗ₘ G.map g) ≫ (ρ (F.obj M') N').inv =
      (ρ (F.obj M) N).inv ≫ G.map (F.map f ⊗ₘ g) := by
    apply (cancel_mono (ρ (F.obj M') N').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hρ, Iso.inv_hom_id_assoc]
  have hu : f ≫ adj.unit.app M' = adj.unit.app M ≫ G.map (F.map f) :=
    adj.unit.naturality f
  have ht : (f ⊗ₘ G.map g) ≫ (adj.unit.app M' ⊗ₘ 𝟙 (G.obj N')) =
      (adj.unit.app M ⊗ₘ 𝟙 (G.obj N)) ≫ (G.map (F.map f) ⊗ₘ G.map g) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hu]
    simp only [Category.id_comp, Category.comp_id]
  rw [← Category.assoc, ht, Category.assoc, hi, ← Category.assoc]

private theorem nativePull_preservesKFlat {X Z : Scheme.{u}} (j : X ⟶ Z)
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules Z R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Z) (R := R) P)
    (hf : flatTerms.{u + 1, u, u} (ProEt.topology Z) R P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := S)
        (((proEtaleRingModulePullback j R S c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      flatTerms.{u + 1, u, u} (ProEt.topology X) S
        (((proEtaleRingModulePullback j R S c).mapHomologicalComplex (.up ℤ)).obj P) := by
  have : PreservesFiniteLimits (proEtaleSheafInverseImage j (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage j (𝟙 Z)).2.2.2.1
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists j R
  let T := I.modules ⋙ proEtaleRingExtension j R S c
  have hT : T = proEtaleRingModulePullback j R S c := by
    dsimp only [T]
    rw [hI]
    rfl
  have : T.Additive := by rw [hT]; infer_instance
  have hobj (M) : T.obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (f : M ⟶ N), T.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom
        (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm := by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hp := SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage j (Type (u + 1)))
    (proEtaleSheafDirectImage j (Type (u + 1)))
    (proEtaleSheafAdjunction j (Type (u + 1))) I c.hom T hobj hmap P hP hf
  have transfer
      (F₁ F₂ : proEtaleRingModules Z R ⥤ proEtaleRingModules X S)
      [F₁.Additive] [F₂.Additive] (h : F₁ = F₂)
      (hp : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := S)
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ∧
        flatTerms.{u + 1, u, u} (ProEt.topology X) S
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) :
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := S)
          ((F₂.mapHomologicalComplex (.up ℤ)).obj P) ∧
        flatTerms.{u + 1, u, u} (ProEt.topology X) S
          ((F₂.mapHomologicalComplex (.up ℤ)).obj P) := by
    subst F₂
    exact hp
  exact transfer T (proEtaleRingModulePullback j R S c) hT hp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- Preserve the existing existential binder, whose witness is intentionally unrestricted.
set_option linter.unusedVariables false in
/-- Every positive finite coefficient stage admits the native open tensor datum.
Source: Stacks sites-modules.tex 0E8I, sites-cohomology.tex 0GL1 and 0G7E,
and Homology 012Z.
(blueprint: lem-coef-native-open-tensor-finite-existence).

Proof: localize the ambient pro-etale site at the open object. An object
of the open site is sent to its composite with j; its inverse is supplied by
factorization through the open. Covers are unchanged. The constant-ring
identification is the identity on constant sections, so the coefficient ring
on the open is the restricted ambient coefficient ring. Transport the
localized module restriction and extension along these site and ring
identifications. The direct-sum insertion and sheafification units agree
with the specified native unit, which identifies the adjunctions. Take right
to be the native module direct image, with its restriction adjunction.

Restriction takes a pure tensor to the tensor of its restricted sections.
The balanced tensor universal property, followed by sheafification, gives
pullTensor and its inverse. Checking on pure tensors proves pullPure and
pullNaturality. Apply ringed-topos pullback preservation of flat-term K-flat
complexes to this restriction: its two conclusions give pullKFlat and pullFlat.

For M on the open and N on the ambient site, transpose unit_M tensor identity
followed by pullTensor inverse under the native extension adjunction. The native
open unit is invertible, so extension is fully faithful. The localized tensor
formula of 0E8I shows that extension M tensor N lies in its essential image.
Its counit is therefore invertible. The transpose is extension of the invertible
adjunct followed by that counit, hence is itself invertible. Take the inverse
of this isomorphism as ordinary. The adjunction Hom equivalence proves
ordinaryInverse. Naturality of the unit and pullTensor, and injectivity of the
Hom equivalence, give ordinaryNaturality.

In total degree k, take the direct sum over a+b=k of the ordinary comparison.
Extension preserves these sums because it is a left adjoint. Define the inverse
by the direct sum of the inverses. Naturality of the ordinary comparison for
the two differentials shows that these maps commute with d tensor 1 and with
(-1)^a times 1 tensor d, hence are inverse chain maps. Their definition on
coproduct insertions proves summand; ordinary naturality on each insertion
proves chainNaturality. This is the totalization argument of 0GL1/012Z.

Fix n throughout and use the constant sheaf of compactSupportSystemLevel l E n.
The transported functors are StrictTower.moduleJ and modulePullback, and the
constant-section identification is StrictTower.constantRingIso. Thus the
section equation is exactly the one specified by finitePullSection. This
construction needs neither a sequence-site datum nor compatibility between
different n. The case n=0 is the first positive quotient, not a zero-th power.
The empty open and the zero coefficient ring satisfy the same formulas. -/
theorem nativeOpenTensor_finite_exists {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    ∃ Dn : NativeOpenTensorPrimitives.FiniteOpenCochainsData l E j n, True := by
  let B := compactSupportSystemLevel l E n
  let RZ := ProEtale.StrictTower.coefficients B Z
  let RX := ProEtale.StrictTower.coefficients B X
  let F := ProEtale.StrictTower.moduleJ B j
  let G := ProEtale.StrictTower.modulePullback B j
  let a := ProEtale.StrictTower.moduleJAdj B j
  let A := proEtaleRingModules X RX
  let C := proEtaleRingModules Z RZ
  let : EssentiallySmall.{u + 1} X.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures X
  let : EssentiallySmall.{u + 1} Z.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures Z
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1} (ProEt.topology X)
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1} (ProEt.topology Z)
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology X)
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology Z)
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let := SheafOfModules.isMonoidal_W_independentCoefficients RZ
  let := SheafOfModules.monoidalCategory RX
  let := SheafOfModules.monoidalCategory RZ
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients RX
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients RZ
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients RX
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients RZ
  let : F.Additive := ProEtale.StrictTower.moduleJ_additive B j
  let : PreservesFiniteLimits F := ProEtale.StrictTower.moduleJ_finiteLimits B j
  let : PreservesFiniteColimits F := ProEtale.StrictTower.moduleJ_finiteColimits B j
  let : G.Additive := proEtaleRingModulePullback_additive j RZ RX
    (ProEtale.StrictTower.constantRingIso B j)
  let : PreservesFiniteLimits G := proEtaleRingModulePullback_preservesFiniteLimits j RZ RX
    (ProEtale.StrictTower.constantRingIso B j)
  let : PreservesFiniteColimits G := proEtaleRingModulePullback_preservesFiniteColimits j RZ RX
    (ProEtale.StrictTower.constantRingIso B j)
  let : F.IsLeftAdjoint := a.isLeftAdjoint
  obtain ⟨ρ, ⟨hρ', hPure'⟩, _⟩ := proEtaleOrdinaryTensorPullback_existsUnique
    j RZ RX (ProEtale.StrictTower.constantRingIso B j)
  have hρ {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N') :
      G.map (f ⊗ₘ g) ≫ (ρ M' N').hom =
        (ρ M N).hom ≫ (G.map f ⊗ₘ G.map g) := by
    simpa only [G, ProEtale.StrictTower.modulePullback, proEtaleOrdinaryTensor,
      curriedTensor, tensorHom_def, Category.assoc] using
      hρ' M M' N N' f g
  have hPure (M N : C) (V : Z.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
      (ρ M N).hom.val.app ((proEtaleBaseChange j).op.obj V)
          (finitePullSection l E j n (ordinaryTensor.{u + 1, u, u}
            (ProEt.topology Z) RZ M N) V
              (tensorSection.{u + 1, u, u} (ProEt.topology Z) RZ M N V x y)) =
        tensorSection.{u + 1, u, u} (ProEt.topology X) RX (G.obj M) (G.obj N)
          ((proEtaleBaseChange j).op.obj V)
          (finitePullSection l E j n M V x) (finitePullSection l E j n N V y) :=
    hPure' M N V.unop x y
  let p (M : A) (N : C) : F.obj (M ⊗ G.obj N) ⟶ F.obj M ⊗ N :=
    (a.homEquiv _ _).symm ((a.unit.app M ⊗ₘ 𝟙 (G.obj N)) ≫ (ρ (F.obj M) N).inv)
  let : IsIso a.unit := ProEtale.StrictTower.openBetaModuleJUnit B j
  let ff := a.fullyFaithfulLOfIsIsoUnit
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  have hp (M : A) (N : C) : IsIso (p M N) := by
    have : IsIso (a.counit.app (F.obj M ⊗ N)) :=
      a.isIso_counit_app_iff_mem_essImage.mpr (nativeFiniteTensor_mem_essImage l E j n M N)
    dsimp only [p]
    rw [Adjunction.homEquiv_counit]
    infer_instance
  let e (M : A) (N : C) : F.obj (M ⊗ G.obj N) ≅ F.obj M ⊗ N :=
    @asIso _ _ _ _ (p M N) (hp M N)
  have he {M M' : A} {N N' : C} (f : M ⟶ M') (g : N ⟶ N') :
      F.map (f ⊗ₘ G.map g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map f ⊗ₘ g) :=
    adjoint_tensor_natural F G a ρ hρ f g
  let H := curriedTensor A
  let H' := curriedTensor C
  let := SheafOfModules.precompose_preservesZero H G
  let (M : A) := SheafOfModules.precompose_obj_preservesZero H G M
  let (P : CochainComplex A ℤ) (Q : CochainComplex C ℤ) :=
    SheafOfModules.precompose_hasTotal H G P Q
  let τ : (Functor.postcompose₂.obj F).obj
      (H ⋙ (Functor.whiskeringLeft C A A).obj G) ≅
      (((Functor.whiskeringLeft₂ C).obj F).obj (𝟭 C)).obj H' :=
    SheafOfModules.bifunctorIsoOfComponents _ _ e (by
      intro M M' N N' f g
      change F.map (f ▷ G.obj N) ≫ F.map (M' ◁ G.map g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map f ▷ N) ≫ (F.obj M' ◁ g)
      rw [← Category.assoc, ← F.map_comp]
      simpa only [← tensorHom_def, Category.assoc] using he f g)
  obtain ⟨Φ, hι, hn⟩ := SheafOfModules.comparisonPrecompose_exists F G H H' τ
  refine ⟨{
    right := proEtaleRingModuleDirectImage j RZ RX (ProEtale.StrictTower.constantRingIso B j)
    pullAdjunction := proEtaleRingModuleAdjunction j RZ RX
      (ProEtale.StrictTower.constantRingIso B j)
    pullTensor := ρ
    pullNaturality := hρ
    pullPure := hPure
    pullKFlat := fun P hP hf ↦ (nativePull_preservesKFlat j RZ RX
      (ProEtale.StrictTower.constantRingIso B j) P hP hf).1
    pullFlat := fun P hP hf ↦ (nativePull_preservesKFlat j RZ RX
      (ProEtale.StrictTower.constantRingIso B j) P hP hf).2
    ordinary := fun M N ↦ (e M N).symm
    ordinaryInverse := ?_
    ordinaryNaturality := ?_
    chain := fun P Q ↦ (Φ P Q).symm
    summand := ?_
    chainNaturality := ?_
  }, trivial⟩
  · intro M N
    exact (a.homEquiv _ _).apply_symm_apply _
  · intro M M' N N' f g
    simpa only [ordinaryTensorHom, Iso.symm_hom] using
      SheafOfModules.inverse_square (e M N) (e M' N') _ _ (he f g)
  · intro P Q b c k h
    have hi := hι P Q b c k h
    simp only [τ, SheafOfModules.bifunctorIsoOfComponents_hom] at hi
    simpa only [tensorSummand, Iso.symm_hom, Functor.mapIso_inv,
      HomologicalComplex.eval_map] using
      SheafOfModules.inverse_square (e (P.X b) (Q.X c))
        ((HomologicalComplex.eval C (.up ℤ) k).mapIso (Φ P Q)) _ _ hi
  · intro P P' Q Q' f g
    simpa only [totalTensor, coefficientTotalTensor, Functor.uncurry_obj_map,
      Iso.symm_hom] using
      SheafOfModules.inverse_square (Φ P Q) (Φ P' Q') _ _ (hn P P' Q Q' f g)

end WeilConjectures.CoefSupportOpenTensor
