/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import WeilConjectures.WeilSheaf.Native.NativeCoherentInverseHomSquare
import WeilConjectures.WeilSheaf.Native.NativeFrobeniusCoherentRingedModel
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.SheafHomIdentityUnit
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedPresentation
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
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
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionUnderivedRestriction
import all WeilConjectures.SixFunctors.WeilFrobeniusAction.WeilFrobeniusActionResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # A ringed presentation of the underived native forgetful functor

Source: Stacks 00W0, 00YV, 06YS, 06YU and the Frobenius action-site construction.
This record contains no native derived tensor or derived tensor comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
attribute [local irreducible] SheafOfModules.monoidalCategory
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private noncomputable def transport_identity_hom
    {B D : Type*} [Category B] [Category D] (E : B ≌ D)
    (HB : Bᵒᵖ × B ⥤ B) (HD : Dᵒᵖ × D ⥤ D)
    (h : HB ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ HD)
    (B₀ : B) (e : Prod.sectR (op B₀) B ⋙ HB ≅ 𝟭 B) :
    Prod.sectR (op (E.functor.obj B₀)) D ⋙ HD ≅ 𝟭 D := by
  let h' : (Prod.sectR (op B₀) B ⋙ HB) ⋙ E.functor ≅
      E.functor ⋙ (Prod.sectR (op (E.functor.obj B₀)) D ⋙ HD) :=
    NatIso.ofComponents (fun Y ↦ h.app (op B₀, Y)) (fun f ↦ by
      simpa using h.hom.naturality (Prod.mkHom (𝟙 (op B₀)) f))
  exact (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
    Functor.isoWhiskerLeft E.inverse h'.symm ≪≫
    Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight e E.functor) ≪≫
    Functor.isoWhiskerLeft E.inverse (Functor.leftUnitor E.functor) ≪≫ E.counitIso

private theorem action_equivalence_exists
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (P : TwistedActionRingedSite.Presentation A.J A.s A.R A.a) :
    letI := P.category
    ∃ K : TwistedActionRingedSite.Modules P.coefficient ≌ ProEtaleWeilSheaf k₀ l X,
      K.functor = A.toWeil P := by
  let _ := P.category
  have : (Endofunctor.IsoAlgebra.mapOfNatIso A.comparison).IsEquivalence :=
    fixedPair_transport_equivalence A.E A.comparison
  have : (A.toWeil P).IsEquivalence := inferInstanceAs
    (P.modules.functor ⋙ Endofunctor.IsoAlgebra.mapOfNatIso A.comparison).IsEquivalence
  exact ⟨(A.toWeil P).asEquivalence, rfl⟩

/-- Present native forgetting on the Frobenius action site, before deriving any tensor.

Source: steps 1 and 2 of native tensor geometry; Stacks 00W0, 00YV, 06YS, 06YU,
and the action-site realization in lem-sf-weil-frobenius-action-resolutions.
(blueprint: lem-sf-native-weil-tensor-ringed-bridge).

Proof: take the small ordinary pro-etale site and its continuous coefficient ring
from the Frobenius realization. Form the semidirect action site with integer-labelled
arrows. Restriction to degree-zero arrows is the functor forget. The section-module
comparison on the ordinary site intertwines the two Frobenius pullbacks: both pull back
locally finite-subextension functions by the same precomposition. Lift it to fixed
pairs and compose with the action-site restriction equivalence to get native; its
ordinary counterpart gives ordinary. Retain its canonical tensor coherence through
the explicit inverse-Hom comparison. Their square is the restriction identification.
All component maps are the actual module maps, so the equivalences and restriction
are additive. Restriction creates limits and colimits and is exact; its exact orbit-sum
left adjoint implies preservation of K-injectives. The pure-tensor and local-map
formulas in the action-site presentation give underived. On a local Hom section,
both paths in hom_square are conjugation by the source and target Frobenius actions;
evaluation determines this comparison uniquely. Native Hom from adicConstant is
the identity. Transport it through the equivalence and use uniqueness of tensor's
left adjoint; evaluation at the unit gives nativeUnit. Finally ringed
pullback with invertible structural map preserves flat-term K-flat resolutions,
which is precisely preserves_flat_models. This condition is unchanged between the
normalized action-site presentations: their restriction equivalences preserve the
same tensor, coproducts and acyclic complexes. None of these operations uses a native
derived tensor. The zero module, empty site and all unbounded complexes are included. -/
theorem native_weil_tensor_ringed_bridge
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (NativeWeilTensorRingedBridge k₀ l X) := by
  let A := canonicalFrobeniusRingedModel k₀ l X
  have hA := native_frobenius_coherent_ringed_model k₀ l X
  obtain ⟨P⟩ := TwistedActionRingedSite.presentation A.J A.s A.R A.a
  let _ := P.category
  obtain ⟨⟨F, G, η, ε, htriangle⟩, hF⟩ := action_equivalence_exists A P
  change F = A.toWeil P at hF
  subst F
  have hK : (A.toWeil P).Additive := by
    constructor
    intro M N f g
    apply Endofunctor.IsoAlgebra.hom_ext
    change A.E.functor.map (P.modules.functor.map (f + g)).hom.f =
      A.E.functor.map (P.modules.functor.map f).hom.f +
        A.E.functor.map (P.modules.functor.map g).hom.f
    rw [P.modules_add]
    exact A.additive.map_add
  let K : TwistedActionRingedSite.Modules P.coefficient ≌ ProEtaleWeilSheaf k₀ l X :=
    { functor := A.toWeil P
      inverse := G
      unitIso := η
      counitIso := ε
      functor_unitIso_comp := htriangle }
  have : K.functor.Additive := hK
  have : K.inverse.Additive := K.inverse_additive
  have : A.E.functor.Additive := A.additive
  have : A.E.inverse.Additive := A.E.inverse_additive
  have : (TwistedActionRingedSite.sigma A.J A.s A.R A.a).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have : (TwistedActionRingedSite.sigma A.J A.s A.R A.a).IsEquivalence := by
    rw [← P.translation_eq]
    infer_instance
  let U := P.modules.functor ⋙ TwistedActionRingedSite.forgetPairs
    (TwistedActionRingedSite.sigma A.J A.s A.R A.a)
  have : P.modules.functor.Additive := by
    constructor
    intro M N f g
    apply Endofunctor.IsoAlgebra.hom_ext
    exact P.modules_add f g
  have : U.Additive := by
    constructor
    intro M N f g
    exact P.modules_add f g
  have : PreservesFiniteLimits U := by
    let _ := P.exact_limits
    infer_instance
  have : PreservesFiniteColimits U := by
    let _ := P.exact_colimits
    infer_instance
  have hproducts : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) U := by
    intro I
    let _ := P.createsLimits
    infer_instance
  have hcoproducts : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) U := by
    intro I
    let _ := P.createsColimits
    infer_instance
  have : U.PreservesKInjectiveComplexes := by
    have : P.induction.Additive := by
      constructor
      intro M N f g
      apply Endofunctor.IsoAlgebra.hom_ext
      exact P.induction_add f g
    let _ := P.induction_limits
    let _ := P.induction_colimits
    have : P.modules.symm.functor.Additive :=
      inferInstanceAs P.modules.inverse.Additive
    have : (P.modules.symm.inverse ⋙ TwistedActionRingedSite.forgetPairs
        (TwistedActionRingedSite.sigma A.J A.s A.R A.a)).Additive :=
      inferInstanceAs U.Additive
    exact (P.inductionAdjunction.comp P.modules.symm.toAdjunction).preservesKInjectiveComplexes
  obtain ⟨square, nativeHom, ordinaryHom, hcoherent, homsquare⟩ :=
    native_coherent_inverse_hom_square A hA P K rfl
  obtain ⟨d, hd⟩ := TwistedActionRingedSite.underived_restriction P
  refine ⟨{
    C := TwistedActionRingedSite.Object A.C
    categoryC := P.category
    J := P.topology
    R := P.coefficient
    A := A.C
    categoryA := A.category
    K := A.J
    Q := A.R
    native := K.symm
    ordinary := A.E.symm
    native_additive := inferInstanceAs K.inverse.Additive
    ordinary_additive := inferInstanceAs A.E.inverse.Additive
    forget := U
    forget_additive := inferInstance
    forget_limits := inferInstance
    forget_colimits := inferInstance
    forget_injectives := inferInstance
    forget_products := hproducts
    forget_coproducts := hcoproducts
    square := square
    underived := d
    nativeHom := nativeHom
    ordinaryHom := ordinaryHom
    ordinary_coherence := hcoherent
    hom_square := ?_
    nativeUnit := ?_
    preserves_flat_models := ?_ }⟩
  · intro M N
    change U.map (nativeHom.hom.app (op M, N)) ≫
        d.hom.hom.app (op (K.inverse.obj M), K.inverse.obj N) ≫
        SheafOfModules.homObjMap (R := A.R) (square.inv.app M) (square.hom.app N) ≫
        ordinaryHom.inv.app (op M.carrier, N.carrier) =
      square.hom.app (ihom k₀ l X M N)
    rw [hd]
    exact homsquare M N
  · let hconst : Prod.sectR (op (adicConstant k₀ l X)) _ ⋙
        Functor.uncurry.obj (ihomBifunctor k₀ l X) ≅ 𝟭 _ :=
      NatIso.ofComponents ihomAdicConstantIso (fun f ↦ by
        apply Endofunctor.IsoAlgebra.hom_ext
        change ((Mod.ihomMap (𝟙 _)).app _ ≫
          (ProEtale.AdicSheaf.ihom _).map f.hom.f) ≫
            Mod.ihomRegularIso.hom.app _ = Mod.ihomRegularIso.hom.app _ ≫ f.hom.f
        rw [Mod.ihomMap_id, NatTrans.id_app, Category.id_comp]
        exact Mod.ihomRegularIso.hom.naturality f.hom.f)
    let h := transport_identity_hom K.symm _ _ nativeHom (adicConstant k₀ l X) hconst
    exact Classical.choice (TwistedActionRingedSite.unit_iso_of_identity_hom
      P.coefficient (K.inverse.obj (adicConstant k₀ l X)) h)
  · intro L hL hterms
    obtain ⟨F, hF, adj, hflat, _⟩ := RingedToposMorphism.exists_kFlatPullback
      A.J P.topology A.R P.coefficient P.geometric
    let _ := hF
    let e : F ≅ U := adj.leftAdjointUniq P.modulePullback
    obtain ⟨h₁, h₂⟩ := hflat L
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat L).mp hL)
      (fun n ↦ (WeilFrobeniusAction.flat_comparison _).mpr (hterms n))
    let c := (NatIso.mapHomologicalComplex e (.up ℤ)).app L
    exact ⟨WeilFrobeniusAction.kflat_iso c
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr h₁),
      fun n ↦ WeilFrobeniusAction.flat_iso ((HomologicalComplex.eval _ (.up ℤ) n).mapIso c)
        ((WeilFrobeniusAction.flat_comparison _).mp (h₂ n))⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
