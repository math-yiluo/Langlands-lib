/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralCoefficientFlat
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralCoefficientHeart
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Native constructibility of a finite integral tensor model

Source: Bhatt--Scholze, Proposition 6.8.11(3) and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-tensor-constructible).
The assertion concerns the explicit derived tensor functor, independently of
any normalized functor on the common-stage category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

attribute [local irreducible] sections CoefficientPresentation.integralMap

private theorem stratifiedFinitelyPresented_of_iso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {F G : pbcModules X (pbcAdicCompletion X d)} (e : F ≅ G)
    (hF : IsIntegralStratifiedFinitelyPresented X d F) :
    IsIntegralStratifiedFinitelyPresented X d G := by
  obtain ⟨s, hs⟩ := hF
  refine ⟨s, fun j ↦ ?_⟩
  obtain ⟨V, hV, h⟩ := hs j
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨N, hN, ⟨eN⟩⟩ := h U f hf
  exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion j) _).mapIso e.symm) ≪≫ eN⟩⟩

/-- Extension of a constructible complete integral complex to the native coefficient
has bounded constructible cohomology, read through the section-module equivalence.

Source: Bhatt--Scholze, Proposition 6.8.11(3), Proposition 6.8.14(2) and Lemma 6.8.2.
(blueprint: lem-sf-native-integral-tensor-constructible).

Proof in words: use the integral stratified-perfect characterization and its detailed
coefficient transport to obtain a bounded complex whose cohomology sheaves have
stratified finitely presented integral local models. The transport is exact and faithful,
so it reflects the bounds. Ordinary extension along C.integralMap is exact by
nativeIntegralCoefficient_flat and the scalar-extension adjunction. Hence its universal
left derived functor is canonically isomorphic to its termwise exact derived functor.
It preserves the bounds and commutes with cohomology. For each cohomology sheaf,
nativeIntegralCoefficient_heart takes its integral local models to native constructible
sheaves. The given isomorphism e and the exact section-module equivalence then transfer
both conclusions to M. The comparison on homology also transports the local-model
condition along the detailed coefficient isomorphism. Rank zero, the zero complex and
the empty scheme satisfy the same argument.
-/
theorem nativeIntegralTensor_constructible
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [IsCommMonObj (abRing l X)] [(sections l X).Additive]
    [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
    (E : Index l (PadicAlgCl l))
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (M : DerivedCategory (ProEtale.AdicSheaf l X))
    (e : (sections l X).mapDerivedCategory.obj M ≅
      (pbcDerivedExtend (C.integralMap l X)).obj K.obj) :
    ProEtale.DerivedCategory.boundedAdicConstructible l X M := by
  let A := Coefficient.{u} l (PadicAlgCl l) E
  let R := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison X l A).hom
  haveI : PreservesFiniteLimits R :=
    (integralDetailedCoefficientRestriction_exact X l A).1
  haveI : PreservesFiniteColimits R :=
    (integralDetailedCoefficientRestriction_exact X l A).2
  haveI : R.Additive := Functor.additive_of_preserves_binary_products _
  haveI : R.Faithful := by
    constructor
    intro F G f g h
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h
  have hunit : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤
    intro x hx
    simpa only [map_natCast] using (Fact.out : ∀ x : X,
      IsUnit (l : X.presheaf.stalk x)) x
  have hK := (integralStratifiedPerfectDetailed X l A Fact.out hunit K.obj).mp K.property
  have hmodels := (integralStratifiedPerfectCharacterization X l A
    Fact.out hunit ((integralDetailedTransport X l A).obj K.obj)).2.mp
      ((integralStratifiedPerfectCharacterization X l A
        Fact.out hunit ((integralDetailedTransport X l A).obj K.obj)).1.mp hK)
  obtain ⟨a, b, _, ha, hb⟩ := hmodels.1
  have hbounded : DerivedCategory.TStructure.t.bounded K.obj := by
    apply R.bounded_of_bounded_mapDerivedCategory_obj
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  let T := pbcExtend (C.integralMap l X)
  haveI : PreservesFiniteLimits T :=
    nativeIntegralCoefficient_flat l X A (embedding l E) C
  haveI : PreservesColimitsOfSize.{0, 0} T :=
    (pbcScalarAdjunction (C.integralMap l X)).leftAdjoint_preservesColimits
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : (pbcDerivedExtend (C.integralMap l X)).IsLeftDerivedFunctor
      (pbcExtensionCounit (C.integralMap l X))
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    pbcDerivedExtension_universal (C.integralMap l X)
  haveI : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let d : pbcDerivedExtend (C.integralMap l X) ≅ T.mapDerivedCategory :=
    Functor.leftDerivedNatIso _ _ (pbcExtensionCounit (C.integralMap l X))
      T.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)
  let q := e ≪≫ d.app K.obj
  haveI : (ProEtale.AdicSheaf.forgetAb l X).IsEquivalence :=
    ProEtale.nativeScalarForgetting_isEquivalence l X
  haveI : (sections l X).IsEquivalence := by
    unfold sections
    infer_instance
  refine ⟨(sections l X).bounded_of_bounded_mapDerivedCategory_obj
    ((DerivedCategory.TStructure.t.bounded).prop_of_iso q.symm
      (T.bounded_mapDerivedCategory_obj hbounded)), fun n ↦ ?_⟩
  let N := (DerivedCategory.homologyFunctor _ n).obj K.obj
  have hn : IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l A) (R.obj N) :=
    stratifiedFinitelyPresented_of_iso X _
      (((R.mapDerivedCategoryHomologyFunctorIso n).app K.obj).symm) (hmodels.2 n)
  apply nativeIntegralCoefficient_heart l X A (embedding l E) C N hn
  exact ((sections l X).mapDerivedCategoryHomologyFunctorIso n).app M ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso q ≪≫
      ((T.mapDerivedCategoryHomologyFunctorIso n).app K.obj).symm

end WeilConjectures.LocallyFiniteAdicRealization
