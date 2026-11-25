/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison
import all WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalProperScalarMateNormalization
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.FiniteScalarPreservation
import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarIsomorphism
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
/-! # The canonical finite coefficient left comparison

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-finite-scalar-left-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients CategoryTheory.Limits
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem change_eq_of_map {R S : PurCompactSupport.Coefficients.{u}}
    (a b : PurCompactSupport.Change R S) (h : ∀ T, a.map T = b.map T) : a = b := by
  cases a
  cases b
  congr
  funext T
  exact h T

-- The chosen derived presentations require an extended conversion budget.
/-- The proper/open comparison for a finite coefficient map is invertible on its finite-Tor domain.
Source: Zheng, Lemma 5.22; finite scalar mates, Construction 2.26 and Proposition 2.29.

Proof: finite scalar preservation supplies a bounded etale origin for K and for
its finite scalar extension. Reflect the cohomological interval through the finite-ring
site comparison. Exact open extension gives bounded-below models on the proper
compactification, and its scalar comparison shows that the tensor of the first
model is also bounded below. Apply the proper etale-origin scalar theorem. The
inverse mate interchange law identifies its geometric mate with the specified
properComparison. Transport along the canonical open presentation and site
isomorphisms, then combine with the invertible openComparison using the proper/open
factorization. No flatness of the quotient map or absolute separatedness is used.
(blueprint: lem-sf-finite-scalar-left-comparison). -/
theorem finiteScalarLeftComparison_isIso
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (E L : FieldStage.{u} l) (m n : ℕ+)
    (φ : Padic.coefficientExtensionRing l E.carrier m →+*
      Padic.coefficientExtensionRing l L.carrier n)
    (a : PurCompactSupport.Change
      ((RingStage.finite E m).coefficients l) ((RingStage.finite L n).coefficients l))
    (ha : ∀ T : Scheme.{u}, a.map T = proEtaleConstantRingMap (T := T) φ)
    (K : C.{u} l Ω X (.finite E m)) :
    IsIso ((PurCompactSupport.comparison a c).app K.obj)
    := by
  classical
  let b : PurCompactSupport.Change
      ((RingStage.finite E m).coefficients l) ((RingStage.finite L n).coefficients l) := {
    map := fun T ↦ proEtaleConstantRingMap (T := T) φ
    square := fun g ↦ (proEtaleConstantInverseImageMap_naturality g
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1, u, u} φ))).symm }
  have he : a = b := change_eq_of_map a b ha
  subst a
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero => omega
  | succ m =>
    cases n with
    | zero => omega
    | succ n =>
      let A := Padic.coefficientExtensionRing l E.carrier (m + 1)
      let B := Padic.coefficientExtensionRing l L.carrier (n + 1)
      have : Finite A := Padic.finite_coefficientExtensionRing l E.carrier (m + 1) hm
      have : Finite B := Padic.finite_coefficientExtensionRing l L.carrier (n + 1) hn
      let ρ := FiniteCompactScalar.scalarRingMap φ
      have hK := K.property.1
      have hred := (ExceptionalFiniteScalar.finiteScalar_preserves D l hl E.carrier
        L.carrier m n φ X K).1
      have : IsNoetherian Y := noetherianOfField D.k Y
      have : IsNoetherian c.Z := noetherianCompactification c
      have hKo : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} A) X) ⋙
          ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).essImage K.obj := by
        apply ((finiteRing_constructibleDerived_origin X A).2.2.1 K.obj).mpr
        obtain ⟨hs, hc⟩ := hK
        exact ⟨hc, (finite_homology_support_iff K.obj).mp hs⟩
      obtain ⟨G₀, ⟨eK⟩⟩ := hKo
      have hGplus : DerivedCategory.TStructure.t.plus G₀.obj := by
        obtain ⟨lo, hi, _, hv⟩ := G₀.property.2
        exact ⟨lo, (DerivedCategory.isGE_iff _ lo).mpr
          fun i hi ↦ hv i (Or.inl hi)⟩
      let G : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
        ⟨G₀.obj, hGplus⟩
      let LB := (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) X).obj G.obj
      let eB : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj LB ≅
          (pbcDerivedExtend (ρ X)).obj K.obj :=
        (FiniteCompactScalar.siteScalarIso (A := A) (B := B) φ X).symm.app G.obj ≪≫
          (pbcDerivedExtend (ρ X)).mapIso eK
      obtain ⟨lo, hi, _, hvred⟩ := (finite_homology_support_iff _).mp hred.1
      have hvB : ∀ i : ℤ, (i < lo ∨ hi < i) →
          IsZero ((DerivedCategory.homologyFunctor _ i).obj LB) := by
        apply ((finiteRing_constructibleDerived_origin X B).2.2.2 LB lo hi).mpr
        intro i hi
        exact (hvred i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eB)
      let GB : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
        ⟨LB, ⟨lo, (DerivedCategory.isGE_iff _ lo).mpr
          fun i hi ↦ hvB i (Or.inl hi)⟩⟩
      let H := (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategoryPlus.obj G
      let HB := (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.i).mapDerivedCategoryPlus.obj GB
      let eH : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) c.Z).obj H.obj ≅
          HB.obj := (Etale.FiniteCompactScalar.openScalarIso
            (RingHom.ulift.{u + 1, u + 1} φ) c.i).app G.obj
      have hH : ∃ b : ℤ, (ProEtale.properOriginEtaleTensor
          (RingHom.ulift.{u + 1, u + 1} φ) c.Z H.obj).IsGE b := by
        obtain ⟨b, hb⟩ := HB.property
        have : HB.obj.IsGE b := hb
        have : ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1} φ) c.Z).obj H.obj).IsGE b :=
          DerivedCategory.TStructure.t.isGE_of_iso eH.symm b
        have ht : ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) c.Z ⋙
            Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology
              (RingHom.ulift.{u + 1, u + 1} φ)).obj H.obj).IsGE b :=
          (Sheaf.restrictScalars c.Z.smallEtaleTopology
            (RingHom.ulift.{u + 1, u + 1} φ)).isGE_mapDerivedCategory_obj
              ((Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1} φ) c.Z).obj H.obj) b
        exact ⟨b, DerivedCategory.TStructure.t.isGE_of_iso
          ((Etale.scalarTensorIso (RingHom.ulift.{u + 1, u + 1} φ) c.Z).app H.obj) b⟩
      have hp := (ProEtale.properEtaleOriginScalarIsomorphism (A := A) (B := B) φ c.g H hH).1
      let M := (PurCompactSupport.openExtension
        (PurCompactSupport.finite l E.carrier (m + 1) hm) c.i).mapDerivedCategory.obj K.obj
      have hAdd : (sfIntrinsicExtensionByZero c.i
          (Padic.coefficientExtensionRing l E.carrier (m + 1))).Additive :=
        sfIntrinsicExtensionByZero_additive c.i _
      have hLim := sfIntrinsicExtensionByZero_preservesFiniteLimits c.i
        (Padic.coefficientExtensionRing l E.carrier (m + 1))
      have hColim := sfIntrinsicExtensionByZero_preservesFiniteColimits c.i
        (Padic.coefficientExtensionRing l E.carrier (m + 1))
      let eM : M ≅ (ProEtale.finiteCoefficientIntrinsicDerivedComparison c.Z A).obj H.obj :=
        (Functor.mapDerivedCategoryNatIso
          (PurCompactSupport.finiteOpenIso l E.carrier m c.i)).app K.obj ≪≫
        (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.mapIso eK.symm ≪≫
        (FiniteCompactScalar.openSiteIso A c.i).symm.app G.obj
      have hproper : IsIso ((PurCompactSupport.properComparison b c.g).app M) := by
        have hq : PurCompactSupport.properComparison b c.g =
            ProEtale.directImageScalarComparison φ c.g := by
          rw [properScalarMate_normalized]
          rfl
        rw [hq]
        have := hp
        exact IsIso.of_isIso_fac_left
          ((ProEtale.directImageScalarComparison φ c.g).naturality eM.inv)
      have hopen := PurCompactSupport.openComparison_isIso b c.i K.obj
      change IsIso ((PurCompactSupport.comparison b c).app K.obj)
      rw [PurCompactSupport.comparison_factorization]
      apply IsIso.comp_isIso' hproper
      infer_instance

end WeilConjectures.ExceptionalIntegralScalar
