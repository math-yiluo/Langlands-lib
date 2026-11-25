/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Published.PublishedSystemAmbientPresentation
import WeilConjectures.SixFunctors.PublishedTensorNormalization.PublishedTensorModelRepresentativeTransport
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all WeilConjectures.SixFunctors.System.SystemPullbackCompositorIdentification

/-! Representative normalization for the transported ambient tensor comparison.
Source: Stacks 03D3, 03EL, 07A4 and 07A7.
(blueprint: lem-sf-published-system-tensor-identification-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor
namespace WeilConjectures

/-- Generic component cancellation for transport of a tensor comparison along an
isomorphism of inverse-image functors. -/
theorem tensor_comparison_transport_hom_eq
    {A B : Type*} [Category A] [Category B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (F G : A ⥤ B) (d : F ≅ G)
    (m : TA ⋙ F ≅ (F.prod F) ⋙ TB)
    (n : TA ⋙ G ≅ (G.prod G) ⋙ TB)
    (h : (Functor.isoWhiskerLeft TA d ≪≫ n ≪≫
        Functor.isoWhiskerRight (NatIso.prod d d).symm TB) = m) :
    ∀ M N, d.hom.app (TA.obj (M, N)) ≫ n.hom.app (M, N) =
      m.hom.app (M, N) ≫ TB.map (Prod.mkHom (d.hom.app M) (d.hom.app N)) := by
  intro M N
  have hh := congrArg (fun e ↦ e.hom.app (M, N)) h
  calc
    d.hom.app (TA.obj (M, N)) ≫ n.hom.app (M, N) =
        d.hom.app (TA.obj (M, N)) ≫ n.hom.app (M, N) ≫
          TB.map ((NatIso.prod d d).inv.app (M, N)) ≫
          TB.map ((NatIso.prod d d).hom.app (M, N)) := by
      rw [← TB.map_comp]
      simp [NatIso.prod]
    _ = (Functor.isoWhiskerLeft TA d ≪≫ n ≪≫
        Functor.isoWhiskerRight (NatIso.prod d d).symm TB).hom.app (M, N) ≫
          TB.map ((NatIso.prod d d).hom.app (M, N)) := by
      simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
        NatTrans.comp_app, NatIso.prod, Iso.symm_hom, Category.assoc]
    _ = m.hom.app (M, N) ≫
          TB.map ((NatIso.prod d d).hom.app (M, N)) := by
      rw [hh]
    _ = m.hom.app (M, N) ≫ TB.map (Prod.mkHom (d.hom.app M) (d.hom.app N)) := by
      rfl

namespace PublishedTensorNormalization
/-- Equality of right adjoints identifies their specified chosen adjunctions. -/
private theorem chosen_adj_heq {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) [F.IsRightAdjoint] [G.IsRightAdjoint] (h : F = G) :
    HEq (Adjunction.ofIsRightAdjoint F) (Adjunction.ofIsRightAdjoint G) := by
  subst G
  rfl

end PublishedTensorNormalization

universe w v

/-- Isomorphism components respect equal category presentations. -/
private theorem iso_hom_app_heq {C C' D D' : Type w}
    [cC : Category.{v} C] [cC' : Category.{v} C']
    [cD : Category.{v} D] [cD' : Category.{v} D']
    (hC : C = C') (hD : D = D') (hcc : HEq cC cC') (hdc : HEq cD cD')
    {F G : C ⥤ D} {F' G' : C' ⥤ D'}
    (hF : HEq F F') (hG : HEq G G')
    {e : F ≅ G} {e' : F' ≅ G'} (he : HEq e e')
    {X : C} {X' : C'} (hX : HEq X X') :
    HEq (e.hom.app X) (e'.hom.app X') := by
  subst C'
  subst D'
  cases eq_of_heq hcc
  cases eq_of_heq hdc
  cases eq_of_heq hF
  cases eq_of_heq hG
  cases eq_of_heq he
  cases eq_of_heq hX
  rfl

/-- Transport a six-edge rectangle across equal category presentations. -/
private theorem rectangle_transfer {C D : Type w}
    [cC : Category.{v} C] [cD : Category.{v} D]
    {X0 X1 X2 X3 X4 X5 : C}
    {a : X0 ⟶ X1} {b : X1 ⟶ X2} {c : X2 ⟶ X3}
    {d : X0 ⟶ X4} {e : X4 ⟶ X5} {f : X5 ⟶ X3}
    (h : a ≫ b ≫ c = d ≫ e ≫ f)
    (hCD : C = D) (hcat : HEq cC cD)
    {Y0 Y1 Y2 Y3 Y4 Y5 : D}
    (a' : Y0 ⟶ Y1) (b' : Y1 ⟶ Y2) (c' : Y2 ⟶ Y3)
    (d' : Y0 ⟶ Y4) (e' : Y4 ⟶ Y5) (f' : Y5 ⟶ Y3)
    (h0 : HEq X0 Y0) (h1 : HEq X1 Y1) (h2 : HEq X2 Y2)
    (h3 : HEq X3 Y3) (h4 : HEq X4 Y4) (h5 : HEq X5 Y5)
    (ha : HEq a a') (hb : HEq b b') (hc : HEq c c')
    (hd : HEq d d') (he : HEq e e') (hf : HEq f f') :
    a' ≫ b' ≫ c' = d' ≫ e' ≫ f' := by
  subst D
  cases eq_of_heq hcat
  cases eq_of_heq h0
  cases eq_of_heq h1
  cases eq_of_heq h2
  cases eq_of_heq h3
  cases eq_of_heq h4
  cases eq_of_heq h5
  cases eq_of_heq ha
  cases eq_of_heq hb
  cases eq_of_heq hc
  cases eq_of_heq hd
  cases eq_of_heq he
  cases eq_of_heq hf
  exact h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the ambient tensor comparison back along the specified inverse-image
identification. Its representative normalization is the remaining chain-level step
in the proof of the published-system tensor identification. -/
noncomputable def publishedSystemTransportedTensor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        pullbackTensorSequenceDerived l E f ≅
      ((pullbackTensorSequenceDerived l E f).prod
        (pullbackTensorSequenceDerived l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor :=
  (isoWhiskerLeft (pullbackTensorCalculus l E Y).systemClosed.tensor
      (publishedSystemAmbientPullIso l E f)) ≪≫
    (publishedSystemAmbientData l E).tensor f ≪≫
    (Functor.isoWhiskerRight
      (NatIso.prod (publishedSystemAmbientPullIso l E f)
        (publishedSystemAmbientPullIso l E f)).symm
      (pullbackTensorCalculus l E X).systemClosed.tensor)

attribute [local irreducible] publishedSystemTransportedTensor
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  AmbientPullbackTensor.siteSmall
attribute [local irreducible] AmbientPullbackTensor.tensorData AmbientPullbackTensor.pull
  pullbackTensorSequenceInverse Functor.leftAdjoint

/-- The ambient representative rectangle on flat-term K-flat complexes. This is the
flat representative part of the descent argument for arbitrary K-flat complexes.
Source: Stacks 03D3, 03EL, 07A4 and 07A7.
(blueprint: lem-sf-published-system-tensor-identification-representative-flat).

Proof: the constant-section coefficient formulas identify the two direct images,
so their chosen left adjoints and the adjunction units agree after transport.
The ambient ordinary comparison sends the unit of a pure tensor to the tensor
of the two units. On a total summand in degrees p,q, its chain model is the
inverse of this ordinary comparison followed by the pulled-back summand inclusion.
Naturality of the adjunction unit at that inclusion therefore shows that the inverse
chain map satisfies the unit formula defining pullbackTensorSequenceCochain. The
signed total differential is already built into both chain maps. Adjunction and
pure-tensor extensionality in every summand, or the uniqueness clause of that
cochain comparison, identify the inverse chain map with the specified cochain map.
In the ambient model's derived equation, invert the chain isomorphism and cancel
the four model and exact-localization isomorphisms to obtain the forward rectangle.
Finally transport back along sequence_inverse_eq; the induced equality on exact
derived functors is publishedSystemAmbientPullIso, so its component transports
are precisely those in publishedSystemTransportedTensor. K-flat preservation
identifies the target model, independently of its proof witness.
-/
theorem publishedSystemTransportedTensor_normalized_flat {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) Q)
    (flatP : SemilinearSections.flatTerms.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P)
    (flatQ : SemilinearSections.flatTerms.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) Q) :
    (pullbackTensorSequenceDerived l E f).map
        (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
      (publishedSystemTransportedTensor l E f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
      (pullbackTensorSystemModel l E X _ _
        (pullbackTensorSequenceGood l E f P hP)
        (pullbackTensorSequenceGood l E f Q hQ)).hom := by
  let : (AmbientPullbackTensor.push.{u, u} l E f none).IsRightAdjoint :=
    AmbientPullbackTensor.pushRightAdjoint.{u, u} l E f none
  let : (AmbientPullbackTensor.pull.{u, u} l E f none).Additive :=
    AmbientPullbackTensor.pullAdditive.{u, u} l E f none
  let : CategoryTheory.Limits.PreservesFiniteLimits
      (AmbientPullbackTensor.pull.{u, u} l E f none) :=
    AmbientPullbackTensor.pullLimits.{u, u} l E f none
  let : CategoryTheory.Limits.PreservesFiniteColimits
      (AmbientPullbackTensor.pull.{u, u} l E f none) :=
    AmbientPullbackTensor.pullColimits.{u, u} l E f none
  let data := AmbientPullbackTensor.tensorData.{u, u} l E f none
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed
    (pullbackTensorCalculus l E Y).systemTensorModel
    (pullbackTensorCalculus l E X).systemTensorModel
  have hn : AmbientPullbackTensor.TensorData.Normalized.{u, u} l E f none
      (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed
      (pullbackTensorCalculus l E Y).systemTensorModel
      (pullbackTensorCalculus l E X).systemTensorModel data := by
    dsimp only [data]
    unfold AmbientPullbackTensor.tensorData
    exact (AmbientPullbackTensor.tensorData_existsUnique.{u, u} l E f none
      (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed
      (pullbackTensorCalculus l E Y).systemTensorModel
      (pullbackTensorCalculus l E X).systemTensorModel).exists.choose_spec
  have ho : ∀ (M N : coefficientSequenceModules l E Y) (V : ℕ × Y.ProEt)
    (x : M.val.obj (op V)) (y : N.val.obj (op V)),
    ((data.model.ordinary M N).hom.val.app (op ((pullbackTensorSequenceBase f).obj V)))
      (((AmbientPullbackTensor.adjunction.{u, u} l E f none).unit.app
        (SemilinearSections.ordinaryTensor.{u + 1, u, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) M N)).val.app (op V)
        (SemilinearSections.tensorSectionAtSize
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) M N (op V) x y)) =
      SemilinearSections.tensorSectionAtSize
        (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        ((AmbientPullbackTensor.pull.{u, u} l E f none).obj M)
        ((AmbientPullbackTensor.pull.{u, u} l E f none).obj N)
        (op ((pullbackTensorSequenceBase f).obj V))
        (((AmbientPullbackTensor.adjunction.{u, u} l E f none).unit.app M).val.app (op V) x)
        (((AmbientPullbackTensor.adjunction.{u, u} l E f none).unit.app N).val.app (op V) y) := by
    intro M N V x y
    have h' := hn.1 M N V ((AmbientPullbackTensor.base.{u} f none).obj V)
      (𝟙 _) x y 1
    simpa only [AmbientPullbackTensor.generator, AmbientPullbackTensor.tensor,
      AmbientPullbackTensor.pure, SMul.smul_eq_hSMul, one_smul, op_id, PresheafOfModules.map_id,
      ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply,
      AmbientPullbackTensor.base, AmbientPullbackTensor.topology,
      AmbientPullbackTensor.coefficients, pullbackTensorSequenceBase] using h'
  have hadj : HEq (pullbackTensorSequenceAdjunction l E f)
      (AmbientPullbackTensor.adjunction.{u, u} l E f none) := by
    unfold pullbackTensorSequenceAdjunction pullbackTensorSequenceInverse
      AmbientPullbackTensor.adjunction AmbientPullbackTensor.pull
    with_unfolding_all exact
      PublishedTensorNormalization.chosen_adj_heq _ _ (sequence_direct_eq l E f)
  have hmuy : data.mu = (publishedSystemAmbientData l E).tensor f := by
    rfl
  have hmodel (W : Scheme.{u})
      (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hp : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P)
      (hq : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) Q) :
      SemilinearSections.tensorModelIso.{u + 1, u, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel P Q hp hq =
        pullbackTensorSystemModel l E W P Q hp hq := by
    rfl
  have ht0 := PublishedTensorNormalization.model_transport_named.{u + 1, u, u}
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceTopology (ProEt.topology X))
    (pullbackTensorSequenceBase f)
    (coefficientSequenceCommRingSheaf l E Y)
    (coefficientSequenceCommRingSheaf l E X)
    (pullbackTensorSequenceRing l E f) (AmbientPullbackTensor.ringUnit.{u, u} l E f none)
    (sequence_ring_eq l E f)
    (pullbackTensorSequenceInverse l E f) (AmbientPullbackTensor.pull.{u, u} l E f none)
    (sequence_inverse_eq l E f)
    (pullbackTensorSequenceAdjunction l E f) (AmbientPullbackTensor.adjunction.{u, u} l E f none)
    hadj
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed
    (pullbackTensorCalculus l E Y).systemTensorModel
    (pullbackTensorCalculus l E X).systemTensorModel
    data.mu data.model hn.2.2.1
    (pullbackTensorSequenceCochain l E f) ho
    (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
    (publishedSystemAmbientPullIso l E f)
    ⟨publishedSystemAmbientPull_eq.{u} l E f, by unfold publishedSystemAmbientPullIso; rfl⟩
    P Q hP hQ flatP flatQ
    (pullbackTensorSequenceGood l E f P hP) (pullbackTensorSequenceGood l E f Q hQ)
  have ht1 := ht0 (pullbackTensorSequenceDerived l E f) rfl
  have ht2 := ht1
    ((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q)) rfl
  have ht3 := ht2
    ((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)).obj
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P,
        ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj Q)) rfl
  have ht4 := ht3
    (pullbackTensorSystemModel l E Y P Q hP hQ)
    (heq_of_eq (hmodel Y P Q hP hQ).symm)
    (pullbackTensorSystemModel l E X _ _
      (pullbackTensorSequenceGood l E f P hP) (pullbackTensorSequenceGood l E f Q hQ))
    (heq_of_eq (hmodel X _ _
      (pullbackTensorSequenceGood l E f P hP) (pullbackTensorSequenceGood l E f Q hQ)).symm)
  have ht5 := ht4
    (publishedSystemTransportedTensor l E f)
    (by rw [hmuy]; unfold publishedSystemTransportedTensor; rfl)
  have ht6 := ht5
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors (by rfl)
  have ht := ht6
    ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) (by rfl)
  have hf0 := rectangle_transfer ht (D := coefficientSequenceDerived l E X)
  have hf1 := hf0 rfl
  have hf2 := @hf1 (by rfl)
  have hf3 := hf2
    ((pullbackTensorSequenceDerived l E f).map
      (pullbackTensorSystemModel l E Y P Q hP hQ).hom)
    ((publishedSystemTransportedTensor l E f).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    ((pullbackTensorCalculus l E X).systemClosed.tensor.map
      (Prod.mkHom ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)))
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q)))
    (DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)))
    ((pullbackTensorSystemModel l E X _ _
      (pullbackTensorSequenceGood l E f P hP)
      (pullbackTensorSequenceGood l E f Q hQ)).hom)
  have hf4 := hf3 (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have he1 := hf4 (by rfl)
  have he2 := he1 (by apply iso_hom_app_heq <;> rfl)
  have he3 := he2 (by rfl)
  have he4 := he3 (by rfl)
  have he5 := he4 (by rfl)
  have hfinal := he5 (by rfl)
  exact hfinal

/-- Faithful restriction and cancellation, with both comparisons abstract. -/
private theorem tensor_comparison_eq_of_flat_rectangles {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (m n : (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        pullbackTensorSequenceDerived l E f ≅
      ((pullbackTensorSequenceDerived l E f).prod
        (pullbackTensorSequenceDerived l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor)
    (hrect : ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q)
      (_flatP : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (_flatQ : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q),
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        m.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        n.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q))) :
    m = n := by
  apply Iso.ext
  obtain ⟨_, _, _, faithful⟩ := SheafOfModules.cochain_tensor_model_rigidity
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y)
  apply (faithful _ inferInstance _ _).1
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  change m.hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    n.hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  let a := (pullbackTensorSequenceDerived l E f).mapIso
    (pullbackTensorSystemModel l E Y P.obj Q.obj P.property.1 Q.property.1)
  let b := (pullbackTensorCalculus l E X).systemClosed.tensor.mapIso (Iso.prod
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app P.obj)
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app Q.obj))
  apply (cancel_epi a.hom).1
  apply (cancel_mono b.hom).1
  simpa only [a, b, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Category.assoc] using
    hrect P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2

set_option linter.unusedVariables false in
/-- The flat representative rectangle determines the transported comparison by
K-flat tensor descent. The conclusion is an equality of tensor comparison isomorphisms,
which is then used to extend the flat representative equation to all independent
K-flat complexes.
Source: Stacks 06YU and 07A4.
(blueprint: lem-sf-published-system-tensor-identification-representative-descent).

Proof: restriction to pairs of flat-term K-flat representatives is faithful by
cochain tensor model rigidity. For each such pair, the assumed forward rectangle
and the canonical comparison's defining rectangle have the same right-hand side.
Cancel the derived image of the source tensor-model isomorphism on the left,
and tensor applied to the two exact-factorization isomorphisms on the right.
The resulting component equalities prove equality of the restricted hom maps;
faithfulness and isomorphism extensionality give the stated equality.
-/
theorem publishedSystemTransportedTensor_eq_of_flat_normalized {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hflat : ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q)
      (flatP : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (flatQ : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q),
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        (publishedSystemTransportedTensor l E f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
        (pullbackTensorSystemModel l E X _ _
          (pullbackTensorSequenceGood l E f P hP)
          (pullbackTensorSequenceGood l E f Q hQ)).hom) :
    publishedSystemTransportedTensor l E f =
      pullbackTensorSystemComparison l E f := by
  apply tensor_comparison_eq_of_flat_rectangles l E f
  intro P Q hP hQ flatP flatQ
  refine (hflat P Q hP hQ flatP flatQ).trans ?_
  symm
  exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ

/-- On flat K-flat representatives, the transported ambient comparison has the
same inverse representative rectangle as `pullbackTensorSystemComparison`.
Source: Stacks 03D3, 03EL, 07A4 and 07A7, representative normalization of the
pullback tensor comparison. The proof identifies the ordinary pure-tensor map,
its signed total complex map, and the exact-localization model maps on every
summand; the `sequence_inverse_eq` transport removes the ambient presentation.
(blueprint: lem-sf-published-system-tensor-identification-representative).
-/
theorem publishedSystemTransportedTensor_normalized {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) Q) :
    (pullbackTensorSequenceDerived l E f).map
        (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
      (publishedSystemTransportedTensor l E f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
      (pullbackTensorSystemModel l E X _ _
        (pullbackTensorSequenceGood l E f P hP)
        (pullbackTensorSequenceGood l E f Q hQ)).hom := by
  have heq := publishedSystemTransportedTensor_eq_of_flat_normalized l E f
    (fun P Q hP hQ flatP flatQ ↦
      publishedSystemTransportedTensor_normalized_flat l E f P Q hP hQ flatP flatQ)
  rw [heq]
  exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ

/-- The representative normalization determines the transported comparison by the
existing uniqueness theorem. -/
theorem publishedSystemTransportedTensor_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hn : ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q),
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        (publishedSystemTransportedTensor l E f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
        (pullbackTensorSystemModel l E X _ _
          (pullbackTensorSequenceGood l E f P hP)
          (pullbackTensorSequenceGood l E f Q hQ)).hom) :
    publishedSystemTransportedTensor l E f =
      pullbackTensorSystemComparison l E f := by
  exact (pullbackTensorSystemComparison_existsUnique l E f).unique
    hn (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec

end WeilConjectures
