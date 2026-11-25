/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityDerivedFactors
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Localization.Prod
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! # Tensor normalization of the reindexing identity

Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI.
(blueprint: lem-pod-reindexing-tensor-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 1000001] cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local implicit_reducible] siteId
attribute [local irreducible] podReindexingHomModel
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientTotalTensor coefficientTensorGenerator SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  CoefficientClosedStructure.tensor

private theorem identity_coefficient (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) :
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (podReindexingCoefficient l E (𝟙 X) s).hom =
      (Functor.sheafPushforwardContinuousId' (siteId X) RingCat.{u + 1}
        (ProEt.topology X)).hom.app
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (podReindexingRing l E X s)) := by
  have hf (n : ℕ) :
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (podReindexingCoefficient l E (𝟙 X) (some n)).hom =
        (Functor.sheafPushforwardContinuousId' (siteId X) RingCat.{u + 1}
          (ProEt.topology X)).hom.app
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (podReindexingRing l E X (some n))) := by
    change (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((podReindexingCoefficient_existsUnique l E (𝟙 X)).exists.choose (some n)).hom = _
    rw [(podReindexingCoefficient_existsUnique l E (𝟙 X)).exists.choose_spec.1 n]
    apply (isoSectionwiseConstantMap_existsUnique.{u, u} (𝟙 X)
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).unique
      (isoSectionwiseConstantMap_existsUnique.{u, u} (𝟙 X) _).exists.choose_spec
    intro U a
    exact congrArg (fun f ↦ f a)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))))).naturality
            ((siteId X).inv.app U).op).symm
  cases s with
  | some n => exact hf n
  | none =>
    apply limit.hom_ext
    intro n
    have hp := congrArg
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((podReindexingCoefficient_existsUnique l E (𝟙 X)).exists.choose_spec.2 n.unop)
    simp only [Functor.map_comp] at hp
    change _ ≫ _ = _ ≫ _ at hp
    erw [hp]
    rw [show (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((podReindexingCoefficient_existsUnique l E (𝟙 X)).exists.choose (some n.unop)).hom = _
        from hf n.unop]
    exact (Functor.sheafPushforwardContinuousId' (siteId X) RingCat.{u + 1}
      (ProEt.topology X)).hom.naturality
        (limit.π (integralCoefficientSheafSystem l E X) n)

private theorem identity_exact (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) :
    (podReindexingFunctor l E (𝟙 X) s).Additive ∧
      PreservesFiniteLimits (podReindexingFunctor l E (𝟙 X) s) ∧
      PreservesFiniteColimits (podReindexingFunctor l E (𝟙 X) s) := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (podReindexingRing l E X s)
  let c : (isoSectionwiseInverseImage (𝟙 X) RingCat.{u + 1}).obj R ≅ R :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E (𝟙 X) s)
  exact isoSectionwiseModuleInverseImage_exact (𝟙 X) (RY := R) (RX := R) c.hom

private instance identity_additive (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) :
    (podReindexingFunctor l E (𝟙 X) s).Additive := (identity_exact l E X s).1

private instance identity_limits (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) :
    PreservesFiniteLimits (podReindexingFunctor l E (𝟙 X) s) := (identity_exact l E X s).2.1

private instance identity_colimits (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) :
    PreservesFiniteColimits (podReindexingFunctor l E (𝟙 X) s) := (identity_exact l E X s).2.2

private def identity_ordinary (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) :
    podReindexingFunctor l E (𝟙 X) s ≅ 𝟭 (podReindexingModules l E X s) := by
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let R := W.obj (podReindexingRing l E X s)
  let c : (isoSectionwiseInverseImage (𝟙 X) RingCat.{u + 1}).obj R ≅ R :=
    W.mapIso (podReindexingCoefficient l E (𝟙 X) s)
  let a := SheafOfModules.pushforwardNatIso
    (J := ProEt.topology X) (K := ProEt.topology X)
    (F := 𝟭 X.ProEt) (G := proEtaleIsoPostcompose (𝟙 X))
    (S := R) (T := R) c.inv (siteId X).symm
  letI : IsIso (W.mapIso (podReindexingCoefficient l E (𝟙 X) s)).hom :=
    (W.mapIso (podReindexingCoefficient l E (𝟙 X) s)).isIso_hom
  letI : IsIso c.hom := c.isIso_hom
  let b : podReindexingFunctor l E (𝟙 X) s ≅ SheafOfModules.pushforward c.inv := by
    refine SheafOfModules.pushforwardCongr ?_
    change inv c.hom = c.inv
    exact IsIso.inv_eq_of_hom_inv_id c.hom_inv_id
  refine b ≪≫ a ≪≫ SheafOfModules.pushforwardCongr ?_ ≪≫
    SheafOfModules.pushforwardId _
  change c.inv ≫ _ = 𝟙 _
  erw [← identity_coefficient l E X s]
  exact c.inv_hom_id

private theorem identity_ordinary_sections (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (M : podReindexingModules l E X s) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 X)).obj U))) :
    HEq (((identity_ordinary l E X s).hom.app M).val.app (op U) x)
      (M.val.map ((siteId X).inv.app U).op x) := by
  simp only [identity_ordinary, SheafOfModules.pushforwardId]
  rfl

private def identity_data (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) : Identity l E X s := by
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let a := identity_ordinary l E X s
  let ac := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  refine
    { ordinary := a
      sections := identity_ordinary_sections l E X s
      complex := fun P ↦ ac.app P
      degree := ?_
      derived := Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso _
      model := fun P ↦ podIdentityDerivedFactors _ a P }
  intro P i
  simp only [ac, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  exact Category.comp_id _

private theorem identity_generator_restrict (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) (P Q : K l E X s)
    (p q n : ℤ) (h : p + q = n) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((total l E X s).obj (P, Q)).X n).val.map f
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) P Q p q n h U x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) P Q p q n h V
          ((P.X p).val.map f x) ((Q.X q).val.map f y) := by
  let R := podReindexingRing l E X s
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  unfold coefficientTensorGenerator total coefficientTotalTensor
  erw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
  rfl

private theorem identity_complex_sections (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ) (k : Identity l E X s)
    (P : K l E X s) (n : ℤ) (U : X.ProEt)
    (x : (P.X n).val.obj (op ((proEtaleIsoPostcompose (𝟙 X)).obj U))) :
    ((k.complex P).hom.f n).val.app (op U) x =
      (P.X n).val.map ((siteId X).inv.app U).op x := by
  rw [k.degree]
  exact eq_of_heq (k.sections (P.X n) U x)

-- Check a map out of a tensor presentation using chosen preimages of its generators.
private theorem identity_tensor_iso_hom_ext (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (A P Q H : K l E X s) (e : A ≅ (total l E X s).obj (P, Q))
    (f : (total l E X s).obj (P, Q) ⟶ H) (g : A ⟶ H)
    (hh : ∀ (n p q : ℤ) (hpq : p + q = n) (U : X.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ∃ z : (A.X n).val.obj U,
        (e.hom.f n).val.app U z =
          coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (podReindexingRing l E X s) P Q p q n hpq U x y ∧
        (f.f n).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (podReindexingRing l E X s) P Q p q n hpq U x y) =
          (g.f n).val.app U z) :
    e.hom ≫ f = g := by
  apply (cancel_epi e.inv).mp
  rw [Iso.inv_hom_id_assoc]
  ext n : 1
  apply ScalarHomTensor.total_pure_hom_ext (J := ProEt.topology X)
    (R := podReindexingRing l E X s)
  intro p q hpq U x y
  obtain ⟨z, hz, hf⟩ := hh n p q hpq U x y
  have hi := congrArg (fun a ↦ (a.f n).val.app U z) e.hom_inv_id
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  rw [hf, ← hz]
  exact congrArg (fun z ↦ (g.f n).val.app U z) hi.symm

-- Evaluate the two routes directly on the preimages of pure generators.
private theorem identity_tensor_chain (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (S : Closed l E X s) (T : Models l E X s S)
    (c : Comparison l E (𝟙 X) s S S T T) (k : Identity l E X s)
    (P Q : K l E X s) :
    (c.tensorChain P Q).hom ≫
        (total l E X s).map ((k.complex P).hom, (k.complex Q).hom) =
      (k.complex ((total l E X s).obj (P, Q))).hom := by
  apply identity_tensor_iso_hom_ext l E X s _ _ _ _ (c.tensorChain P Q)
  intro n p q hpq U x y
  refine ⟨coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
    (podReindexingRing l E X s) P Q p q n hpq
      (op ((proEtaleIsoPostcompose (𝟙 X)).obj U.unop)) x y,
    c.tensorChain_pure P Q p q n hpq U.unop x y, ?_⟩
  refine (ScalarHomTensor.tensor_generator_map (k.complex P).hom
    (k.complex Q).hom p q n hpq U x y).trans ?_
  refine (congrArg₂ (fun a b ↦ coefficientTensorGenerator.{u, u + 1, u}
    (ProEt.topology X) (podReindexingRing l E X s) P Q p q n hpq U a b)
      (identity_complex_sections l E X s k P p U.unop x)
      (identity_complex_sections l E X s k Q q U.unop y)).trans ?_
  exact (identity_generator_restrict l E X s P Q p q n hpq
    ((siteId X).inv.app U.unop).op x y).symm.trans
      (identity_complex_sections l E X s k ((total l E X s).obj (P, Q)) n U.unop _).symm

private theorem identity_representative_square
    {C : Type*} [Category C] (F : C ⥤ C) (B : C × C ⥤ C)
    (a : F ≅ 𝟭 C) (δ : B ⋙ F ⟶ (F.prod F) ⋙ B)
    {p q t fp fq ft : C} (r : t ≅ B.obj (p, q))
    (αp : F.obj p ⟶ fp) (αq : F.obj q ⟶ fq) (αt : F.obj t ⟶ ft)
    (ap : fp ⟶ p) (aq : fq ⟶ q) (at' : ft ⟶ t) (d : ft ⟶ B.obj (fp, fq))
    (hp : a.hom.app p = αp ≫ ap) (hq : a.hom.app q = αq ≫ aq)
    (ht : a.hom.app t = αt ≫ at')
    (hδ : F.map r.hom ≫ δ.app (p, q) ≫ B.map (Prod.mkHom αp αq) = αt ≫ d)
    (hd : d ≫ B.map (Prod.mkHom ap aq) = at' ≫ r.hom) :
    δ.app (p, q) ≫ B.map (Prod.mkHom (a.hom.app p) (a.hom.app q)) =
      a.hom.app (B.obj (p, q)) := by
  apply (cancel_epi (F.map r.hom)).mp
  rw [a.hom.naturality, ht, hp, hq]
  have hpair : Prod.mkHom (αp ≫ ap) (αq ≫ aq) =
      Prod.mkHom αp αq ≫ Prod.mkHom ap aq := rfl
  rw [hpair, B.map_comp]
  calc
    _ = (F.map r.hom ≫ δ.app (p, q) ≫ B.map (Prod.mkHom αp αq)) ≫ B.map (Prod.mkHom ap aq) := by
      simp only [Category.assoc]
    _ = _ := by rw [hδ, Category.assoc, hd, Category.assoc]; rfl

-- State the localized naturality square explicitly before composing it with the chain square.
private theorem identity_tensor_representative (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (S : Closed l E X s) (T : Models l E X s S)
    (c : Comparison l E (𝟙 X) s S S T T) (k : Identity l E X s)
    (P Q : K l E X s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) Q) :
    c.tensor.hom.app ((podReindexingQ l E X s).obj P, (podReindexingQ l E X s).obj Q) ≫
      S.tensor.map (Prod.mkHom
        (k.derived.hom.app ((podReindexingQ l E X s).obj P))
        (k.derived.hom.app ((podReindexingQ l E X s).obj Q))) =
      k.derived.hom.app (S.tensor.obj
        ((podReindexingQ l E X s).obj P, (podReindexingQ l E X s).obj Q)) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let α := podReindexingDerivedFactors l E (𝟙 X) s
  let Q₀ := podReindexingQ l E X s
  let B := total l E X s
  obtain ⟨hFP, hFQ, hm⟩ := c.tensor_model P Q hP hQ
  let r := T.comparison.app (⟨P, hP⟩, ⟨Q, hQ⟩)
  have hn : Q₀.map (B.map (Prod.mkHom (k.complex P).hom (k.complex Q).hom)) ≫ r.hom =
      T.comparison.hom.app (⟨_, hFP⟩, ⟨_, hFQ⟩) ≫
        S.tensor.map (Prod.mkHom (Q₀.map (k.complex P).hom) (Q₀.map (k.complex Q).hom)) :=
    T.comparison.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (k.complex P).hom :
      (⟨_, hFP⟩ : ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology X) (R := podReindexingRing l E X s))) ⟶ ⟨P, hP⟩)
      (ObjectProperty.homMk (k.complex Q).hom :
        (⟨_, hFQ⟩ : ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            (J := ProEt.topology X) (R := podReindexingRing l E X s))) ⟶ ⟨Q, hQ⟩))
  have hc := identity_tensor_chain l E X s S T c k P Q
  have hd : (Q₀.map (c.tensorChain P Q).hom ≫
      T.comparison.hom.app (⟨_, hFP⟩, ⟨_, hFQ⟩)) ≫
      S.tensor.map (Prod.mkHom (Q₀.map (k.complex P).hom) (Q₀.map (k.complex Q).hom)) =
      Q₀.map (k.complex (B.obj (P, Q))).hom ≫ r.hom := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ Q₀.map (c.tensorChain P Q).hom ≫ f) hn.symm).trans
        ((Q₀.map_comp_assoc _ _ _).symm.trans
          (congrArg (fun f ↦ Q₀.map f ≫ r.hom) hc)))
  exact identity_representative_square (podReindexingDerivedFunctor l E (𝟙 X) s)
    S.tensor k.derived c.tensor.hom r (α.hom.app P) (α.hom.app Q)
    (α.hom.app (B.obj (P, Q))) (Q₀.map (k.complex P).hom)
    (Q₀.map (k.complex Q).hom) (Q₀.map (k.complex (B.obj (P, Q))).hom)
    (Q₀.map (c.tensorChain P Q).hom ≫ T.comparison.hom.app (⟨_, hFP⟩, ⟨_, hFQ⟩))
    (k.model P) (k.model Q) (k.model (B.obj (P, Q))) hm hd

/-- The canonical site and localized tensor identity comparison.
Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI
(blueprint: lem-pod-reindexing-tensor-identity).

Proof: For a module M and an object U of the pro-etale site, use M.val.map ((siteId X).inv.app
U).op as the ordinary comparison. Its inverse is restriction along siteId.hom. Functoriality of M
and the site isomorphism identities prove the two inverse laws, while naturality of siteId proves
compatibility with restriction. The coefficient action is unchanged on finite-stage constants;
equality after every finite quotient proves the same assertion for completed coefficients. Hence
the section maps are linear and define the required natural ordinary module isomorphism, with
precisely the sections field of Identity.

On a cochain complex take these ordinary maps in every degree. Their naturality with respect to
the differentials gives a chain isomorphism; its degree field is the defining formula. The chain
isomorphisms are natural in P. Descend them through localization, since reindexing preserves
quasi-isomorphisms. Full faithfulness of whiskering with the localization determines the resulting
derived isomorphism, and its defining representative equation is exactly Identity.model with the
recorded podReindexingDerivedFactors. Thus every field is constructed by restriction or
localization.

For the tensor equation first use c.tensorChain_pure on the actual total tensor of complexes P,Q.
On a pure section x tensor y in the (p,q) summand, restriction along siteId.inv gives the tensor
of the two restricted sections. These are exactly the two routes in the proposed chain square. No
degree is permuted, so no sign occurs. Sheafification and total-summand extensionality give
equality of chain maps. Choose P,Q independently K-flat. Their reindexings are K-flat, since the
inverse exact reindexing equivalence transports the defining acyclic tensor tests. Substitute
c.tensor_model and the identity model equation into the localized chain square, and cancel the
K-flat comparison isomorphisms. This gives the desired square on their localized objects.
Independent K-flat resolutions and naturality of c.tensor and the identity comparison then give
the equation for arbitrary M,N. This argument proves only the tensor equation; the item derives
the Hom equation from evaluation.
-/
theorem tensor_identity_exists (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (S : Closed l E X s) (T : Models l E X s S)
    (c : Comparison l E (𝟙 X) s S S T T) :
    ∃ k : Identity l E X s,
      (∀ M N : podReindexingDerived l E X s,
        c.tensor.hom.app (M, N) ≫ S.tensor.map
          (Prod.mkHom (k.derived.hom.app M) (k.derived.hom.app N)) =
        k.derived.hom.app (S.tensor.obj (M, N))) := by
  let k := identity_data l E X s
  let F := podReindexingDerivedFunctor l E (𝟙 X) s
  let lhs : S.tensor ⋙ F ⟶ S.tensor := c.tensor.hom ≫
    Functor.whiskerRight (NatTrans.prod k.derived.hom k.derived.hom) S.tensor
  let rhs : S.tensor ⋙ F ⟶ S.tensor := Functor.whiskerLeft S.tensor k.derived.hom
  let K₀ := coefficientKFlatInclusion.{u, u + 1, u}
    (ProEt.topology X) (podReindexingRing l E X s)
  let L := K₀ ⋙ podReindexingQ l E X s
  let W := (HomologicalComplex.quasiIso (podReindexingModules l E X s)
    (.up ℤ)).inverseImage K₀
  have : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2}
    (ProEt.topology X) (podReindexingRing l E X s)
  have h : lhs = rhs := by
    apply Localization.natTrans_ext (L.prod L) (W.prod W)
    intro PQ
    exact identity_tensor_representative l E X s S T c k
      PQ.1.obj PQ.2.obj PQ.1.property PQ.2.property
  exact ⟨k, fun M N ↦ congrArg (fun a ↦ a.app (M, N)) h⟩

end WeilConjectures.PodReindexingCoherence
