/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerTensorComparison
import WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldLocalTensorModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Constructibility of an integral scalar residue layer

This is the constructibility clause of the residue-layer argument.  It isolates the
finite-residue scalar-extension and local finite-model comparison from the support
clause of the parent theorem.
Source: Stacks, sites-modules, lemma-tensor-product-locally-constant; proetale,
lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layer-constructible).

Proof: the quotient of two consecutive powers of the target uniformizer is the
finite target residue field.  Multiplication by the appropriate power of the
uniformizer identifies the quotient with that residue field; cancellation in the
DVR proves injectivity.  The coefficient map factors through the source residue
field.  Balanced tensor associativity identifies the resulting layer complex with
finite-field scalar extension of the source residue reduction.  Exact finite-field
scalar extension preserves the given finite local models, and restriction to the
finite quotient ring preserves those models.  Derived homology agrees with the
homology of the K-flat representative.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

private theorem firstCoefficient_maximal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  simpa only [Padic.coefficientExtensionIdeal, pow_one, hgen] using hm

private noncomputable def residueRestrictCoextendScalarsAdj
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : AlgebraicGeometry.Scheme.{u}) (f : A →+* B) :
    sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) ⊣
      sheafCompose (ProEt.topology X)
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} f) :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f).whiskerRight X.ProEtᵒᵖ)
    (fullyFaithfulSheafToPresheaf (ProEt.topology X) _)
    (fullyFaithfulSheafToPresheaf (ProEt.topology X) _) (Iso.refl _) (Iso.refl _)

-- The restriction/pullback comparison uses only the coextension adjunction.
-- Importing the upstream projection-formula version would close an import cycle.
private noncomputable def residueRestrictionPullbackIso
    {X Y : AlgebraicGeometry.Scheme.{u}} {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (f : A →+* B) (g : Y ⟶ X) :
    sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) ⋙
        AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g ≅
      AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} B) g ⋙
        sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) :=
  (conjugateIsoEquiv
    ((AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction _ g).comp
      (residueRestrictCoextendScalarsAdj Y f))
    ((residueRestrictCoextendScalarsAdj X f).comp
      (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction _ g))).symm (Iso.refl _)

private theorem finiteLisse_restrict
    {X : AlgebraicGeometry.Scheme.{u}} {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite B] (f : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (hM : AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant B M) :
    AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant A
      ((sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj M) := by
  let : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f).isLeftAdjoint
  obtain ⟨I, W, g, hg, h⟩ := hM
  refine ⟨I, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := h i
  let R := sheafCompose (ProEt.topology (W i)) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)
  have : Finite N := Module.finite_of_finite B
  exact ⟨(ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).obj N,
    @Module.Finite.of_finite _ _ _ _ _ (inferInstanceAs (Finite N)),
    ⟨(residueRestrictionPullbackIso f (g i)).app M ≪≫
      R.mapIso e ≪≫ (constantCommuteCompose (ProEt.topology (W i))
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).app N⟩⟩

private theorem fixedConstructible_restrict
    (X : AlgebraicGeometry.Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite B] (f : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (hM : AlgebraicGeometry.ProEtale.IsConstructible B M) :
    AlgebraicGeometry.ProEtale.IsConstructible A
      ((sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun i ↦ ?_⟩
  exact AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_of_iso
    ((residueRestrictionPullbackIso f (S.immersion i)).app M).symm
    (finiteLisse_restrict f _ (hS i))

private theorem constantScalarUnit_naturality
    (Y : AlgebraicGeometry.Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    proEtaleModuleScalarUnit Y A ≫
        ((adicLisseForget Y).map ((constantSheaf (ProEt.topology Y)
          CommRingCat.{u + 1}).map (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).hom =
      Functor.whiskerRight
        ((Functor.const Y.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))
        (forget₂ CommRingCat RingCat) ≫ proEtaleModuleScalarUnit Y B := by
  ext U b
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).symm U) b

private noncomputable def restrictionEncodingIso
    (Y : AlgebraicGeometry.Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))) ⋙
        proEtaleModuleRestriction Y A ≅
      proEtaleModuleRestriction Y B ⋙ sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} f)) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := ((pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))) ⋙
        proEtaleModuleRestriction Y A).obj M).obj.obj U
    let Q := ((proEtaleModuleRestriction Y B ⋙ sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (RingHom.ulift.{u + 1, u + 1} f))).obj M).obj.obj U
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1} A] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    exact congrArg (fun a ↦ a • (show M.val.obj U from m))
      (ConcreteCategory.congr_hom (congr_app (constantScalarUnit_naturality Y f) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

private noncomputable def residueSheafExtend
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify _ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)

private noncomputable def residueSheafExtendAdjunction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    residueSheafExtend f Y ⊣
      sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)

private theorem residueSheafExtend_exact
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (Y : AlgebraicGeometry.Scheme.{u}) {f : A →+* B} (hf : f.Flat) :
    PreservesFiniteLimits (residueSheafExtend f Y) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1} hf
  have : PreservesFiniteLimits ((Functor.whiskeringRight Y.ProEtᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)) := by
    constructor
    intro J _ _
    infer_instance
  unfold residueSheafExtend Sheaf.composeAndSheafify
  have := comp_preservesFiniteLimits
    ((Functor.whiskeringRight Y.ProEtᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f))
    (presheafToSheaf (ProEt.topology Y) (ModuleCat.{u + 1} B))
  exact comp_preservesFiniteLimits _ _

private noncomputable def finiteFieldConstantRingMap
    (Y : AlgebraicGeometry.Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') : adicLisseConstantRing Y (ULift.{u + 1} k) ⟶
      adicLisseConstantRing Y (ULift.{u + 1} k') :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))

/-- Tensor extension of pro-etale module sheaves along a finite-field map.
Source: Stacks Project, Tag 093V. -/
private noncomputable def finiteFieldScalarExtension
    (Y : AlgebraicGeometry.Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k)) ⥤
      pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k')) :=
  pbcExtend (finiteFieldConstantRingMap Y f)

/-- Scalar extension is additive, hence preserves zero morphisms.
Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant;
finite-field coefficient specialization. -/
private noncomputable instance finiteFieldScalarExtension_additive
    (Y : AlgebraicGeometry.Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    (finiteFieldScalarExtension Y f).Additive :=
  pbcExtend_additive (finiteFieldConstantRingMap Y f)

private noncomputable def scalarExtensionEncodingIso
    (Y : AlgebraicGeometry.Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    finiteFieldScalarExtension Y f ⋙ proEtaleModuleRestriction Y k' ≅
      proEtaleModuleRestriction Y k ⋙
        residueSheafExtend (RingHom.ulift.{u + 1, u + 1} f) Y := by
  let E := proEtaleModuleEncoding Y k
  let E' := proEtaleModuleEncoding Y k'
  let L := residueSheafExtend (RingHom.ulift.{u + 1, u + 1} f) Y
  let R := sheafCompose (ProEt.topology Y)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} f))
  let adj := E.toAdjunction.comp
    ((residueSheafExtendAdjunction (RingHom.ulift f) Y).comp E'.symm.toAdjunction)
  let eR : E'.functor ⋙ R ⋙ E.inverse ≅ pbcRestrict (finiteFieldConstantRingMap Y f) :=
    (isoWhiskerRight (restrictionEncodingIso Y f).symm E.inverse) ≪≫
      isoWhiskerLeft _ E.unitIso.symm
  let adj' := adj.ofNatIsoRight eR
  let e := (pbcScalarAdjunction (finiteFieldConstantRingMap Y f)).leftAdjointUniq adj'
  exact isoWhiskerRight e E'.functor ≪≫
    isoWhiskerLeft (E.functor ⋙ L) E'.counitIso

private theorem scalarExtension_exact
    (Y : AlgebraicGeometry.Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    PreservesFiniteLimits (finiteFieldScalarExtension Y f) ∧
      PreservesFiniteColimits (finiteFieldScalarExtension Y f) := by
  have := proEtaleModuleRestriction_isEquivalence Y k
  have := proEtaleModuleRestriction_isEquivalence Y k'
  have hflat : (RingHom.ulift.{u + 1, u + 1} f).Flat := by
    let := (RingHom.ulift.{u + 1, u + 1} f).toAlgebra
    exact inferInstanceAs (Module.Flat (ULift.{u + 1} k) (ULift.{u + 1} k'))
  have := residueSheafExtend_exact Y hflat
  have : PreservesFiniteLimits
      (finiteFieldScalarExtension Y f ⋙ proEtaleModuleRestriction Y k') :=
    preservesFiniteLimits_of_natIso (scalarExtensionEncodingIso Y f).symm
  have : (finiteFieldScalarExtension Y f).IsLeftAdjoint :=
    (pbcScalarAdjunction (finiteFieldConstantRingMap Y f)).isLeftAdjoint
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves
    (finiteFieldScalarExtension Y f) (proEtaleModuleRestriction Y k'), inferInstance⟩

private theorem finite_tensor_model
    {k k' : Type u} [Field k] [Field k'] [Finite k'] (f : k →+* k')
    (M : ModuleCat.{u + 1} (ULift.{u + 1} k)) [Finite M] :
    Finite ((ModuleCat.extendScalars (RingHom.ulift.{u + 1, u + 1} f)).obj M) := by
  let := (RingHom.ulift.{u + 1, u + 1} f).toAlgebra
  have : Module.Finite (ULift.{u + 1} k) M := Module.Finite.of_finite
  change Finite ((ULift.{u + 1} k') ⊗[ULift.{u + 1} k] M)
  have : Module.Finite (ULift.{u + 1} k')
      ((ULift.{u + 1} k') ⊗[ULift.{u + 1} k] M) := inferInstance
  exact Module.finite_of_finite (ULift.{u + 1} k')

private theorem finiteFieldSheafScalarExtension
    (Y : AlgebraicGeometry.Scheme.{u}) {k k' : Type u}
    [Field k] [Field k'] [Finite k] [Finite k'] (f : k →+* k') :
    PreservesFiniteLimits (finiteFieldScalarExtension Y f) ∧
      PreservesFiniteColimits (finiteFieldScalarExtension Y f) ∧
      ∀ F, IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} k) F →
        IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} k')
          ((finiteFieldScalarExtension Y f).obj F) := by
  obtain ⟨hlim, hcolim⟩ := scalarExtension_exact Y f
  refine ⟨hlim, hcolim, fun F hF ↦ ?_⟩
  obtain ⟨S, hn, hS, hF⟩ := hF
  refine ⟨S, hn, hS, fun i ↦ ?_⟩
  obtain ⟨K, hK, hF⟩ := hF i
  refine ⟨K, hK, fun V g hg ↦ ?_⟩
  obtain ⟨M, hM, eM⟩ := hF V g hg
  have : Finite M := hM
  exact ⟨(ModuleCat.extendScalars (RingHom.ulift.{u + 1, u + 1} f)).obj M,
    finite_tensor_model f M,
    finiteFieldScalarExtension_localModel Y f _ (S.immersion i) F V M eM⟩

private theorem coefficientConstructible_restrict
    (Y : AlgebraicGeometry.Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (f : A →+* B)
    (M : pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} B)))
    (hM : IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} B) M) :
    IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} A)
      ((pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).obj M) := by
  apply (CoefficientSerre.coefficient_constructible_iff Y (ULift.{u + 1} A) _).mpr
  apply AlgebraicGeometry.ProEtale.isConstructible_of_iso
    ((restrictionEncodingIso Y f).app M).symm
  exact fixedConstructible_restrict Y (RingHom.ulift.{u + 1, u + 1} f) _
    ((CoefficientSerre.coefficient_constructible_iff Y (ULift.{u + 1} B) M).mp hM)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The finite-model constructibility part of the residue-layer estimate.
Source: Stacks, sites-modules, lemma-tensor-product-locally-constant; proetale,
lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layer-constructible). -/
theorem integralScalarResidueLayer_constructible
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (r s : ℤ) (hrs : r ≤ s)
    (h₁ : intrinsicFiniteTorsionConstructible l E 1 (by omega) Y
      ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)))
    (hbound : ∀ i : ℤ,
      i ∈ proEtaleCohomologicalSupport
        ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)) →
      r ≤ i ∧ i ≤ s) (n : ℕ)
    (F : Fin (n + 1 + 1) → Submodule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))
    (hF : F = fun (j : Fin (n + 1 + 1)) ↦ (Ideal.span ({ULift.up ((Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l L (n + 1)))
        (Padic.coefficientExtensionUniformizer l L))} :
          Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^ ((j : ℕ))) :
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    ∀ (j : Fin (n + 1)) (i : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B
          (completedIntegralCommRingSheafUnrestricted l E Y)
          (integralScalarRho l E L ι Y n) P.obj
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology i) := by
  have _interval := hrs
  have _support := hbound
  subst F
  let := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let := Padic.finite_coefficientExtensionRing l L 1 (by omega)
  let := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
  let := firstCoefficient_maximal l E
  let := firstCoefficient_maximal l L
  let : Field (Padic.coefficientExtensionRing l E 1) := Ideal.Quotient.field _
  let : Field (Padic.coefficientExtensionRing l L 1) := Ideal.Quotient.field _
  let := scalarReductionExtensionAdditive l E Y 0
  let C := ((scalarReductionExtension l E Y 0).mapHomologicalComplex (.up ℤ)).obj P.obj
  let f := integralScalarQuotientMap l E L ι 0
  let T := finiteFieldScalarExtension Y f
  have hT := finiteFieldSheafScalarExtension Y f
  let : PreservesFiniteLimits T := hT.1
  let : PreservesFiniteColimits T := hT.2.1
  let q : Padic.coefficientExtensionRing l L (n + 1) →+*
      Padic.coefficientExtensionRing l L 1 :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))
  let R := pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} q)))
  let TC := (T.mapHomologicalComplex (.up ℤ)).obj C
  let RTC := (R.mapHomologicalComplex (.up ℤ)).obj TC
  let eC : (integralDerivedReduction l E Y D hl 0).obj
      (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C :=
    integralDerivedReductionKFlatIso l E Y D hl 0 P.obj P.property.1
  have hC (i : ℤ) : IsConstructibleProEtaleCoefficientModuleSheaf Y
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) (C.homology i) := by
    let e := (DerivedCategory.homologyFunctor _ i).mapIso eC ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app C
    have h := (proEtaleModuleRestriction_constructible_iff Y
      (Padic.coefficientExtensionRing l E 1) _).mp (h₁.2 i)
    have h' := (CoefficientSerre.coefficient_constructible_iff Y
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) _).mpr h
    exact AlgebraicGeometry.Scheme.coefficientConstructible_of_iso Y _ e h'
  dsimp only
  intro j i
  have ht : IsConstructibleProEtaleCoefficientModuleSheaf Y
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L 1)) (TC.homology i) := by
    exact AlgebraicGeometry.Scheme.coefficientConstructible_of_iso Y _
      ((C.sc i).mapHomologyIso T).symm
      (hT.2.2 _ (hC i))
  have hr : IsConstructibleProEtaleCoefficientModuleSheaf Y
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) (RTC.homology i) := by
    exact AlgebraicGeometry.Scheme.coefficientConstructible_of_iso Y _
      ((TC.sc i).mapHomologyIso R).symm
      (coefficientConstructible_restrict Y q _ ht)
  obtain ⟨e⟩ := integralScalarResidueLayerTensorComparison l E L ι Y P.obj n j
  let he := ((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _
  exact AlgebraicGeometry.Scheme.coefficientConstructible_of_iso Y _ he.symm hr

end WeilConjectures
