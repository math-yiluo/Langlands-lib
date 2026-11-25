/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteScalarCoherence
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteConstructibilityComparison
import WeilConjectures.FourierTransform.FdIntegralIdentityRationalEquivalence
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleRationalHomComparison
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiltrationModels
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic

/-! # Finite condensed realizations of the raw rational stages

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Lemma 6.8.2.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u w a b v v'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization

private theorem rawCategoryHEq
    (l : ℕ) [Fact l.Prime] {A B : Type u}
    [fa : Field A] [fb : Field B]
    [aa : Algebra ℚ_[l] A] [ab : Algebra ℚ_[l] B]
    [na : FiniteDimensional ℚ_[l] A] [nb : FiniteDimensional ℚ_[l] B]
    (T : Scheme.{u}) (h : A = B) (hf : HEq fa fb) (ha : HEq aa ab) :
    HEq (inferInstance : Category (sfRationalConstructibleCategory l A T))
      (inferInstance : Category (sfRationalConstructibleCategory l B T)) := by
  cases h
  cases hf
  cases ha
  rfl

private theorem finiteCategoryHEq
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
      (inferInstance : Category
        (sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  exact rawCategoryHEq
    (na := AlgebraicallyClosedCoefficients.coefficientFinite.{u} l Ω E) l T (by rfl) (by
    unfold pbcFiniteFieldField
    rfl) (by
    unfold pbcFiniteFieldAlgebra
    rfl)

private theorem equivalenceOfHEq
    {A B : Type a} {D : Type b} [ca : Category.{v} A] [cb : Category.{v} B]
    [Category.{v'} D]
    (hAB : A = B) (hab : HEq ca cb) (F : A ⥤ D) (e : B ≌ D)
    (h : HEq F e.functor) : F.IsEquivalence := by
  subst B
  have hab' : ca = cb := eq_of_heq hab
  subst cb
  have h' : F = e.functor := eq_of_heq h
  subst F
  infer_instance

private theorem realization_image (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (s : RationalModuleRealization l E T)
    (K : DerivedCategory (pbcModules T (rationalCoefficientSheaf l T E))) :
    finiteFreeTarget T (rationalCoefficientSheaf l T E) K ↔
      ∃ M, Nonempty (s.J.obj M ≅ K) := by
  have hf := ((constructibleRationalHomComparison l E T).2 s).2.1
  have hi := ((constructibleRationalHomComparison l E T).2 s).2.2
  let X : ContinuousRational.Base l :=
    { scheme := T, dimension := Fact.out, prime_unit := Fact.out }
  constructor
  · rintro ⟨⟨a, b, _, ha, hb⟩, hc⟩
    have := ha
    have := hb
    obtain ⟨_, M, _, ⟨e⟩, _⟩ := RationalConeModels.bounded_model l E T s hf hi
      (fun F hF ↦ ContinuousRational.rationalContinuousFiltrationModels l E X s F hF)
      K a b (fun r hr ↦ hr.elim
        (fun h ↦ DerivedCategory.isZero_of_isGE K a r h)
        (fun h ↦ DerivedCategory.isZero_of_isLE K b r h)) hc
    exact ⟨(pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj M, ⟨e⟩⟩
  · rintro ⟨⟨M⟩, ⟨e⟩⟩
    obtain ⟨⟨a, b, ha, hb⟩, hc⟩ := s.constructible M
    let q : (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).obj M.obj ≅ K :=
      (eqToIso (s.objects M)).symm ≪≫ e
    have := ha
    have := hb
    have hge := DerivedCategory.TStructure.t.isGE_of_iso q a
    have hle := DerivedCategory.TStructure.t.isLE_of_iso q b
    refine ⟨⟨min a b, b, min_le_right _ _, ?_, hle⟩, fun r ↦ ?_⟩
    · exact DerivedCategory.TStructure.t.isGE_of_ge K (min a b) a (min_le_left _ _)
    · obtain ⟨t, ht⟩ := hc r
      refine ⟨t, fun j ↦ ?_⟩
      have := ht j
      exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1}
        ((proEtaleModuleInverseImage (t.immersion j)
          (rationalCoefficientSheaf l T E)).mapIso
            ((DerivedCategory.homologyFunctor _ r).mapIso q))

private theorem finiteCore_exists (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))] : Nonempty (Core l T) := by
  classical
  let stage (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    (fdIntegralIdentityRationalEquivalence D l hl (PadicAlgCl l) T E).choose
  obtain ⟨raw⟩ := fdCompletionInverseScalarCoherence D l hl (PadicAlgCl l) T stage
  let realization (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
    Classical.choice (rationalModuleRealizationFunctor l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T)
  refine ⟨⟨stage, raw, realization, ?_, ?_⟩⟩
  · intro E K L
    have hf := ((constructibleRationalHomComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T).2 (realization E)).2.1
    have hi := ((constructibleRationalHomComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E) T).2 (realization E)).2.2
    exact (Functor.FullyFaithful.ofFullyFaithful (realization E).J).map_bijective K L
  · intro E K
    exact realization_image l (pbcFiniteField.{u} l (PadicAlgCl l) E) T (realization E) K

/-- Only the finite clauses of the continuous realization data are required.
No closure essential-image, tower or identity coherence is included.
Source: BS 6.8.2 and 6.8.14(2).
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
structure FiniteCondensedData (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))] extends Core l T where
  scalar : ScalarData l T toCore
  closure : ClosureData l T toCore scalar
  finite_sections : ∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj T l E) K ↔
      finiteFreeTarget T (rationalCoefficientSheaf l T
        (pbcFiniteField.{u} l (PadicAlgCl l) E))
        ((pbcDerivedExtend (closure.finiteIso E).hom).obj
          ((sectionDerived T (ProEtale.padicSubfieldRingObj T l E)).obj K))

/-- The finite realization data require no structure map to an auxiliary finite field.
The auxiliary datum is used only as a proof parameter in the integral identity theorem.
Source: BS 6.8.14(2)
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
theorem finiteData_exists (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))] : Nonempty (FiniteCondensedData l T) := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  letI : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{u} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ULift.{u} (ZMod p)
      card_base := by simp [Nat.card_eq_fintype_card, ZMod.card]
      k := AlgebraicClosure (ULift.{u} (ZMod p)) }
  obtain ⟨C⟩ := finiteCore_exists D l (Nat.ne_of_lt hp) T
  obtain ⟨B, _⟩ := adic_finite_scalar_coherence l T C
  obtain ⟨R, _, _, hFS, _⟩ := adic_finite_constructibility_comparison l T C B
  exact ⟨{ toCore := C, scalar := B, closure := R, finite_sections := hFS }⟩

variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

/-- Extension along the specified coefficient isomorphism is an equivalence.
Source: scalar extension/restriction adjunction, BS 6.8.2.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
theorem derivedExtendIso_isEquivalence
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S) :
    (pbcDerivedExtend e.hom).IsEquivalence := by
  letI := derivedRestrictIso_isEquivalence e
  exact (pbcDerivedScalarAdjunction e.hom).isEquivalence_left_of_isEquivalence_right

/-- The exact equivalence from internal finite coefficient modules to continuous modules.
It is section reconstruction followed by extension along the specified coefficient iso.
Source: BS 6.8.2 and the internal/section equivalence.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
@[irreducible] def finiteCondensedEncoding (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (ProEtale.padicSubfieldRingObj T l E)) ≌
      DerivedCategory (pbcModules T (rationalCoefficientSheaf l T
        (pbcFiniteField.{u} l (PadicAlgCl l) E))) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (ProEtale.padicSubfieldRingObj T l E)
  letI := Functor.additive_of_preserves_binary_products e.functor
  letI := Functor.additive_of_preserves_binary_products e.inverse
  letI := derivedExtendIso_isEquivalence T (A.closure.finiteIso E)
  e.mapDerivedCategory.trans
    (pbcDerivedExtend (A.closure.finiteIso E).hom).asEquivalence

/-- The forward encoding has the literal section-reconstruction tensor formula.
Source: the definition of the section encoding, BS 6.8.2.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
theorem finiteCondensedEncoding_functor (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    (finiteCondensedEncoding l T A E).functor =
      sectionDerived T (ProEtale.padicSubfieldRingObj T l E) ⋙
        pbcDerivedExtend (A.closure.finiteIso E).hom := by
  unfold finiteCondensedEncoding sectionDerived
  rfl

/-- The raw comparison is the specified rational equivalence, with its category
presentation transported explicitly.
Source: integral identity, BS 6.8.14(2).
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
theorem finiteRawFunctor_isEquivalence (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    (A.raw.family.Φ E).IsEquivalence := by
  have hf := A.raw.finite_functor
  unfold FdCompletionFiniteFunctor at hf
  apply equivalenceOfHEq (F := A.raw.family.Φ E) (e := (A.stage E).rational)
    (by
      dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
        AlgebraicallyClosedCoefficients.Coefficient, pbcFiniteField]
      rfl)
    (finiteCategoryHEq l (PadicAlgCl l) T E)
  exact hf E

/-- The finite continuous realization is full and faithful.
Source: the integral identity and constructible rational Hom comparison, BS 6.8.14(2).
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
def finiteFunctor_fullyFaithful (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    (A.raw.family.Φ E ⋙ (A.realization E).J).FullyFaithful := by
  haveI := finiteRawFunctor_isEquivalence l T A E
  haveI : (A.realization E).J.Full := ⟨fun f ↦ (A.fully_faithful E _ _).2 f⟩
  haveI : (A.realization E).J.Faithful := ⟨fun h ↦ (A.fully_faithful E _ _).1 h⟩
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- Finite realization lands in the actual bounded constructible condensed subcategory.
Source: BS 6.8.8, 6.8.14(2); transport through the specified section encoding.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
theorem finiteCondensed_constructible (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E) :
    ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj T l E)
      ((finiteCondensedEncoding l T A E).inverse.obj
        ((finiteFunctor l T A.toCore E).obj K)) := by
  apply (A.finite_sections E _).mpr
  apply (A.image E _).mpr
  refine ⟨(A.raw.family.Φ E).obj K, ⟨?_⟩⟩
  simpa only [finiteCondensedEncoding_functor, Functor.comp_obj,
    Functor.id_obj, finiteFunctor] using
    ((finiteCondensedEncoding l T A E).counitIso.app
      ((finiteFunctor l T A.toCore E).obj K)).symm

/-- The finite functor, with its constructibility witness and no new choice of objects.
Source: BS 6.8.14(2).
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
def finiteCondensedFunctor (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
      ProEtale.PadicSubfieldConstructible T l E :=
  (ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj T l E)).lift
    (finiteFunctor l T A.toCore E ⋙ (finiteCondensedEncoding l T A E).inverse)
    (finiteCondensed_constructible l T A E)

instance finiteCondensedFunctor_full (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    (finiteCondensedFunctor l T A E).Full := by
  letI : (finiteFunctor l T A.toCore E).Full :=
    (finiteFunctor_fullyFaithful l T A E).full
  unfold finiteCondensedFunctor
  infer_instance

instance finiteCondensedFunctor_faithful (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    (finiteCondensedFunctor l T A E).Faithful := by
  letI : (finiteFunctor l T A.toCore E).Faithful :=
    (finiteFunctor_fullyFaithful l T A E).faithful
  unfold finiteCondensedFunctor
  infer_instance

/-- The specified finite functor recovers the original continuous realization.
Source: BS 6.8.2, the counit of the exact section encoding.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
def finiteCondensedComparison (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    finiteCondensedFunctor l T A E ⋙
        (ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj T l E)).ι ⋙
          (finiteCondensedEncoding l T A E).functor ≅ finiteFunctor l T A.toCore E :=
  Functor.isoWhiskerLeft (finiteFunctor l T A.toCore E)
    (finiteCondensedEncoding l T A E).counitIso

/-- Section reconstruction intertwines the specified derived finite scalar adjunctions.
The unit equation in `scalarAdjunctionCoefficientEquivalence` determines this iso uniquely;
thus this choice has no unspecified scalar automorphism.
Source: Stacks 03EK and BS 6.8.2.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
@[irreducible] def finiteSectionScalarComparison
    {E L : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ L) :
    ProEtale.derivedExtendScalarsSubfield T l h ⋙
        sectionDerived T (ProEtale.padicSubfieldRingObj T l L) ≅
      sectionDerived T (ProEtale.padicSubfieldRingObj T l E) ⋙
        pbcDerivedExtend (ProEtale.CondensedRing.sectionRingMap T
          (ProEtale.padicSubfieldRingObjMap T l h)) := by
  unfold sectionDerived
  letI hcommE : IsCommMonObj (ProEtale.padicSubfieldRingObj T l E) :=
    ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) T
  letI hcommL : IsCommMonObj (ProEtale.padicSubfieldRingObj T l L) :=
    ProEtale.isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj L) T
  let φ := ProEtale.padicSubfieldRingObjMap T l h
  let eE := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (ProEtale.padicSubfieldRingObj T l E)
  let eL := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (ProEtale.padicSubfieldRingObj T l L)
  letI := Functor.additive_of_preserves_binary_products eE.functor
  letI := Functor.additive_of_preserves_binary_products eL.functor
  let k := Functor.mapDerivedCategoryCompIso (Mod.comap φ) eE.functor ≪≫
    Functor.mapDerivedCategoryNatIso (ProEtale.CondensedRing.sectionModuleComapIso T φ) ≪≫
    (Functor.mapDerivedCategoryCompIso eL.functor
      (pbcRestrict (ProEtale.CondensedRing.sectionRingMap T φ))).symm
  let a : ProEtale.derivedExtendScalarsSubfield T l h ⊣
      (Mod.comap φ).mapDerivedCategory := by
    exact @Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (ProEt.topology T) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (ProEtale.padicSubfieldRingObj T l E) (ProEtale.padicSubfieldRingObj T l L)
      _ _ hcommE hcommL φ _
  exact (scalarAdjunctionCoefficientEquivalence a
    (pbcDerivedScalarAdjunction (ProEtale.CondensedRing.sectionRingMap T φ))
    eE.functor.mapDerivedCategory eL.functor.mapDerivedCategory k).choose

/-- A commuting square of ring sheaves gives the normalized scalar-extension square.
The comparison is the unique left-adjoint comparison for the literal restriction square.
Source: change of rings and adjunction uniqueness, Stacks 03EK.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
@[irreducible] def coefficientExtensionSquare
    {R₀ R₁ R₂ S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ S) (c : R₀ ⟶ R₂) (d : R₂ ⟶ S)
    (h : a ≫ b = c ≫ d) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend b ≅
      pbcDerivedExtend c ⋙ pbcDerivedExtend d :=
  Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b)
    ((pbcDerivedScalarAdjunction c).comp (pbcDerivedScalarAdjunction d))
    (derivedRestrictionSquare a b d c h)

/-- The specified coefficient encodings commute with scalar extension.
Source: BS 6.8.2, tensor transitivity and the normalized coefficient square.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
@[irreducible] def finiteCondensedScalarEncoding (A : FiniteCondensedData l T)
    {E L : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ L) :
    ProEtale.derivedExtendScalarsSubfield T l h ⋙
        (finiteCondensedEncoding l T A L).functor ≅
      (finiteCondensedEncoding l T A E).functor ⋙
        pbcDerivedExtend (A.scalar.coefficient h).coefficient := by
  let φ := ProEtale.CondensedRing.sectionRingMap T
    (ProEtale.padicSubfieldRingObjMap T l h)
  let m := coefficientExtensionSquare T φ (A.closure.finiteIso L).hom
    (A.closure.finiteIso E).hom (A.scalar.coefficient h).coefficient
    (A.closure.coefficient_normalization h).symm
  exact Functor.isoWhiskerLeft (ProEtale.derivedExtendScalarsSubfield T l h)
      (eqToIso (finiteCondensedEncoding_functor l T A L)) ≪≫
    (Functor.associator (ProEtale.derivedExtendScalarsSubfield T l h)
      (sectionDerived T (ProEtale.padicSubfieldRingObj T l L))
      (pbcDerivedExtend (A.closure.finiteIso L).hom)).symm ≪≫
    Functor.isoWhiskerRight (finiteSectionScalarComparison l T h)
      (pbcDerivedExtend (A.closure.finiteIso L).hom) ≪≫
    Functor.associator (sectionDerived T (ProEtale.padicSubfieldRingObj T l E))
      (pbcDerivedExtend φ) (pbcDerivedExtend (A.closure.finiteIso L).hom) ≪≫
    Functor.isoWhiskerLeft (sectionDerived T (ProEtale.padicSubfieldRingObj T l E)) m ≪≫
    (Functor.associator (sectionDerived T (ProEtale.padicSubfieldRingObj T l E))
      (pbcDerivedExtend (A.closure.finiteIso E).hom)
      (pbcDerivedExtend (A.scalar.coefficient h).coefficient)).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (finiteCondensedEncoding_functor l T A E)).symm
      (pbcDerivedExtend (A.scalar.coefficient h).coefficient)

/-- Scalar compatibility for the finite condensed realizations, obtained by cancelling
its fully faithful ambient section encoding. The comparisons retain the actual tensor
associators and normalized field inclusions.
Source: BS 6.8.14(2), finite tensor comparison.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
@[irreducible] def finiteCondensedScalarComparison (A : FiniteCondensedData l T)
    {E L : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ L) :
    finiteCondensedFunctor l T A E ⋙ ProEtale.constructibleExtendScalars T l h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h ⋙
        finiteCondensedFunctor l T A L := by
  let Q := (ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj T l L)).ι ⋙
    (finiteCondensedEncoding l T A L).functor
  apply Functor.fullyFaithfulCancelRight Q
  exact Functor.isoWhiskerLeft
      (finiteCondensedFunctor l T A E ⋙
        (ProEtale.boundedConstructible (ProEtale.padicSubfieldRingObj T l E)).ι)
      (finiteCondensedScalarEncoding l T A h) ≪≫
    Functor.isoWhiskerRight (finiteCondensedComparison l T A E)
      (pbcDerivedExtend (A.scalar.coefficient h).coefficient) ≪≫
    (scalarComparison l T A.toCore A.scalar h).symm ≪≫
    Functor.isoWhiskerLeft
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h)
      (finiteCondensedComparison l T A L).symm

/-- The ambient finite realization after scalar extension to the condensed closure.
Source: BS 6.8.14(2).
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
def finiteCondensedClosureFunctor (A : FiniteCondensedData l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (ProEtale.padicAlgClRingObj T l)) :=
  finiteCondensedFunctor l T A E ⋙ ProEtale.constructibleToPadicAlgCl T l E ⋙
    (ProEtale.boundedConstructible (ProEtale.padicAlgClRingObj T l)).ι

/-- The canonical finite-field transition after extension to the condensed closure.
Source: BS 6.8.14(2), the finite tensor associator followed by the raw scalar comparison.
(blueprint: def-sf-locally-finite-adic-finite-condensed-realization). -/
def finiteCondensedClosureTransition (A : FiniteCondensedData l T)
    {E L : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ L) :
    finiteCondensedFunctor l T A E ⋙ ProEtale.constructibleToPadicAlgCl T l E ⋙
        (ProEtale.boundedConstructible (ProEtale.padicAlgClRingObj T l)).ι ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h ⋙
        finiteCondensedFunctor l T A L ⋙ ProEtale.constructibleToPadicAlgCl T l L ⋙
          (ProEtale.boundedConstructible (ProEtale.padicAlgClRingObj T l)).ι :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (finiteCondensedFunctor l T A E)
      (ProEtale.constructibleToPadicAlgClCompIso T l h).symm ≪≫
    Functor.isoWhiskerRight (finiteCondensedScalarComparison l T A h)
      (ProEtale.constructibleToPadicAlgCl T l L))
    (ProEtale.boundedConstructible (ProEtale.padicAlgClRingObj T l)).ι

end WeilConjectures.AdicFiniteRealization
