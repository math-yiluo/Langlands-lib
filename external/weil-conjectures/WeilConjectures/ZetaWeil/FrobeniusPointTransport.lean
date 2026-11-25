/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible
import WeilConjectures.TraceFormula.Integral.IntegralPullbackReductionCounit

/-!
# Point transport along geometric Frobenius

Source: Deligne, Weil II (1.1.7), pp. 150--151; the explicit restriction,
comma-coprojection and sheafification construction in the blueprint
(blueprint: def-weil-frobenius-point-transport).

The canonical sectionwise model of inverse image along an isomorphism identifies
its comma coprojection followed by sheafification with the identity on sections.
Thus sigma is the restriction along g_s in that model. The finite comparison is
the recorded tensor-unit map; the integral comparison is the recorded Roos lift,
not tensor extension by the completed coefficient sheaf. Rational transport is
scalar extension of the integral arrow. The algebraic-closure arrow is represented
at the object's own coefficient stage. No naturality or invertibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Spec of the geometric field Frobenius, with its prescribed inverse.
Source: Deligne, Weil II (1.1.7) (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIso (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- The arrow (s,g_s) to (s,id) of the small pro-etale site.
Source: blueprint restriction formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointRestriction (D : FiniteFieldDatum.{u}) :
    (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))) ⟶ ProEt.mk (𝟙 (Spec (.of D.k))) :=
  (ProEt.forget (Spec (.of D.k))).preimage (Over.homMk (frobeniusPointIso D).hom)

attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The same excluded characteristic makes l a unit in the residue fields.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport).
Proof: the unique point has residue field canonically k, of characteristic p.
The image of l is nonzero because l and p are distinct primes, hence invertible. -/
theorem frobeniusPointPrimeResidueUnit (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).residueField x) := by
  intro x
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have h := hk.map
    ((StructureSheaf.toStalk (CommRingCat.of D.k) x) ≫ (Spec (.of D.k)).residue x).hom
  simpa only [map_natCast] using h

/-- The canonical inverse of the residue-field unit; no extra hypothesis on s.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport). -/
@[instance_reducible]
def frobeniusPointPrimeInvertible (x : Spec (.of D.k)) :
    Invertible (l : (Spec (.of D.k)).residueField x) :=
  (frobeniusPointPrimeResidueUnit D l hl x).invertible

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem pointFiniteScalar_restriction (n : ℕ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) :
    (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))
        (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)) a) =
      (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.map
        (frobeniusPointRestriction D).op
        (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)) a) := by
  let A := CommRingCat.of
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
  let U := ProEt.mk (𝟙 (Spec (.of D.k)))
  let c := inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n
  have hn := (isoSectionwiseConstantMap_existsUnique.{u, u}
    (frobeniusPointIso D).hom A).exists.choose_spec U a
  have hr := congrArg (fun f ↦ f a)
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)).naturality
        (frobeniusPointRestriction D).op)
  have hi := congrArg (fun f ↦ f.hom.app (op U)
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)) a))
    (IsIso.hom_inv_id c)
  have hh := congrArg (fun x ↦ (inv c).hom.app (op U) x) hn
  change _ = (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.map
    (frobeniusPointRestriction D).op (pointConstantSectionMap D.k _ a) at hr
  change _ = (inv c).hom.app (op U) (pointConstantSectionMap D.k _ a) at hh
  change _ = _ at hi
  exact hh.symm.trans (hi.trans hr)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def sectionRestrictionLinear
    {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (M : PresheafOfModules.{u + 1} R) {U V : Cᵒᵖ} (r : U ⟶ V)
    {A : Type (u + 1)} [Ring A] (a : A →+* R.obj U) (b : R.obj U →+* R.obj V)
    (h : ∀ c, R.map r (a c) = b (a c)) :
    (ModuleCat.restrictScalars a).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars b).obj (M.obj V)) := by
  refine ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars a).obj (M.obj U))
    (Y := (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars b).obj (M.obj V)))
    { toFun := fun x ↦ M.map r x
      map_add' := fun x y ↦ (M.map r).hom.map_add x y
      map_smul' := ?_ }
  intro c x
  exact (M.map_smul r (a c) x).trans
    (congrArg (fun d ↦ @SMul.smul _ _ (M.obj V).isModule.toSMul d (M.map r x)) (h c))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def pointFiniteSigmaTerm (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj M ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).obj M) := by
  exact sectionRestrictionLinear M.val (frobeniusPointRestriction D).op
    (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)))
    ((inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom
    (fun a ↦ (pointFiniteScalar_restriction D l E n a).symm)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/-- The finite sigma chain map is uniquely fixed on every term and section.
Source: blueprint finite/integral paragraph (blueprint: def-weil-frobenius-point-transport).
Proof: use restriction along g_s and then the distinguished comma coprojection
and the sheafification unit. In the recorded sectionwise inverse-image model the
latter two maps identify the section with itself. Restrictions commute with d.
The constant coefficient comparison fixes every constant section, so restriction
is linear for the transported c inverse action. Equality on all sections proves
uniqueness of the chain map. No naturality in derived morphisms is used. -/
theorem frobeniusPointFiniteSigma_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ∃! f : ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  let f : ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
          (.up ℤ)).obj K) :=
    { f i := pointFiniteSigmaTerm D l E n (K.X i)
      comm' i j _ := by
        ext x
        exact (PresheafOfModules.naturality_apply (K.d i j).val
          (frobeniusPointRestriction D).op x) }
  refine ⟨f, fun _ ↦ HEq.rfl, ?_⟩
  intro g hg
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  exact congrFun (eq_of_heq (hg i)) x

/-- Sigma is the specified chain map res, ins, sheafification, in its sectionwise model.
Source: blueprint displayed sigma (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointFiniteSigma (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
               (.up ℤ)).obj K) :=
  Classical.choose (frobeniusPointFiniteSigma_existsUnique D l E n K)

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures
