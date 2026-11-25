/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus

import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite-stage geometric Verdier biduality on the etale site

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2128 (blueprint: theorem-verdier-biduality--1).

The coefficient ring is the actual positive-level quotient A_(E,n), canonically
lifted to the coefficient universe of the small etale site. The conclusion uses
exactly the recorded constructibility and Tor-amplitude predicates, and the
canonical evaluation transpose of the source library. Its normalization is
that of definition-verdier-dual-evaluation--4; the proposition retains the pairing witness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry

namespace WeilConjectures

/-- The four categorical clauses of geometric biduality, with the functor and its
canonical double-dual transformation kept as parameters. This is a presentation of
invertibility, preservation, the restricted anti-equivalence, and exactness.
Source: blueprint order 2128 (blueprint: theorem-verdier-biduality--1). -/
def GeometricBidualityConclusion
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (V : Cᵒᵖ ⥤ C) (δ : 𝟭 C ⟶ V.rightOp ⋙ V) : Prop :=
  (∀ K, P K → IsIso (δ.app K)) ∧
  (∀ K, P K → P (V.obj (op K))) ∧
  (∃ e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory,
    Nonempty (e.functor ⋙ P.ι ≅ P.ι.op ⋙ V)) ∧
  ∃ s : V.CommShift ℤ,
    ∀ T : Triangle Cᵒᵖ, P T.obj₁.unop → P T.obj₂.unop → P T.obj₃.unop →
      T ∈ distTriang Cᵒᵖ →
      Triangle.mk (V.map T.mor₁) (V.map T.mor₂)
        (V.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈ distTriang C

/-- The finite-stage etale biduality conclusion, using the canonical evaluation transpose.
The pairing witness determines the evaluation transpose uniquely, so its existence
is part of the conclusion and imposes no extra assumption. The equivalence comparison
identifies the restricted functor on both objects and morphisms. Exactness uses the
ambient distinguished triangles whose vertices lie in the full subcategory; the
opposite category has the reversed integer shift. The local finite-ring instance
is the named finiteness theorem applied to the positive-level quotient.
Source: blueprint order 2128 (blueprint: theorem-verdier-biduality--1). -/
noncomputable def FiniteEtaleGeometricBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  Etale.AmbientDualityPairing
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
      (Etale.dualizingComplex
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) aX) ∧
    GeometricBidualityConclusion (finiteTorConstructibleEtale l E n hn X)
      (Etale.verdierDual
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) aX)
      (Etale.verdierDualDoubleDual
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) aX)

private lemma boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦ ?_⟩
    · exact (DerivedCategory.isGE_iff K a).2 fun i hi ↦ hz i (.inl hi)
    · exact (DerivedCategory.isLE_iff K b).2 fun i hi ↦ hz i (.inr hi)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private lemma finiteTorConstructibleEtale_iff_source
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X) :
    finiteTorConstructibleEtale l E n hn X K ↔
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X K := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  constructor
  · rintro ⟨hc, a, b, hab, ht⟩
    exact ⟨(boundedConstructible_iff_source _ X K).1 hc, a, b,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩
  · rintro ⟨hc, a, b, ht⟩
    exact ⟨(boundedConstructible_iff_source _ X K).2 hc, min a b, b, min_le_right _ _,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
        (ht.mono (min_le_left _ _) le_rfl)⟩

private theorem coefficient_invertible_exponent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    HasInvertibleExponent (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      (Spec (.of D.k)) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hlk : (l : D.k) ≠ 0 := fun hz ↦
    hl ((CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm.trans
      (ringChar.eq D.k D.p))
  have hu : IsUnit ((l ^ n : ℕ) : D.k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow n
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · exact ULift.down_injective hkill
  · simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom

private lemma derivedHom_exact (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : Etale.DerivedCategoryModule A X) :
    ∃ _ : ((Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj W).CommShift ℤ,
      ((Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj W).IsTriangulated := by
  let J := X.smallEtaleTopology
  let R := Sheaf.derivedRestrictScalars J (RingHom.id A)
  let S := Etale.scalarExtension (RingHom.id A) X
  let H := (Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj W
  let e₀ : Sheaf.restrictScalars J (RingHom.id A) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId A) ≪≫ F.obj.rightUnitor))
      (fun f ↦ by
        apply (sheafToPresheaf J _).map_injective
        ext U : 2
        exact (ModuleCat.restrictScalarsId A).hom.naturality (f.hom.app U))
  let eR : R ≅ 𝟭 _ := Functor.mapDerivedCategoryNatIso e₀ ≪≫
    Functor.mapDerivedCategoryIdIso _
  have : R.IsEquivalence := Functor.isEquivalence_of_iso eR.symm
  let adj : S ⊣ R := Adjunction.ofIsRightAdjoint R
  have : S.IsEquivalence := adj.isEquivalence_left_of_isEquivalence_right
  let sS := Etale.etaleHomScalarCommShift X (RingHom.id A)
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : S.IsTriangulated := adj.isTriangulated_leftAdjoint
  obtain ⟨v, hv, _⟩ := Etale.etaleHomComparison_thickLocus X (RingHom.id A)
  obtain ⟨sA, sB, sPhi, sPsi, _, _, _, _, hPhi, _, _⟩ := (hv W).2.1
  let : (H ⋙ S).CommShift ℤ := sPhi
  have : (H ⋙ S).IsTriangulated := hPhi
  let : H.CommShift ℤ := Functor.CommShift.ofComp (Iso.refl (H ⋙ S)) ℤ
  have hc := Functor.CommShift.ofComp_compatibility (Iso.refl (H ⋙ S)) ℤ
  exact ⟨inferInstance, (@Functor.isTriangulated_iff_comp_right
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    H S (H ⋙ S) (Iso.refl (H ⋙ S)) inferInstance sS sPhi hc
    inferInstance inferInstance inferInstance).2 hPhi⟩

private lemma verdierDual_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [HasInvertibleExponent A (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ _ : (Etale.verdierDual A a).CommShift ℤ,
      (Etale.verdierDual A a).IsTriangulated :=
  derivedHom_exact A X (Etale.dualizingComplex A a)

private lemma dual_equivalence_comparison
    {C : Type*} [Category C] (P : ObjectProperty C) (V : Cᵒᵖ ⥤ C)
    (hV : ∀ K, P K → P (V.obj (op K)))
    (δ : 𝟭 C ⟶ V.rightOp ⋙ V) (hδ : ∀ K, P K → IsIso (δ.app K)) :
    Nonempty ((P.liftDualEquivalence V hV δ hδ).functor ⋙ P.ι ≅ P.ι.op ⋙ V) :=
  ⟨Iso.refl _⟩

private lemma triangulated_map_explicit
    {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] [HasZeroObject C] [HasZeroObject D]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
      (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈ distTriang D :=
  F.map_distinguished T hT

private theorem geometric_biduality_conclusion
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (V : Cᵒᵖ ⥤ C) (δ : 𝟭 C ⟶ V.rightOp ⋙ V)
    (hδ : ∀ K, P K → IsIso (δ.app K))
    (hV : ∀ K, P K → P (V.obj (op K)))
    (hex : ∃ _ : V.CommShift ℤ, V.IsTriangulated) :
    GeometricBidualityConclusion P V δ := by
  refine ⟨hδ, hV, ?_, ?_⟩
  · exact ⟨P.liftDualEquivalence V hV δ hδ,
      dual_equivalence_comparison P V hV δ hδ⟩
  · obtain ⟨s, hs⟩ := hex
    let : V.CommShift ℤ := s
    have : V.IsTriangulated := hs
    exact ⟨s, fun T _ _ _ hT ↦ triangulated_map_explicit V T hT⟩

private theorem finite_geometric_biduality_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent A (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (P : ObjectProperty (Etale.DerivedCategoryModule A X))
    (hP : ∀ K, P K ↔ Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) X K) :
    Etale.AmbientDualityPairing (ModuleCat.{u + 1} A) X
        (Etale.dualizingComplex A a) ∧
      GeometricBidualityConclusion P (Etale.verdierDual A a)
        (Etale.verdierDualDoubleDual A a) := by
  refine ⟨(Etale.ambient_duality_pairing A a).1,
    geometric_biduality_conclusion P _ _ ?_ ?_ (verdierDual_exact A a)⟩
  · intro K hK
    exact Etale.isIso_verdierDualDoubleDual_app A a ((hP K).1 hK)
  · intro K hK
    exact (hP _).2 (Etale.constructibleFiniteTor_verdierDual A a ((hP K).1 hK))

/-- Finite-stage geometric Verdier biduality: the canonical double-dual map is
invertible, and Verdier duality is an exact contravariant anti-equivalence of
Dᵇ_ctf on the ordinary etale site of every separated finite-type scheme over the
global algebraically closed field. No pro-etale or integral category is substituted.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2128
(blueprint: theorem-verdier-biduality--1).

Proof:
1. Identify the finite-stage bounded-constructible and Tor-amplitude predicates
   with the source library's constructibleFiniteTor predicate. Bounds may be
   widened to [min a b,b], so this includes the zero complex and empty intervals.
2. The quotient is finite and is killed by l^n. Since l differs from the residue
   characteristic, l^n is invertible on the algebraically closed geometric base.
3. Apply the existing source theorems isIso_verdierDualDoubleDual_app and
   constructibleFiniteTor_verdierDual in Etale.Derived.VerdierBiduality.
   Their proof already performs the required geometric induction, so the
   geometric steps are reused rather than restated as new unproved lemmas.
4. Restrict the specified Verdier functor by ObjectProperty.liftDualEquivalence.
   Its inclusion comparison is the identity, on objects and morphisms.
5. For exactness specialize the triangulated internal-Hom comparison of
   lem-coef-etale-hom-thick-locus to identity scalar extension. Restriction of
   scalars along the identity is naturally isomorphic to the identity, hence
   its left adjoint is an exact equivalence. Reflect triangulatedness through
   this equivalence and apply map_distinguished with the obtained shift structure.
-/
theorem finite_stage_etale_geometric_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    FiniteEtaleGeometricBiduality l E n hn X aX := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have : HasInvertibleExponent
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l _hl E n
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact finite_geometric_biduality_core
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) aX
    (finiteTorConstructibleEtale l E n hn X)
    (finiteTorConstructibleEtale_iff_source l E n hn X)

end WeilConjectures
