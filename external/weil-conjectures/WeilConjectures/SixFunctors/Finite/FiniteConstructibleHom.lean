/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicSiteHomTransport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Internal Hom of finite-stage constructible complexes

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
proposition-six-operations-dctf--15, order 2138
(blueprint: proposition-six-operations-dctf--15).

## Main statements

* `WeilConjectures.finite_constructible_derivedHom_etale`
* `WeilConjectures.finite_constructible_derivedHom_proEtale`

The two statements give the etale and pro-etale assertions separately. On the etale
site the scalar ring is its canonical universe lift; on the pro-etale site the recorded
constant-ring module category already uses that lift. No perfectness is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

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

private theorem coefficient_invertibleExponent
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

private theorem etaleHomBound (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [HasInvertibleExponent A (Spec (.of k))]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (K L : Etale.DerivedCategoryModule A X)
    (hK : Etale.DerivedCategory.isBoundedConstructible A X K)
    (hL : Etale.DerivedCategory.isBoundedConstructible A X L)
    (hKt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b K)
    (hLt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X c e L) :
    Etale.DerivedCategory.isBoundedConstructible A X
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) ∧
      Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) := by
  obtain ⟨hc, ht⟩ := Etale.constructibleFiniteTor_derivedHom_of_isSeparated
    A (X ↘ Spec (.of k)) d hd
    ((boundedConstructible_iff_source A X K).1 hK) hKt
    ((boundedConstructible_iff_source A X L).1 hL) hLt
  exact ⟨(boundedConstructible_iff_source A X _).2 hc, ht⟩

-- Align quotient coefficient specializations with the canonical ring hierarchy.
attribute [local instance 2000] CommRing.toRing

/-- Etale internal Hom is bounded constructible, with the asserted Tor interval.
The input intervals already imply finite Tor amplitude. Finiteness of the lifted
coefficient ring is supplied by the recorded positive-level finiteness theorem.
Source: blueprint order 2138 (blueprint: proposition-six-operations-dctf--15).

Proof:
1. General biduality (theorem-verdier-biduality--1) identifies L with D_X D_X L.
Apply internal Hom(K,-), then the natural currying isomorphism of
lem-weil-pbc-ringed-internal-hom-exact-restriction, to identify the result with
D_X(K tensor^L D_X L), without a perfectness hypothesis.
2. By lemma-verdier-duality-preserves-constructibility--1, D_X L is constructible with interval
[-e-2d,-c]. By proposition-six-operations-dctf--14 the tensor with K is constructible with interval
[a-e-2d,b-c]. Dualizing again gives bounded constructibility and the interval
[c-b-2d,e-a+2d]. Transport these properties across the displayed isomorphism. -/
theorem finite_constructible_derivedHom_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (K L : Etale.DerivedCategoryModule (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X K)
    (_hL : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X L)
    (_hKt : Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X a b K)
    (_hLt : Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X c e L) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X
      (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj L) ∧
    Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
      (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
      (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj L) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertibleExponent D l _hl E n
  exact etaleHomBound D.k A X d _hd a b c e K L _hK _hL _hKt _hLt

attribute [local irreducible] Etale.derivedHom ProEtale.derivedHom
  derivedInternalHomOfUniverses

private theorem torAmplitude_iso
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (f : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    HasProEtaleTorAmplitude X A L a b := by
  refine ⟨h.1, ?_⟩
  intro M P he g hg hP N i hi
  exact h.2 M P (he.map (fun e ↦ e ≪≫ f.symm)) g hg hP N i hi

private theorem finiteTor_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)}
    (f : K ≅ L) (h : finiteTorConstructible l E n hn X K) :
    finiteTorConstructible l E n hn X L := by
  refine ⟨(finiteTorsionConstructible D l hl E n hn X).prop_of_iso f h.1, ?_⟩
  obtain ⟨a, b, ht⟩ := h.2
  exact ⟨a, b, torAmplitude_iso X _ f a b ht⟩

/-- Pro-etale internal Hom preserves finite-Tor bounded constructibility and has the
same interval bound. The internal Hom is the recorded Hom-complex localization on the
original small site, whose object and morphism universes remain distinct.
Source: blueprint order 2138 (blueprint: proposition-six-operations-dctf--15).

Proof:
1. By theorem-comparison-constructible-sheaves choose bounded constructible etale
origins K', L'. By clause (ii) of lem-sf-comparison-tor-amplitude they retain the
original intervals [a,b] and [c,e].
2. Apply the etale argument: biduality theorem-verdier-biduality--1 and currying
lem-weil-pbc-ringed-internal-hom-exact-restriction give Hom(K',L') as
D_X(K' tensor^L D_X L'). The two duality bounds of
lemma-verdier-duality-preserves-constructibility--1 and tensor bound
proposition-six-operations-dctf--14 give bounded constructibility and interval [c-b-2d,e-a+2d].
3. By proposition-six-operations-dctf--15, inverse image of this internal Hom
is the internal Hom of the inverse images. That comparison applies since K' is
finite-Tor constructible and L' is bounded constructible. Clause (i) of
lem-sf-comparison-tor-amplitude preserves bounded constructibility and the exact
interval. Transport through the chosen identifications with K,L. -/
theorem finite_constructible_derivedHom_proEtale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hK : finiteTorConstructible l E n hn X K)
    (_hL : finiteTorConstructible l E n hn X L)
    (_hKt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) K a b)
    (_hLt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) L c e) :
    finiteTorConstructible l E n hn X
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, L)) ∧
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, L))
      (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let Λ := ULift.{u + 1, u} A
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let G := ProEtale.finiteCoefficientIntrinsicRealization X A
  let : G.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact X A).1
  let R := G.mapDerivedCategory
  let P := finiteTorConstructibleEtale l E n hn X
  let Q := finiteTorConstructibleProEtaleModule l E n hn X
  have hc := finite_duality_site_comparison D l _hl E n hn X
  dsimp only [FiniteDualitySiteComparison, ProEtale.FiniteDualityComparisonData] at hc
  have hHom := hc.1
  obtain ⟨eqv, ⟨eqvIso⟩⟩ := hc.2.choose_spec.2.choose_spec.choose_spec.2.1
  have origin (M : proEtaleDerivedCategory X A)
      (hM : finiteTorConstructible l E n hn X M) :
      ∃ M' : Etale.DerivedCategoryModule Λ X, P M' ∧
        Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj M' ≅ M) := by
    let M₀ := R.objPreimage M
    let e₀ : R.obj M₀ ≅ M := R.objObjPreimageIso M
    have hM₀ : Q M₀ := finiteTor_iso D l _hl E n hn X e₀.symm hM
    let N : Q.FullSubcategory := ⟨M₀, hM₀⟩
    let N' := eqv.inverse.obj N
    refine ⟨N'.obj, N'.property, ⟨?_⟩⟩
    exact (Functor.mapDerivedCategoryCompIso F G).symm.app N'.obj ≪≫
      R.mapIso ((eqvIso.app N').symm ≪≫ Q.ι.mapIso (eqv.counitIso.app N)) ≪≫ e₀
  obtain ⟨K', hK', ⟨eK⟩⟩ := origin K _hK
  obtain ⟨L', hL', ⟨eL⟩⟩ := origin L _hL
  have hunit : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  have hKt := finiteCoefficient_comparison_reflects_torAmplitude D l _hl E n hn X a b
    K' ((boundedConstructible_iff_source Λ X K').1 hK'.1).1.1
    K _hK.1 _hKt eK.symm
  have hLt := finiteCoefficient_comparison_reflects_torAmplitude D l _hl E n hn X c e
    L' ((boundedConstructible_iff_source Λ X L').1 hL'.1).1.1
    L _hL.1 _hLt eL.symm
  have hh := finite_constructible_derivedHom_etale D l _hl E n hn X d _hd
    a b c e _hab _hce K' L' hK'.1 hL'.1
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hKt)
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hLt)
  let H := ((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K')).obj L'
  have habound : c - b - 2 * (d : ℤ) ≤ e - a + 2 * (d : ℤ) := by omega
  have hp := finiteCoefficient_comparison_preserves_torAmplitude D l _hl E n hn X
    (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) habound H hh.1
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hh.2)
  let : F.PreservesFlat := ProEtale.preservesFlat_comparisonUpperStar (X := X)
  have : IsIso (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K' L') :=
    hHom K' L' hK' hL'.1
  obtain ⟨et⟩ := ProEtale.intrinsicSiteHom_transport X A
    (F.mapDerivedCategory.obj K') (F.mapDerivedCategory.obj L')
  let ecompK := (Functor.mapDerivedCategoryCompIso F G).symm.app K'
  let ecompL := (Functor.mapDerivedCategoryCompIso F G).symm.app L'
  let homIso := (derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology X) (proEtaleConstantRing X A)).mapIso
      ((ecompK.symm ≪≫ eK).symm.op.prod (ecompL.symm ≪≫ eL))
  let eH := (Functor.mapDerivedCategoryCompIso F G).symm.app H ≪≫
    R.mapIso (asIso (ProEtale.siteComparisonEvaluationHom
      (ModuleCat.{u + 1} Λ) X K' L')) ≪≫ et ≪≫ homIso
  have ht := torAmplitude_iso X A eH _ _ hp.2
  exact ⟨⟨(finiteTorsionConstructible D l _hl E n hn X).prop_of_iso eH hp.1,
    ⟨_, _, ht⟩⟩, ht⟩

end WeilConjectures
