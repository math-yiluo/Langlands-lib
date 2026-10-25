# Private bridge sources and exact host statements

These are **private experiment files**, retained as text, not Library modules or accepted mathematical records. Worker 159 implemented the adapters following Worker 35's proposed prime/discriminant/residue-field route. Worker 65 clarified the secondary endpoint.

## AuditRoot.lean

SHA256 `ac38a6e118e553a2053c1963892ca993f443fb55dbe5acbe5b67f54ff3c1f061`.

```lean
import Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois
set_option pp.universes true in
#check @NumberField.exists_prime_isArithFrobAt_of_isGalois
#print axioms NumberField.exists_prime_isArithFrobAt_of_isGalois
```

```markdown
# Root inspection

Private audit command by Worker 159. Prints the complete upstream Chebotarev declaration type with universe levels and its kernel axioms; no mathematical assertion is added. Compilation/inspection is development evidence only.
```

## AuditBridges.lean

SHA256 `a762fcee9d2d6191e5233cc613779947099226b9585a932583a795b9e30db78e`.

```lean
import AuditRoot
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/- Private interface experiment by Worker 159, 25 October 2026. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped Pointwise NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
universe u v
namespace ChebotarevAudit
variable {K : Type u} {L : Type v} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]

 theorem liesOver_of_prime_mem (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hm : (p : 𝓞 L) ∈ Q) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  exact (Ideal.liesOver_span_iff Ideal.IsPrime.ne_top'
    (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa using hm)

 theorem unramified_of_not_dvd_discr (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hm : (p : 𝓞 L) ∈ Q)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr L) : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  have : Algebra.IsUnramifiedAt ℤ Q :=
    (NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L)
      (Nat.prime_iff_prime_int.mp hp)).mp hd Q inferInstance (by simpa using hm)
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q

 theorem outside_finite_set (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (havoid : p ∉ S.image (fun w => (w.asIdeal.under ℤ).absNorm)) : v ∉ S := by
  classical
  intro hv
  apply havoid
  have hc : (v.asIdeal.under ℤ).absNorm = p := by
    rw [← v.asIdeal.over_def (Ideal.span {(p : ℤ)}), Ideal.absNorm_span_natCast]
    simp
  exact hc ▸ Finset.mem_image_of_mem (fun w => (w.asIdeal.under ℤ).absNorm) hv

 theorem localDegree_ne_one [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L) (hne : σ ≠ 1)
    (hf : IsArithFrobAt ℤ σ w.asIdeal) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≠ 1 := by
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  intro hd
  have hc := Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    ← Langlands.Global.AdelicFunctoriality.localDegree_eq v w, hd] at hc
  haveI hs : Subsingleton (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  exact hne (congrArg Subtype.val
    (Subsingleton.elim (⟨σ, hf.mem_stabilizer⟩ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) 1))

end ChebotarevAudit
set_option pp.universes true in
#check @ChebotarevAudit.localDegree_ne_one
#print axioms ChebotarevAudit.localDegree_ne_one
#print axioms ChebotarevAudit.outside_finite_set
#print axioms ChebotarevAudit.unramified_of_not_dvd_discr
#print axioms ChebotarevAudit.liesOver_of_prime_mem
```

```markdown
# Private Chebotarev interface experiment

Worker 159's derived adapters, 25 October 2026. This file imports the privately adapted Anthropic closure and the current Library, and has no publication or exact-target status. It tests ideal lies-over from rational-prime membership, discriminant exclusion followed by restriction of scalars for unramifiedness, finite avoidance by the rational primes below a finite set, and nontrivial canonical completion degree from a nonidentity absolute Frobenius. The last proof uses Mathlib's decomposition-group cardinality and the Library localDegree_eq, without unramifiedness or cyclicity. Original source notices are retained in the surrounding private draft.
```

## AuditRelative.lean

SHA256 `d120139099756689960e541085f8afe60bc6ed989e96bcc42496637fcd7ebd63`.

```lean
import AuditBridges

/- Private interface experiment by Worker 159, 25 October 2026. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped Pointwise NumberField
universe u v
namespace ChebotarevAudit
variable {K : Type u} {L : Type v} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]

 theorem base_card_eq_prime (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : L ≃ₐ[K] L) (hf : IsArithFrobAt ℤ σ Q) :
    Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = p := by
  classical
  have hZ : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← Q.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot]
  let P := Q.under (𝓞 K)
  have hpow : ∀ y : 𝓞 K ⧸ P, y ^ p = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := hf (algebraMap (𝓞 K) (𝓞 L) x)
    have hfix : (MulSemiringAction.toAlgHom ℤ (𝓞 L) σ)
        (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) x := by
      apply RingOfIntegers.ext
      change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
      exact σ.commutes (x : K)
    rw [hZ, hfix, ← map_pow, ← map_sub] at hx
    rw [← map_pow, eq_comm, Ideal.Quotient.eq]
    exact hx
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hle : Nat.card (𝓞 K ⧸ P) ≤ p := by
    rw [Nat.card_eq_fintype_card]
    exact P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.P2mCycloSplit.card_le_of_forall_pow_eq hp.one_lt hpow
  have hZP : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    dsimp [P]
    rw [Ideal.under_under]
    exact hZ
  have hge : p ≤ Nat.card (𝓞 K ⧸ P) := by
    rw [← hZP]
    exact Nat.card_le_card_of_injective
      (algebraMap (ℤ ⧸ P.under ℤ) (𝓞 K ⧸ P)) Ideal.algebraMap_quotient_injective
  exact Nat.le_antisymm hle hge

 theorem relative_frobenius (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : L ≃ₐ[K] L) (hf : IsArithFrobAt ℤ σ Q) :
    (RingOfIntegers.mapAlgHom σ).IsArithFrobAt Q := by
  have hc := base_card_eq_prime p hp Q σ hf
  have hZ : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← Q.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot]
  intro x
  have hx := hf x
  rw [hZ] at hx
  rw [hc]
  exact hx
end ChebotarevAudit
set_option pp.universes true in
#check @ChebotarevAudit.base_card_eq_prime
set_option pp.universes true in
#check @ChebotarevAudit.relative_frobenius
#print axioms ChebotarevAudit.base_card_eq_prime
#print axioms ChebotarevAudit.relative_frobenius
```

```markdown
# Private base-residue and Frobenius experiment

Worker 159's derived interface experiment, 25 October 2026; no publication or exact-target acceptance. An absolute Frobenius fixes the image of the base field, so all base-residue elements satisfy x^p=x. The polynomial-root bound from the audited external closure gives cardinality at most p; the injective map from the integer residue field gives at least p. Rewriting this cardinality identifies the absolute Frobenius predicate with the Library's RingOfIntegers.mapAlgHom relative predicate. This is a proposed proof until a successful terminal check is recorded.
```

## AuditRealization.lean

SHA256 `7cc47943f8af7b4209df2e2a4879618b01fe8116cd5f1a4dac8787d9e91e4fc8`.

```lean
import AuditRelative
import Langlands.Global.Arithmetic.ChebotarevStatement

/- Private endpoint experiment by Worker 159, 25 October 2026. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
universe u v
namespace ChebotarevAudit

 theorem realization : Langlands.Global.ChebotarevPrimeRealizationStatement.{u,v} := by
  classical
  intro K _ _ L _ _ _ _ σ S
  let T := S.image (fun w => (w.asIdeal.under ℤ).absNorm) ∪ (NumberField.discr L).natAbs.primeFactors
  obtain ⟨p, hp, hpT, Q, hQ, hpQ, hf⟩ :=
    NumberField.exists_prime_isArithFrobAt_of_isGalois K L σ T
  haveI : Q.IsMaximal := hQ
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_prime_mem p hp Q hpQ
  have hQ0 : Q ≠ ⊥ := (Q.bot_lt_of_maximal (RingOfIntegers.not_isField L)).ne'
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, hQ0⟩
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.IsIntegral.under_ne_bot (𝓞 K) hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs (Q.LiesOver (Q.under (𝓞 K)))
  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    inferInstanceAs ((Q.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
  have hpS : p ∉ S.image (fun x => (x.asIdeal.under ℤ).absNorm) := by
    intro h
    exact hpT (Finset.mem_union_left _ h)
  have hd : ¬ (p : ℤ) ∣ NumberField.discr L := by
    intro hd
    have hn : p ∣ (NumberField.discr L).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hd
    exact hpT (Finset.mem_union_right _
      (hp.mem_primeFactors hn (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L))))
  exact ⟨v, outside_finite_set S p hp v hpS, w, inferInstance,
    unramified_of_not_dvd_discr (K := K) p hp Q hpQ hd,
    relative_frobenius p hp Q σ hf⟩

end ChebotarevAudit
set_option pp.universes true in
#check @ChebotarevAudit.realization
#print axioms ChebotarevAudit.realization
```

```markdown
# Private realization endpoint experiment

Worker 159's bounded endpoint experiment, 25 October 2026. The target is the unchanged Library proposition `Langlands.Global.ChebotarevPrimeRealizationStatement` in independent universes. It applies the privately adapted external root outside rational primes under the given finite base set and prime divisors of the absolute discriminant of L. A maximal ideal is nonzero because the ring of integers is not a field; its contraction is nonzero by integrality. The preceding adapters supply actual lies-over, finite avoidance, relative unramifiedness and the precise `RingOfIntegers.mapAlgHom` predicate. Development compilation is feasibility evidence only; this is not a submitted or accepted proof and must not be imported as published mathematics.
```

## AuditInspection.lean

SHA256 `c36233614b9cb21d0fe5da0232c398960b6500122aa9a60a3361910b90b7b28f`.

```lean
import AuditRealization

/- Complete declaration and axiom display for private audit evidence. -/
set_option pp.universes true
#check @NumberField.exists_prime_isArithFrobAt_of_isGalois
#check @ChebotarevAudit.liesOver_of_prime_mem
#check @ChebotarevAudit.unramified_of_not_dvd_discr
#check @ChebotarevAudit.outside_finite_set
#check @ChebotarevAudit.localDegree_ne_one
#check @ChebotarevAudit.base_card_eq_prime
#check @ChebotarevAudit.relative_frobenius
#check @ChebotarevAudit.realization
#print axioms NumberField.exists_prime_isArithFrobAt_of_isGalois
#print axioms ChebotarevAudit.liesOver_of_prime_mem
#print axioms ChebotarevAudit.unramified_of_not_dvd_discr
#print axioms ChebotarevAudit.outside_finite_set
#print axioms ChebotarevAudit.localDegree_ne_one
#print axioms ChebotarevAudit.base_card_eq_prime
#print axioms ChebotarevAudit.relative_frobenius
#print axioms ChebotarevAudit.realization
```

```markdown
# Private declaration-inspection module

Worker 159, 25 October 2026. This module displays full universe-explicit types and axiom lists for the adapted external root and every bridge experiment. It defines no mathematics. Development checks do not supply independent semantic acceptance or an exact-target proof receipt.
```

## Unchanged host Langlands/Global/Arithmetic/ChebotarevStatement.lean

```lean
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Basic

/-!
# Finite Galois Frobenius realization and character rigidity

These are proposition definitions, not proofs of the assertions.
-/

noncomputable section

universe u v w z

namespace Langlands.Global

open NumberField IsDedekindDomain

/-- Every automorphism of a finite Galois number-field extension occurs as
arithmetic Frobenius above an unramified prime outside any finite set. -/
def ChebotarevPrimeRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    ∀ (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (RingOfIntegers K))),
      ∃ p : HeightOneSpectrum (RingOfIntegers K), p ∉ S ∧
        ∃ q : HeightOneSpectrum (RingOfIntegers L),
          q.asIdeal.LiesOver p.asIdeal ∧
          Algebra.IsUnramifiedAt (RingOfIntegers K) q.asIdeal ∧
          (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal

/-- Finite-dimensional complex representations of an actual finite Galois
group are determined by their unramified Frobenius traces outside a finite set. -/
def FiniteGaloisFrobeniusRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (V : Type w) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type z) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V)
    (τ : Representation ℂ (L ≃ₐ[K] L) W)
    (S : Finset (HeightOneSpectrum (RingOfIntegers K))),
    (∀ (p : HeightOneSpectrum (RingOfIntegers K)), p ∉ S →
      ∀ (q : HeightOneSpectrum (RingOfIntegers L)),
        q.asIdeal.LiesOver p.asIdeal →
        Algebra.IsUnramifiedAt (RingOfIntegers K) q.asIdeal →
        ∀ σ : L ≃ₐ[K] L,
          (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal →
          ρ.character σ = τ.character σ) →
      Nonempty (ρ.Equiv τ)

/-- The coherent finite Galois Chebotarev and representation-rigidity input. -/
def ChebotarevRigidityStatement : Prop :=
  ChebotarevPrimeRealizationStatement.{u, v} ∧
  FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}

end Langlands.Global
```

## Unchanged host Langlands/Global/Arithmetic/CyclicNonsplitPrimeStatement.lean

```lean
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Nonsplit finite primes in nontrivial cyclic extensions -/

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension

universe u v

/-- A nontrivial cyclic extension of number fields has a finite prime with
nontrivial completed degree outside every finite set. This states the cyclic
number-field specialization of Artin–Tate V §4, Theorem 2. -/
def CyclicNonsplitPrimeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    1 < Module.finrank F E →
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧
        ∃ (w : HeightOneSpectrum (𝓞 E)) (h : w.asIdeal.LiesOver v.asIdeal),
          letI := h
          Module.finrank (v.adicCompletion F) (w.adicCompletion E) ≠ 1

end Langlands.Global
```

## Original root text

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField

theorem NumberField.exists_prime_isArithFrobAt_of_isGalois
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ σ P := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.solution
```
