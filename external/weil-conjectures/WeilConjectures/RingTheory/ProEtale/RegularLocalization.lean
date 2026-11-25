/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.Etale.IntegrallyClosedLocalization
public import WeilConjectures.RingTheory.ProEtale.IndZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Local rings of weakly étale algebras over regular or normal rings are domains

Let `R` be a ring such that the localizations at primes of every étale `R`-algebra are domains,
e.g. a ring all of whose localizations at primes are regular local rings
(`IsRegularLocalRing.localization_of_etale_of_comap`), or integrally closed domains
(`Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap`). A localization at a
prime of an ind-étale `R`-algebra is a filtered colimit of localizations of étale `R`-algebras,
hence a domain. Finally a weakly étale `R`-algebra `S` has a faithfully flat ind-étale
`S`-algebra `T` which is ind-étale over `R` (Stacks 097Z, `Algebra.WeaklyEtale.exists_indEtale`),
and a localization of `S` at a prime embeds into a localization of `T`, the local homomorphism
being flat, hence faithfully flat.

## Main statements

- `Algebra.IndEtale.isDomain_localization_of_etale`
- `Algebra.WeaklyEtale.isDomain_localization_of_etale`
- `Algebra.WeaklyEtale.isDomain_localization_of_isRegularLocalRing`
- `Algebra.WeaklyEtale.isDomain_localization_of_isIntegrallyClosed`
-/

@[expose] public section

universe u

open CategoryTheory Limits

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The localizations at primes of an étale algebra over a ring with regular local rings are
domains, being regular local rings. -/
theorem Algebra.Etale.isDomain_localization_of_isRegularLocalRing [Algebra.Etale R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  have := IsRegularLocalRing.localization_of_etale_of_comap (R := R) q (hR _)
  inferInstance

/-- The localizations at primes of an étale algebra over a ring whose localizations at primes
are integrally closed domains are domains (Stacks `033C`, étale case). -/
theorem Algebra.Etale.isDomain_localization_of_isIntegrallyClosed [Algebra.Etale R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  (Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap q (hR _)).1

open Localization.AtPrime in
/-- The localizations at primes of an ind-étale `R`-algebra are domains if those of every étale
`R`-algebra are: such a localization is the filtered colimit of the localizations of the étale
constituents, which are domains. -/
theorem Algebra.IndEtale.isDomain_localization_of_etale [Algebra.IndEtale R S]
    (hR : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A] (Q : Ideal A)
      [Q.IsPrime], IsDomain (Localization.AtPrime Q))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) := by
  obtain ⟨ι, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := R) (S := S)
  have hdom (i : ι) : IsDomain (Localization.AtPrime (contractionIdeal P q i)) :=
    have := hP i
    hR _ _
  let φ (i : ι) : Localization.AtPrime (contractionIdeal P q i) →+* Localization.AtPrime q :=
    ((localizationCocone P q).ι.app i).hom
  let ψ {i j : ι} (f : i ⟶ j) :
      Localization.AtPrime (contractionIdeal P q i) →+*
        Localization.AtPrime (contractionIdeal P q j) :=
    ((localizationDiag P q).map f).hom
  have hw {i j : ι} (f : i ⟶ j) (x : Localization.AtPrime (contractionIdeal P q i)) :
      φ j (ψ f x) = φ i x :=
    congrArg (fun g ↦ g.hom x) ((localizationCocone P q).w f)
  refine @NoZeroDivisors.to_isDomain _ _ ?_ ⟨fun {a b} hab ↦ ?_⟩
  · infer_instance
  obtain ⟨i, a', rfl⟩ := exists_localRingHom_eq P q a
  obtain ⟨i', b', rfl⟩ := exists_localRingHom_eq P q b
  change φ i a' * φ i' b' = 0 at hab
  change φ i a' = 0 ∨ φ i' b' = 0
  rw [← hw (IsFiltered.leftToMax i i') a', ← hw (IsFiltered.rightToMax i i') b'] at hab ⊢
  set a'' := ψ (IsFiltered.leftToMax i i') a'
  set b'' := ψ (IsFiltered.rightToMax i i') b'
  have hab' : ((localizationCocone P q).ι.app _).hom (a'' * b'') =
      ((localizationCocone P q).ι.app _).hom 0 := by
    change φ _ (a'' * b'') = φ _ 0
    rw [map_mul, map_zero]
    exact hab
  obtain ⟨k', f, hf⟩ := exists_localizationDiag_map_eq P q _ (a'' * b'') 0 hab'
  change ψ f (a'' * b'') = ψ f 0 at hf
  rw [map_mul, map_zero] at hf
  rcases mul_eq_zero.1 hf with h | h
  · left
    rw [← hw f a'', h, map_zero]
  · right
    rw [← hw f b'', h, map_zero]

/-- The localizations at primes of an ind-étale algebra over a ring with regular local rings
are domains. -/
theorem Algebra.IndEtale.isDomain_localization_of_isRegularLocalRing [Algebra.IndEtale R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  isDomain_localization_of_etale (R := R) (fun A _ _ _ Q _ ↦
    Algebra.Etale.isDomain_localization_of_isRegularLocalRing (S := A) hR Q) q

/-- **Weakly étale algebras have integral local rings if étale algebras do.** Let `R` be a ring
such that the localizations at primes of every étale `R`-algebra are domains and `S` a weakly
étale `R`-algebra. Then the localizations of `S` at primes are domains: there is a faithfully
flat ind-étale `S`-algebra `T` which is ind-étale over `R` (Stacks 097Z), whose localizations
are domains, and the localization of `S` at a prime `q` embeds into the localization of `T` at a
prime over `q`, the local homomorphism being flat, hence faithfully flat. -/
theorem Algebra.WeaklyEtale.isDomain_localization_of_etale [Algebra.WeaklyEtale R S]
    (hR : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A] (Q : Ideal A)
      [Q.IsPrime], IsDomain (Localization.AtPrime Q))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) := by
  obtain ⟨T, _, _, _, _, _, _, _⟩ := Algebra.WeaklyEtale.exists_indEtale R S
  obtain ⟨⟨Q, _⟩, hQ⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := T) ⟨q, inferInstance⟩
  have hQq : q = Q.comap (algebraMap S T) := congrArg PrimeSpectrum.asIdeal hQ.symm
  have := Algebra.IndEtale.isDomain_localization_of_etale hR Q
  have : Q.LiesOver q := ⟨hQq⟩
  let := Localization.AtPrime.algebraOfLiesOver q Q
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime Q) :=
    RingHom.Flat.localRingHom (f := algebraMap S T)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) Q q hQq
  have : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (FaithfulSMul.algebraMap_injective (Localization.AtPrime q)
    (Localization.AtPrime Q)).isDomain _

/-- **Weakly étale algebras over regular rings have integral local rings.** Let `R` be a ring all
of whose localizations at primes are regular local rings and `S` a weakly étale `R`-algebra.
Then the localizations of `S` at primes are domains. -/
theorem Algebra.WeaklyEtale.isDomain_localization_of_isRegularLocalRing [Algebra.WeaklyEtale R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  isDomain_localization_of_etale (R := R) (fun A _ _ _ Q _ ↦
    Algebra.Etale.isDomain_localization_of_isRegularLocalRing (S := A) hR Q) q

/-- **Weakly étale algebras over normal rings have integral local rings.** Let `R` be a ring all
of whose localizations at primes are integrally closed domains and `S` a weakly étale
`R`-algebra. Then the localizations of `S` at primes are domains. -/
theorem Algebra.WeaklyEtale.isDomain_localization_of_isIntegrallyClosed [Algebra.WeaklyEtale R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  isDomain_localization_of_etale (R := R) (fun A _ _ _ Q _ ↦
    Algebra.Etale.isDomain_localization_of_isIntegrallyClosed (S := A) hR Q) q
