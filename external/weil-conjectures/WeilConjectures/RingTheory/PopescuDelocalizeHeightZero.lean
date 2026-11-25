/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizations
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZeroData
import WeilConjectures.RingTheory.PopescuDelocalizeWeak
import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

/-!
# Delocalizing a Popescu resolution at a prime of height zero

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA, Section 07F6
(blueprint: lem-weil-pbc-popescu-delocalize-height-zero).
-/

@[expose] public section

universe u v t

open scoped TensorProduct

namespace Algebra

/-- A resolution at a minimal prime over the extended singular ideal descends from the
local problem when the target localization has dimension zero.

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA
(blueprint: lem-weil-pbc-popescu-delocalize-height-zero).

Proof:
1. Since `A` is finite type over the Noetherian ring `R`, it is Noetherian, and its
singular ideal has finitely many generators `a_i`.
2. Minimality puts their images in `q`. The only prime of the zero-dimensional local
ring `Λ_q` is its maximal ideal, so each image is nilpotent. Choose a common positive
exponent `N` and clear denominators to obtain `λ ∉ q` with `λ α(a_i)^N = 0` for all `i`.
This uses elementwise nilpotence, without assuming `Λ_q` is Artinian.
3. The weak delocalization lemma (lem-weil-pbc-popescu-delocalize-weak, Tag 07F9) gives
`A → C → Λ` with `C` finitely presented over `R` and an element `c ∈ H_{C/R}` mapping
outside `q`. Since `A` is Noetherian, present `C = A[x_k]/(f_j)` and lift `c` to `p_c`.
4. Set `B = A[x_k,y_i,z,t_ij]/(f_j - ∑ y_i t_ij, z y_i)`, a finitely presented
`R`-algebra. Map `x_k` through `C`, `y_i` to `α(a_i)^N`, `z` to `λ`, and `t_ij` to zero.
The relations vanish. If `c'` is the class of `p_c`, then `δ(zc') = λ γ(c) ∉ q` and
`δ(a_i y_i) = α(a_i)^(N+1)`.
5. By lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations,
`B_z = C[t_ij,z]_z`. Polynomial extension and localization are smooth over `C`;
localizing also at `c'` gives a smooth algebra over the smooth `R`-algebra `C_c`.
Thus `B_(zc')` is smooth over `R`, and `zc' ∈ H_{B/R}`.
6. The same auxiliary lemma identifies `B_(y_l)` with a localized polynomial algebra
`A[x_k,y_i,t_ij (i ≠ l)]_(y_l)`. Localize further at `a_l`; polynomial extension,
localization and composition with the smooth map `R → A_(a_l)` show that
`B_(a_l y_l)` is smooth over `R`. Hence `a_l y_l ∈ H_{B/R}`.
7. The image of `zc'` shows `h_B ≰ q`. The images of `a_i y_i` put every `α(a_i)`
in `h_B`, hence `h_A ≤ h_B`. Together with finite presentation and the factorization,
these are exactly the conditions for a resolution. The construction also allows zero
generators or variables, interpreting empty products as one and empty sums as zero.

The tensor factors are reversed by the canonical commutativity isomorphism, so `A_p` is
`R_p ⊗[R] A` with the map of `lem-weil-pbc-popescu-delocalize-weak`; the local algebra
structure on `Λ_q` is the canonical one. `dim Λ_q = 0` is `ringKrullDim Λ_q = 0`. -/
theorem canBePopescuResolved_of_local_height_zero
    {R : Type u} {A : Type v} {Λ : Type t}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    (hlocal :
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      CanBePopescuResolved
        (Algebra.TensorProduct.lift
          (Algebra.ofId (Localization.AtPrime (q.asIdeal.under R))
            (Localization.AtPrime q.asIdeal))
          ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q.asIdeal)).comp α)
          (fun _ _ => Commute.all _ _))
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    CanBePopescuResolved α q := by
  obtain ⟨B, _instB, _algB, β, γ, hfp, hcomp, hle, hnot⟩ :=
    exists_popescu_resolution_data_of_local_height_zero α q hminimal hlocal hdim
  exact ⟨B, inferInstance, inferInstance, β, γ, hfp, hcomp, hle, hnot⟩

end Algebra
