/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.RingTheory.PopescuLiftChartFibres
import WeilConjectures.RingTheory.PopescuLiftChartFlat

@[expose] public section

universe a c

namespace Algebra

/-- The two special-fibre smoothness conclusions for the explicit prepared quotient.

Source: Stacks Project, Tag 07CP, construction of D_k and proof of properties (c), (d).
(blueprint: lem-weil-pbc-popescu-lift-smooth-special).

Proof: Put Q = R[x,z], u_j = f_j - π z_j, and
p_{kl} = a_k z_l - Σ_{j ∈ E_k} h_{klj} z_j - π g_{kl}.
The cleared relations imply π p_{kl} = -a_k u_l + Σ_{j ∈ E_k} h_{klj} u_j.
For a fixed chart k form D_k using
f_j-πz_j only for j in E_k and p_{kl} only for l outside E_k. Normalization makes
p_{kl}=0 for l in E_k, so there are exactly m relations in n+m variables. Modulo π
and after inverting a_k, solve for the z_l outside E_k. The resulting ring is
(Cbar/πCbar)_{a_k}[z_j : j in E_k], with the generator map in the statement.
The smooth chart and the complementary differential basis give, after base change,
a smooth fibre of dimension (n-|E_k|)+|E_k|=n. Equation count gives flatness at
primes containing π and avoiding a_k; the flat smooth fibre criterion gives
smoothness of R → D_k there. The key equality makes all f_l-πz_l vanish in
(D_k)_{a_k}. For another chart k', compute the relation among the conormal basis
with coefficients a_{k'}h_{klj}-Σh_{k'lj'}h_{kj'j}. Basis independence makes these
coefficients zero in the localized reduced quotient. Clear denominators, using
the cleared f relations, to put a power of a_k times each coefficient in I_E+π²P.
Expanding the p equations now puts p_{k'l} in π(D_k)_{a_k}. It is also killed by π
by the key equality. The smooth local ring is flat over R, so flat base change of
annihilators carries Ann_R(π)=Ann_R(π²) to that local ring, forcing p_{k'l}=0.
Thus every generator of the kernel D_k → D vanishes locally. This finite kernel
is killed on a principal neighbourhood outside the prime, where the quotient
map is an isomorphism. Transfer the two smoothness properties of D_k to D by
principal localization. Finally the cover property selects such a chart for
every prime in the special fibre lying over the smooth locus of Cbar. The generator
identity and cmod compatibility identify the special-fibre algebra structures.
ULift is an algebra equivalence and preserves all the constructions and properties.
-/
theorem popescu_lift_smooth_special (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] [IsNoetherianRing R] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (hAnnR : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)))
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) :
    (∀ q : PrimeSpectrum (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)),
      IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R))
        (PrimeSpectrum.comap c.toRingHom q) →
      IsSmoothAtPrime R (PrimeSpectrum.comap (Ideal.Quotient.mk _) q)) ∧
    (∀ q : PrimeSpectrum (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)),
      IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R))
        (PrimeSpectrum.comap c.toRingHom q) →
      @IsSmoothAtPrime (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar))
        (d.liftingAlgebra ⧸
          Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra))
        _ _ cmod.toAlgebra q) := by
  rw [← forall_and]
  intro q
  rw [← imp_and]
  intro hq
  obtain ⟨k, hk⟩ := hd.cover (PrimeSpectrum.comap c.toRingHom q) hq
  obtain ⟨hfibre, hspecial⟩ :=
    popescu_lift_chart_fibres R Cbar π d hd c cmod hc hcmod q k hk
  have hflat := popescu_lift_chart_flat R Cbar π d hd hAnnR c hc q k hk
  have : FinitePresentation R d.liftingAlgebra := d.finitePresentation
  let qD : PrimeSpectrum d.liftingAlgebra :=
    PrimeSpectrum.comap (Ideal.Quotient.mk _) q
  have hfp : ∃ g : d.liftingAlgebra,
      g ∉ qD.asIdeal ∧
      FinitePresentation R (Localization.Away g) :=
    ⟨1, qD.isPrime.one_notMem,
      FinitePresentation.of_isLocalizationAway (1 : d.liftingAlgebra)⟩
  exact ⟨flat_smooth_fibre_smooth_at_prime (R := R)
    (S := d.liftingAlgebra) qD hfp hflat hfibre,
    c (d.ε (d.reduced (d.a k))), hk, hspecial⟩

end Algebra
