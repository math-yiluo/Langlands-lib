/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.RingTheory.FlatScalarExtensionTorComparison
import WeilConjectures.RingTheory.PolynomialInducedPresentation
import all WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Tor bound for adjoining a single variable
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7, pp. 101–102.
(blueprint: lem-pc-polynomial-successor-tor-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

private theorem polynomial_castSucc_flat
    {A : Type u} [CommRing A] (n : ℕ) :
    (MvPolynomial.rename (R := A) (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom.Flat := by
  let e := (MvPolynomial.renameEquiv A (finRotate (n + 1))).trans
    (MvPolynomial.finSuccEquiv A n)
  have he : e.toRingEquiv.toRingHom.comp
      (MvPolynomial.rename Fin.castSucc).toRingHom =
      (Polynomial.C : MvPolynomial (Fin n) A →+* _) := by
    ext a : 1
    · ext x : 1
      simp [e, MvPolynomial.finSuccEquiv_apply]
    · have hj : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
      simp [e, hj, MvPolynomial.finSuccEquiv_X_succ]
  apply (RingHom.Flat.comp_iff_of_bijective_left
    (f := (MvPolynomial.rename Fin.castSucc).toRingHom)
    (g := e.toRingEquiv.toRingHom) e.bijective).mp
  rw [he]
  change (algebraMap (MvPolynomial (Fin n) A) (Polynomial (MvPolynomial (Fin n) A))).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

private theorem tor_isZero_of_shortExact
    {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (N : ModuleCat.{u} R) (j : ℕ)
    (h₂ : IsZero (((Tor' (ModuleCat.{u} R) (j + 1)).obj S.X₂).obj N))
    (h₁ : IsZero (((Tor' (ModuleCat.{u} R) j).obj S.X₁).obj N)) :
    IsZero (((Tor' (ModuleCat.{u} R) (j + 1)).obj S.X₃).obj N) := by
  classical
  have hu := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hv := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  obtain ⟨P, P', P'', a, b, w, _, _, hs⟩ :=
    CategoryTheory.resolutionSES S.f.hom S.g.hom hu hv hex
  let T := ShortComplex.mk a b w
  let F := (MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj N
  let TN := T.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  have hTN : TN.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro k
    exact ((hs k).some.map F).shortExact
  have h₂' : IsZero (TN.X₂.homology (j + 1)) :=
    h₂.of_iso (P'.isoLeftDerivedObj F (j + 1)).symm
  have h₁' : IsZero (TN.X₁.homology j) :=
    h₁.of_iso (P.isoLeftDerivedObj F j).symm
  have hij : (ComplexShape.down ℕ).Rel (j + 1) j := by simp
  have : Mono (hTN.δ (j + 1) j hij) := hTN.mono_δ _ _ _ h₂'
  exact (h₁'.of_mono (hTN.δ (j + 1) j hij)).of_iso
    (P''.isoLeftDerivedObj F (j + 1))

/-- Adjoining one variable raises a Tor bound by at most one.
Source: Weibel, An Introduction to Homological Algebra, Theorem 4.3.7, pp. 101–102.
Proof: put R = A[t_0,...,t_{n-1}] and S = R[t_n], using the coefficient inclusion
`rename Fin.castSucc`. For L = M restricted to R, let E = S tensor_R L. The maps
on E given by delta(f tensor m) = t_n f tensor m - f tensor (t_n m) and
aug(f tensor m) = f m are S-linear and form 0 -> E -> E -> M -> 0.
To see delta is injective, expand an element as sum t_n^j tensor m_j: its top
coefficient in delta is the top m_j. To see ker aug = im delta, subtract delta
of the term one degree lower to eliminate the highest coefficient, then descend
until the remaining degree-zero coefficient is zero by aug. Aug is surjective
since aug(1 tensor m) = m. Freeness of S over R means extension of an R-projective
resolution of L is an S-projective resolution of E. Tensor associativity, and
exactness of restriction of scalars, identify restricted Tor_i^S(E,N) with
Tor_i^R(L,N restricted to R). Hence both copies of E have zero Tor above d.
For i > d+1, the exact segment Tor_i^S(E,N) -> Tor_i^S(M,N) ->
Tor_{i-1}^S(E,N) has zero ends, proving the conclusion. This argument also covers
n=0, d=0, the zero module, and the zero ring; no degree of a nonzero scalar
polynomial and no domain assumption is used.
(blueprint: lem-pc-polynomial-successor-tor-bound) -/
theorem polynomial_successor_tor_bound
    {A : Type u} [CommRing A]
    (n : ℕ) (M : ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A)) (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} (MvPolynomial (Fin n) A), ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin n) A)) i).obj
        ((restrictScalars (MvPolynomial.rename Fin.castSucc).toRingHom).obj M)).obj N)) :
    ∀ N : ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A), ∀ i : ℕ, d + 1 < i →
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A)) i).obj M).obj N) := by
  intro N i hi
  let ρ : MvPolynomial (Fin n) A →+* MvPolynomial (Fin (n + 1)) A :=
    (MvPolynomial.rename Fin.castSucc).toRingHom
  let L := (restrictScalars ρ).obj M
  let E := (extendScalars ρ).obj L
  have hE (j : ℕ) (hj : d < j) :
      IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin (n + 1)) A)) j).obj E).obj N) := by
    obtain ⟨e⟩ := nonempty_flat_scalar_extension_tor_iso ρ (polynomial_castSucc_flat n)
      L N j
    have h := (hTor ((restrictScalars ρ).obj N) j hj).of_iso e
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact (ModuleCat.isZero_iff_subsingleton (R := MvPolynomial (Fin n) A)).mp h
  obtain ⟨δ, π, w, hS⟩ := exists_polynomial_induced_presentation n M
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact tor_isZero_of_shortExact (ShortComplex.mk δ π w) hS N j
    (hE (j + 1) (by omega)) (hE j (by omega))

end ModuleCat
