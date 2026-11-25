/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EssentiallySmoothComp
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.Ring.ULift

/-!
# Initial coefficient algebra over the unlocalized polynomial quotient

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 9 and 25.
(blueprint: lem-weil-pbc-popescu-coefficient-start).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Put the initial local coefficient solution over the unlocalized quotient and lift A.
Source: Stacks Project, Lemma 07FJ, steps 9 and 25; Algebra, localization base change.
(blueprint: lem-weil-pbc-popescu-coefficient-start).

Proof: Identify the two extended prime ideals with the respective local maximal ideals.
The positive power of each maximal ideal is proper, so the target quotient is local.
The polynomial quotient B maps to the localized polynomial quotient Q because the
image of p₀^n is zero. Localization commutes with quotient, so Q is a localization of B,
hence essentially smooth over B. Compose this map with the essentially smooth Q to D₀
map. Give D₀ its k-algebra structure through B and Q; all scalar diagrams commute by
hψ₀ and hfactor₀. The flat local map g₀ is faithfully flat, and therefore injective.
Choose lifts in D₀ of the images of the specified polynomial generators of A, using
hinc₀. Evaluation defines a k-algebra homomorphism from the polynomial presentation to
D₀. Its composite with g₀ equals the given map on constants and generators. Injectivity
of g₀ implies that its kernel contains the presentation kernel, so the surjective
presentation map gives a unique k-algebra map A to D₀. Its composite is the required
A-map into the quotient. Replace D₀ by its ULift to universe max u v w; transport its
ring, local and Artinian structures, the two algebra structures, the scalar tower,
and the maps. This merely changes the carrier, and all identities persist. -/
theorem exists_popescu_coefficient_start
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (n : ℕ) (hn : 0 < n)
    (r : ℕ) (f : MvPolynomial (Fin r) k →ₐ[k] A) (hf : Function.Surjective f)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (D₀ : Type (max u w)) [CommRing D₀] [IsLocalRing D₀] [IsArtinianRing D₀]
    [Algebra (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^ n) D₀]
    (g₀ : D₀ →+* Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        n)
    [IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
          n) D₀)]
    [IsLocalHom g₀]
    (hsmooth₀ : EssentiallySmooth
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            n) D₀)
    (hgflat₀ : g₀.Flat)
    (hfactor₀ : (g₀.comp (algebraMap
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            n) D₀)).comp
      (Ideal.Quotient.mk (((q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            n)) =
      (Ideal.Quotient.mk ((q.asIdeal.map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
          n)).comp ψ₀)
    (hinc₀ : ∀ i : Fin r, Ideal.Quotient.mk
      ((q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        n)
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i)))) ∈
        Set.range g₀)
 :
    let P := MvPolynomial (Fin m₀) k
    let p₀ := q.asIdeal.comap φ₀.toRingHom
    let B := P ⧸ p₀ ^ n
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ n
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : IsLocalRing D)
      (_ : IsArtinianRing D) (_ : Algebra k D) (_ : Algebra B D)
      (_ : IsScalarTower k B D),
      EssentiallySmooth B D ∧
      ∃ (fA : A →ₐ[k] D) (g : D →+* L ⧸ K),
        IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
        (∀ z : P, g (algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) z)) =
          Ideal.Quotient.mk K (algebraMap Λ L (φ₀ z))) ∧
        (∀ x, g (fA x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) := by
  classical
  let P := MvPolynomial (Fin m₀) k
  let p₀ := q.asIdeal.comap φ₀.toRingHom
  let R₀ := Localization.AtPrime p₀
  let I := p₀.map (algebraMap P R₀)
  let Q₀ := R₀ ⧸ I ^ n
  let Q₁ := R₀ ⧸ (p₀ ^ n).map (algebraMap P R₀)
  let B := P ⧸ p₀ ^ n
  let L := Localization.AtPrime q.asIdeal
  let J := (q.asIdeal.map (algebraMap Λ L)) ^ n
  let K := IsLocalRing.maximalIdeal L ^ n
  let S := L ⧸ K
  let eQ : Q₁ ≃ₐ[k] Q₀ := Ideal.quotientEquivAlgOfEq k (Ideal.map_pow _ _ _)
  let eS : (L ⧸ J) ≃ₐ[k] S := Ideal.quotientEquivAlgOfEq k
    (by dsimp [J, K]; rw [Localization.AtPrime.map_eq_maximalIdeal])
  let hBD : B →+* D₀ := (algebraMap Q₀ D₀).comp
    (eQ.toRingHom.comp (algebraMap B Q₁))
  let : Algebra B D₀ := hBD.toAlgebra
  let : Algebra k D₀ := (hBD.comp (algebraMap k B)).toAlgebra
  have : IsScalarTower k B D₀ := IsScalarTower.of_algebraMap_eq' rfl
  let g : D₀ →+* S := eS.toRingHom.comp g₀
  have hproper : K ≠ ⊤ := ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal L).ne_top (Ideal.pow_le_self hn.ne')
  have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing S := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (L ⧸ J) := eS.symm.toRingEquiv.isLocalRing
  have : IsLocalHom g := by dsimp [g]; infer_instance
  have hgflat : g.Flat := hgflat₀.comp (RingHom.Flat.of_bijective eS.bijective)
  have hQ : EssentiallySmooth B Q₁ := by
    have : Smooth B B := {}
    refine ⟨B, inferInstance, inferInstance, inferInstance,
      Algebra.algebraMapSubmonoid B p₀.primeCompl, ?_⟩
    exact ⟨IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B p₀.primeCompl)
      Q₁ (Localization (Algebra.algebraMapSubmonoid B p₀.primeCompl))⟩
  have hQ₀ : letI : Algebra B Q₀ :=
      (eQ.toRingHom.comp (algebraMap B Q₁)).toAlgebra; EssentiallySmooth B Q₀ := by
    let : Algebra B Q₀ := (eQ.toRingHom.comp (algebraMap B Q₁)).toAlgebra
    obtain ⟨T, hT, hBT, hTsmooth, U, ⟨e⟩⟩ := hQ
    let : CommRing T := hT
    let : Algebra B T := hBT
    let eQB : Q₀ ≃ₐ[B] Q₁ := AlgEquiv.ofRingEquiv (f := eQ.symm.toRingEquiv)
      (fun b ↦ by change eQ.symm (eQ (algebraMap B Q₁ b)) = _; simp)
    exact ⟨T, hT, hBT, hTsmooth, U, ⟨eQB.trans e⟩⟩
  have hQ₀D : letI : Algebra Q₀ D₀ := (algebraMap Q₀ D₀).toAlgebra;
      EssentiallySmooth Q₀ D₀ := by
    have heq : (algebraMap Q₀ D₀).toAlgebra = (inferInstance : Algebra Q₀ D₀) :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    rw [heq]
    exact hsmooth₀
  have hsmooth : EssentiallySmooth B D₀ :=
    RingHom.essentiallySmooth_comp
      (eQ.toRingHom.comp (algebraMap B Q₁)) (algebraMap Q₀ D₀) hQ₀ hQ₀D
  have hB (z : P) :
      g (algebraMap B D₀ (Ideal.Quotient.mk (p₀ ^ n) z)) =
        Ideal.Quotient.mk K (algebraMap Λ L (φ₀ z)) := by
    change eS (g₀ (algebraMap Q₀ D₀
      (eQ (Ideal.Quotient.mk ((p₀ ^ n).map (algebraMap P R₀))
        (algebraMap P R₀ z))))) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    have hfact := RingHom.congr_fun hfactor₀ (algebraMap P R₀ z)
    simp only [RingHom.comp_apply] at hfact
    rw [hfact]
    have hψ := RingHom.congr_fun hψ₀ z
    simp only [RingHom.comp_apply] at hψ
    change ψ₀ (algebraMap P R₀ z) = algebraMap Λ L (φ₀ z) at hψ
    rw [hψ, Ideal.quotientEquivAlgOfEq_mk]
  have hgk (x : k) : g (algebraMap k D₀ x) = algebraMap k S x := by
    rw [IsScalarTower.algebraMap_apply k B D₀]
    change g (algebraMap B D₀ (Ideal.Quotient.mk (p₀ ^ n) (MvPolynomial.C x))) = _
    rw [hB]
    change Ideal.Quotient.mk K (algebraMap Λ L (φ₀ (algebraMap k P x))) = _
    rw [φ₀.commutes]
    rfl
  let ga : D₀ →ₐ[k] S := { g with commutes' := hgk }
  let : Algebra D₀ S := g.toAlgebra
  have : Module.Flat D₀ S := hgflat
  have : IsLocalHom (algebraMap D₀ S) := inferInstanceAs (IsLocalHom g)
  have : Module.FaithfullyFlat D₀ S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective g := FaithfulSMul.algebraMap_injective D₀ S
  have hinc (i : Fin r) : Ideal.Quotient.mk K
      (algebraMap Λ L (α (f (MvPolynomial.X i)))) ∈ Set.range g := by
    obtain ⟨x, hx⟩ := hinc₀ i
    refine ⟨x, ?_⟩
    change eS (g₀ x) = _
    rw [hx, Ideal.quotientEquivAlgOfEq_mk]
  choose x hx using hinc
  let fP : MvPolynomial (Fin r) k →ₐ[k] D₀ := MvPolynomial.aeval x
  let faS : A →ₐ[k] S := (IsScalarTower.toAlgHom k Λ L).comp α |>
    (Ideal.Quotient.mkₐ k K).comp
  have hcomp : ga.comp fP = faS.comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    change g (fP (MvPolynomial.X i)) =
      Ideal.Quotient.mk K (algebraMap Λ L (α (f (MvPolynomial.X i))))
    dsimp only [fP]
    rw [MvPolynomial.aeval_X]
    exact hx i
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker fP.toRingHom := by
    intro z hz
    apply hinj
    have heq := AlgHom.congr_fun hcomp z
    change ga (fP z) = faS (f z) at heq
    have hz0 : f z = 0 := RingHom.mem_ker.mp hz
    rw [hz0, map_zero] at heq
    exact heq.trans (map_zero g).symm
  let fA : A →ₐ[k] D₀ := AlgHom.liftOfSurjective f hf fP hker
  have hA (a : A) : g (fA a) = Ideal.Quotient.mk K (algebraMap Λ L (α a)) := by
    obtain ⟨z, rfl⟩ := hf a
    rw [AlgHom.liftOfSurjective_apply]
    exact AlgHom.congr_fun hcomp z
  let D := ULift.{max u v w} D₀
  let e : D ≃ₐ[B] D₀ := ULift.algEquiv
  have : IsLocalRing D := e.symm.toRingEquiv.isLocalRing
  have : IsArtinianRing D := e.symm.toRingEquiv.isArtinianRing
  have : IsScalarTower k B D := inferInstance
  have hsmoothD : EssentiallySmooth B D := by
    obtain ⟨T, hT, hBT, hTsmooth, U, ⟨eT⟩⟩ := hsmooth
    let : CommRing T := hT
    let : Algebra B T := hBT
    let T' := ULift.{max u v w} T
    let eU : T' ≃ₐ[B] T := ULift.algEquiv
    have : Smooth B T' := Smooth.of_equiv eU.symm
    let U' := U.comap eU.toRingEquiv.toMonoidHom
    have hU : U'.map eU.toRingEquiv.toMonoidHom = U :=
      Submonoid.map_comap_eq_of_surjective eU.surjective U
    let er : Localization U' ≃+* Localization U :=
      IsLocalization.ringEquivOfRingEquiv (Localization U') (Localization U)
        eU.toRingEquiv hU
    let eL : Localization U' ≃ₐ[B] Localization U :=
      AlgEquiv.ofRingEquiv (f := er) (fun b ↦ by
        rw [IsScalarTower.algebraMap_apply B T' (Localization U')]
        change IsLocalization.ringEquivOfRingEquiv (Localization U') (Localization U)
          eU.toRingEquiv hU (algebraMap T' (Localization U') (algebraMap B T' b)) = _
        rw [IsLocalization.ringEquivOfRingEquiv_eq]
        change algebraMap T (Localization U) (eU (algebraMap B T' b)) = _
        rw [eU.commutes, ← IsScalarTower.algebraMap_apply B T (Localization U)])
    exact ⟨T', inferInstance, inferInstance, inferInstance, U',
      ⟨(e.trans eT).trans eL.symm⟩⟩
  let gD : D →+* S := g.comp e.toRingHom
  have : IsLocalHom gD := by dsimp [gD]; infer_instance
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hsmoothD, (e.restrictScalars k).symm.toAlgHom.comp fA, gD,
    inferInstance, inferInstance, (RingHom.Flat.of_bijective e.bijective).comp hgflat,
    ?_, ?_⟩
  · intro z
    change g (e (algebraMap B D (Ideal.Quotient.mk (p₀ ^ n) z))) = _
    rw [e.commutes]
    exact hB z
  · intro a
    change g (e (e.symm (fA a))) = _
    rw [e.apply_symm_apply]
    exact hA a

end Algebra
