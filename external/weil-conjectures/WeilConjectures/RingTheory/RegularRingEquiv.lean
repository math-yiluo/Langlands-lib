/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink

/-!
# Regular ring maps and isomorphisms

Source: Stacks Project, More on Algebra, Definition 07BZ, and Algebra, Lemma 0381.
(blueprint: lem-weil-pbc-regular-ring-map-ring-equiv).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

private def semilinearEquiv
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r)) :
    LinearEquiv (e : R →+* S) (σ' := (e.symm : S →+* R)) A B :=
  { f.toAddEquiv with
    map_smul' := fun r x ↦ by
      simp only [Algebra.smul_def]
      exact (f.map_mul _ _).trans (congrArg (fun t ↦ t * f x) (h r)) }

private def tensorRingEquiv
    {R S A B C D : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra S C] [Algebra S D]
    (e : R ≃+* S) (f : A ≃+* C) (g : B ≃+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) :
    TensorProduct R A B ≃+* TensorProduct S C D := by
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.of_ringEquiv_symm e
  let F := semilinearEquiv e f hf
  let G := semilinearEquiv e g hg
  let E := TensorProduct.congr (σ₂₁ := (e.symm : S →+* R)) F G
  refine { E.toAddEquiv with map_mul' := ?_ }
  intro x y
  change E (x * y) = E x * E y
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [E, TensorProduct.congr_tmul]
      change f (a * c) ⊗ₜ[S] g (b * d) = (f a ⊗ₜ[S] g b) * (f c ⊗ₜ[S] g d)
      simp only [map_mul, Algebra.TensorProduct.tmul_mul_tmul]

private theorem geometricRegular_of_equiv
    {k : Type u₁} {l : Type u₂} {A : Type v₁} {B : Type v₂}
    [Field k] [Field l] [CommRing A] [CommRing B] [Algebra k A] [Algebra l B]
    (e : k ≃+* l) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap k A r) = algebraMap l B (e r))
    (hA : Algebra.IsGeometricallyRegular k A) : Algebra.IsGeometricallyRegular l B := by
  let : IsNoetherianRing A := hA.1
  refine ⟨isNoetherianRing_of_ringEquiv A f, ?_⟩
  intro L _ _ _ _
  let : Algebra k l := e.toRingHom.toAlgebra
  let : Algebra k L := ((algebraMap l L).comp e.toRingHom).toAlgebra
  let : IsScalarTower k l L := IsScalarTower.of_algebraMap_eq' rfl
  let E : k ≃ₐ[k] l := { e with commutes' := fun _ ↦ rfl }
  let : Module.Finite k l := e.finite
  let : Module.Finite k L := Module.Finite.trans l L
  let : IsPurelyInseparable k l := E.isPurelyInseparable
  let : IsPurelyInseparable k L := IsPurelyInseparable.trans k l L
  let : Small.{max u₁ v₁} L := Module.Finite.small k L
  let C := Shrink.{max u₁ v₁} L
  let : IsPurelyInseparable k C := (Shrink.algEquiv k L).symm.isPurelyInseparable
  let : IsRegularRing (TensorProduct k C A) := hA.2 C
  let T := tensorRingEquiv e (Shrink.algEquiv k L).toRingEquiv f
    (fun r ↦ (Shrink.algEquiv k L).commutes r) h
  exact IsRegularRing.of_ringEquiv T

/-- A commuting square with horizontal ring equivalences transports regularity.
Source: Stacks Project, More on Algebra, Definition 07BZ; Algebra, Lemma 0381.
(blueprint: lem-weil-pbc-regular-ring-map-ring-equiv).

Proof: Write g as b composed with f composed with a inverse. Equivalences are flat,
so flatness follows by composition. For a prime q of R₂ take p = a inverse(q).
The induced local-ring equivalence identifies their maximal ideals and hence their
residue fields. Tensor the residue-field equivalence and b to identify the fibres,
compatibly with the residue-field actions. Noetherianity transports through the
fibre equivalence. For a finite purely inseparable extension L of the second residue
field, pull its scalar action back through the residue-field equivalence. It remains
finite and purely inseparable: transport a finite basis and use the p-power criterion
for purely inseparable extensions (in characteristic zero the extension is trivial).
Represent L in the universe used by the first geometric-regularity criterion by
shrinking its finite-dimensional underlying vector space. Transport the field and
algebra structures along that equivalence; finiteness and pure inseparability are
preserved. The tensor-product equivalence identifies the base-changed fibre with the
one covered by f's geometric regularity. Regularity of rings transports under this
equivalence. Thus each fibre of g is geometrically regular, proving the claim.
No nonzero-ring hypothesis is needed: rings with no primes have a vacuous fibre clause. -/
theorem RingHom.IsRegular.of_ringEquiv
    {R₁ : Type u₁} {R₂ : Type u₂} {S₁ : Type v₁} {S₂ : Type v₂}
    [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
    (f : R₁ →+* S₁) (g : R₂ →+* S₂) (a : R₁ ≃+* R₂) (b : S₁ ≃+* S₂)
    (h : b.toRingHom.comp f = g.comp a.toRingHom) (hf : f.IsRegular) :
    g.IsRegular := by
  have hg : g = (b.toRingHom.comp f).comp a.symm.toRingHom := by
    rw [h]
    ext x
    simp
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (RingHom.Flat.of_bijective a.symm.bijective).comp
      (hf.1.comp (RingHom.Flat.of_bijective b.bijective))
  · let : Algebra R₁ S₁ := f.toAlgebra
    let : Algebra R₂ S₂ := g.toAlgebra
    intro q hq
    let p : Ideal R₁ := q.comap a.toRingHom
    let : p.IsPrime := Ideal.comap_isPrime a.toRingHom q
    let E : p.ResidueField ≃+* q.ResidueField :=
      Ideal.residueFieldRingEquiv p q a rfl
    have hE (r : R₁) : E (algebraMap R₁ p.ResidueField r) =
        algebraMap R₂ q.ResidueField (a r) :=
      Ideal.ResidueField.map_algebraMap p q a.toRingHom rfl r
    have hb (r : R₁) : b (algebraMap R₁ S₁ r) = algebraMap R₂ S₂ (a r) :=
      DFunLike.congr_fun h r
    let T := tensorRingEquiv a E b hE hb
    apply geometricRegular_of_equiv E T
    · intro r
      change T (r ⊗ₜ[R₁] (1 : S₁)) = E r ⊗ₜ[R₂] (1 : S₂)
      change E r ⊗ₜ[R₂] b 1 = _
      rw [map_one]
    · exact hf.2 p
