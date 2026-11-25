/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint
public import WeilConjectures.Mathlib.RingTheory.Etale.ResidueField
public import WeilConjectures.Mathlib.RingTheory.Etale.ResidueFieldBaseChange

/-!
# Property (C) for finite universal homeomorphisms, at the ring level

Let `A → B` be a finite ring map inducing a universal homeomorphism on spectra, and let `C` be
an étale `B`-algebra with a prime `q`. We show that there is an étale `A`-algebra `A'` and a
`B`-algebra map `C → A' ⊗[A] B` whose induced map on spectra hits `q`. This is the ring-level
content of [Stacks 04DW] ("property (C)").

The proof proceeds in three steps.
1. Trivialise the residue field extension `κ(q)/κ(𝔮)` (`𝔮 = q ∩ B`) after an étale base change
   of `A`: the separable closure `Kₛ` of `κ(p)` (`p = q ∩ A`) in `κ(q)` is finite separable
   over `κ(p)` and is realised by an étale `A`-algebra
   (`Algebra.exists_etale_residueField_equiv`); after base change to it, `κ(q)` becomes
   purely inseparable and separable, hence trivial, over the residue field of `B`.
2. Apply Mathlib's étale local structure theorem for quasi-finite algebras
   (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`) to split off a factor of the
   base change of `C` which is finite over the new base and has a unique prime over the
   relevant prime, with trivial residue field extension.
3. This factor is finite étale of rank one at the relevant prime over the base change of `B`,
   hence, after shrinking the étale neighbourhood, isomorphic to it.
-/

@[expose] public section

universe u

open TensorProduct

section Helpers

/-- Elements of a residue field lie in a subfield as soon as the images of the ring do. -/
lemma Ideal.ResidueField.mem_of_forall_algebraMap_mem {R L : Type*} [CommRing R] [Field L]
    (I : Ideal R) [I.IsPrime] (ρ : I.ResidueField →+* L) (F : Subfield L)
    (h : ∀ r : R, ρ (algebraMap R I.ResidueField r) ∈ F) (x : I.ResidueField) : ρ x ∈ F := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (R ⧸ I)) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective s.1
  have key : ∀ b : R,
      ρ (algebraMap (R ⧸ I) I.ResidueField (Ideal.Quotient.mk I b)) ∈ F := by
    intro b
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact h b
  change ρ (IsLocalization.mk' I.ResidueField (Ideal.Quotient.mk I a) s) ∈ F
  rw [IsFractionRing.mk'_eq_div, map_div₀]
  refine div_mem (key a) ?_
  rw [← hs']
  exact key s'

end Helpers

namespace Algebra.Etale

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- the proof assembles many algebra structures on residue fields
/-- **Trivialising the residue field extension.** Let `C` be an étale `B`-algebra and `q` a prime
of `C` such that the residue field extension of `B/A` at `q ∩ B` is purely inseparable. Then
there is an étale `A`-algebra `A'` and a `B`-algebra map `θ : (A' ⊗[A] B) ⊗[B] C → κ(q)`
extending `C → κ(q)`, whose kernel `q'` is a prime of `(A' ⊗[A] B) ⊗[B] C` lying over `q` with
trivial residue field extension over `A' ⊗[A] B`. -/
theorem exists_etale_bijective_residueFieldMap' [Algebra.Etale B C] (q : Ideal C) [q.IsPrime]
    (hpi : (Ideal.ResidueField.map ((q.under B).under A) (q.under B) (algebraMap A B)
      rfl).IsPurelyInseparable) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (θ : (A' ⊗[A] B) ⊗[B] C →ₐ[B] q.ResidueField),
      (∀ c, θ (Algebra.TensorProduct.includeRight c) = algebraMap C _ c) ∧
      Function.Bijective (Ideal.ResidueField.map ((RingHom.ker θ.toRingHom).under (A' ⊗[A] B))
        (RingHom.ker θ.toRingHom) (algebraMap (A' ⊗[A] B) _) rfl) := by
  classical
  set 𝔮 : Ideal B := q.under B with h𝔮
  set p : Ideal A := 𝔮.under A with hp
  have : q.LiesOver p := ⟨Ideal.under_under q⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Localization.AtPrime.algebraOfLiesOver 𝔮 q
  let := Localization.AtPrime.algebraOfLiesOver p 𝔮
  let K := p.ResidueField
  let M := 𝔮.ResidueField
  let L := q.ResidueField
  have hKM : IsPurelyInseparable K M := RingHom.isPurelyInseparable_algebraMap_iff.mp hpi
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.trans K M L
  let Ks := separableClosure K L
  -- `Kₛ` is finite over `K`.
  have hfin : FiniteDimensional K Ks := by
    have h₁ := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K Ks L
    have h₂ := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K M L
    rw [IsPurelyInseparable.finSepDegree_eq_one Ks L, mul_one,
      Field.finSepDegree_eq_finrank_of_isSeparable K Ks] at h₁
    rw [IsPurelyInseparable.finSepDegree_eq_one K M, one_mul,
      Field.finSepDegree_eq_finrank_of_isSeparable M L] at h₂
    have : 0 < Module.finrank K Ks := by
      rw [h₁, ← h₂]
      exact Module.finrank_pos
    exact Module.finite_of_finrank_pos this
  obtain ⟨A', _, _, _, P', _, hP', e, he⟩ := Algebra.exists_etale_residueField_equiv p Ks
  refine ⟨A', inferInstance, inferInstance, inferInstance, ?_⟩
  -- The map `A' → L` through `κ(P') ≃ Kₛ ⊆ L`.
  let f₁ : A' →ₐ[A] L :=
    { toRingHom := Ks.val.toRingHom.comp (e.toRingHom.comp (algebraMap A' P'.ResidueField))
      commutes' := fun a ↦ by
        change Ks.val (e (algebraMap A' P'.ResidueField (algebraMap A A' a))) = algebraMap A L a
        rw [← Ideal.ResidueField.map_algebraMap p P' (algebraMap A A') hP', he]
        exact (IsScalarTower.algebraMap_apply A K L a).symm }
  let F₀ : A' ⊗[A] B →ₐ[A] L :=
    Algebra.TensorProduct.lift f₁ (IsScalarTower.toAlgHom A B L) (fun _ _ ↦ Commute.all _ _)
  let F : A' ⊗[A] B →ₐ[B] L :=
    { toRingHom := F₀.toRingHom
      commutes' := fun b ↦ by
        change F₀ (1 ⊗ₜ b) = algebraMap B L b
        simp [F₀] }
  let θ : (A' ⊗[A] B) ⊗[B] C →ₐ[B] L :=
    Algebra.TensorProduct.lift F (IsScalarTower.toAlgHom B C L) (fun _ _ ↦ Commute.all _ _)
  have hθ_right : ∀ c : C, θ (Algebra.TensorProduct.includeRight c) = algebraMap C L c := by
    intro c
    simp [θ]
  have hθ_left : ∀ a' : A', θ (Algebra.TensorProduct.includeLeftRingHom
      (Algebra.TensorProduct.includeLeftRingHom a')) = Ks.val (e (algebraMap A' _ a')) := by
    intro a'
    simp [θ, F, F₀, f₁]
  have hθ_B : ∀ b : B, θ (algebraMap B _ b) = algebraMap B L b := θ.commutes
  let q' : Ideal ((A' ⊗[A] B) ⊗[B] C) := RingHom.ker θ.toRingHom
  have : q'.IsPrime := RingHom.ker_isPrime _
  have hq' : q = q'.comap Algebra.TensorProduct.includeRight.toRingHom := by
    ext c
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change c ∈ q ↔ θ (Algebra.TensorProduct.includeRight c) = 0
    rw [hθ_right, Ideal.algebraMap_residueField_eq_zero]
  refine ⟨θ, hθ_right, ?_⟩
  change Function.Bijective (Ideal.ResidueField.map (q'.under (A' ⊗[A] B)) q'
    (algebraMap (A' ⊗[A] B) _) rfl)
  set 𝔮' := q'.under (A' ⊗[A] B) with h𝔮'
  have : 𝔮'.IsPrime := Ideal.IsPrime.under _ _
  set ψ := Ideal.ResidueField.map 𝔮' q' (algebraMap (A' ⊗[A] B) _) rfl with hψ
  refine ⟨ψ.injective, fun y ↦ ?_⟩
  -- The embedding `κ(q') → L` induced by `θ`.
  let ι₁ : q'.ResidueField →+* L := Ideal.ResidueField.lift q' θ.toRingHom le_rfl (fun x hx ↦ by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr hx)
  have hι₁ : ∀ x, ι₁ (algebraMap _ _ x) = θ x := fun x ↦
    Ideal.ResidueField.lift_algebraMap _ _ _ _ x
  let ι₀ : 𝔮'.ResidueField →+* L := ι₁.comp ψ
  have hι₀ : ∀ x : A' ⊗[A] B, ι₀ (algebraMap _ _ x) = θ (algebraMap _ _ x) := fun x ↦ by
    simp [ι₀, ψ, Ideal.ResidueField.map_algebraMap, hι₁]
  -- The image of `κ(𝔮')` in `L` contains `M`.
  have h𝔮𝔮' : 𝔮 = 𝔮'.comap (algebraMap B (A' ⊗[A] B)) := by
    rw [h𝔮', Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, h𝔮, hq', Ideal.under,
      Ideal.comap_comap, IsScalarTower.algebraMap_eq B C ((A' ⊗[A] B) ⊗[B] C)]
    rfl
  have hcomp : ι₀.comp (Ideal.ResidueField.map 𝔮 𝔮' (algebraMap B _) h𝔮𝔮') = algebraMap M L := by
    refine Ideal.ResidueField.ringHom_ext ?_
    ext b
    simp only [RingHom.coe_comp, Function.comp_apply, Ideal.ResidueField.map_algebraMap, hι₀]
    rw [← IsScalarTower.algebraMap_apply B (A' ⊗[A] B), ← IsScalarTower.algebraMap_apply B M L,
      hθ_B]
  have hM : ∀ m : M, algebraMap M L m ∈ ι₀.fieldRange := fun m ↦
    ⟨Ideal.ResidueField.map 𝔮 𝔮' (algebraMap B _) h𝔮𝔮' m, RingHom.congr_fun hcomp m⟩
  let N : IntermediateField M L := ι₀.fieldRange.toIntermediateField hM
  -- The image of `κ(𝔮')` in `L` contains `Kₛ`.
  have hKs : ∀ x : Ks, (x : L) ∈ ι₀.fieldRange := by
    intro x
    obtain ⟨z, rfl⟩ := e.surjective x
    refine Ideal.ResidueField.mem_of_forall_algebraMap_mem P' (Ks.val.toRingHom.comp e.toRingHom)
      ι₀.fieldRange (fun a' ↦ ?_) z
    refine ⟨algebraMap (A' ⊗[A] B) 𝔮'.ResidueField
      (Algebra.TensorProduct.includeLeftRingHom a'), ?_⟩
    rw [hι₀]
    exact hθ_left a'
  have hsep : Algebra.IsSeparable N L := inferInstance
  have hpi' : IsPurelyInseparable N L := by
    have hle : Ks.toSubfield ≤ N.toSubfield := fun x hx ↦ hKs ⟨x, hx⟩
    let : Algebra Ks N := (Subfield.inclusion hle).toAlgebra
    have : IsScalarTower Ks N L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    exact IsPurelyInseparable.tower_top Ks N L
  have hbij := IsPurelyInseparable.bijective_algebraMap_of_isSeparable N L
  obtain ⟨z, hz⟩ := hbij.2 (ι₁ y)
  obtain ⟨w, hw⟩ := z.2
  refine ⟨w, ι₁.injective ?_⟩
  rw [← hz]
  exact hw

/-- **Trivialising the residue field extension.** Let `C` be an étale `B`-algebra and `q` a prime
of `C` such that the residue field extension of `B/A` at `q ∩ B` is purely inseparable. Then
there is an étale `A`-algebra `A'` and a prime `q'` of `(A' ⊗[A] B) ⊗[B] C` lying over `q` whose
residue field extension over `A' ⊗[A] B` is trivial. -/
theorem exists_etale_bijective_residueFieldMap [Algebra.Etale B C] (q : Ideal C) [q.IsPrime]
    (hpi : (Ideal.ResidueField.map ((q.under B).under A) (q.under B) (algebraMap A B)
      rfl).IsPurelyInseparable) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (q' : Ideal ((A' ⊗[A] B) ⊗[B] C)) (_ : q'.IsPrime)
      (_ : q = q'.comap Algebra.TensorProduct.includeRight.toRingHom),
      Function.Bijective (Ideal.ResidueField.map (q'.under (A' ⊗[A] B)) q'
        (algebraMap (A' ⊗[A] B) _) rfl) := by
  obtain ⟨A', _, _, _, θ, hθ, hres⟩ := exists_etale_bijective_residueFieldMap' (A := A) q hpi
  refine ⟨A', inferInstance, inferInstance, inferInstance, RingHom.ker θ.toRingHom,
    RingHom.ker_isPrime _, ?_, hres⟩
  ext c
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change c ∈ q ↔ θ (Algebra.TensorProduct.includeRight c) = 0
  rw [hθ, Ideal.algebraMap_residueField_eq_zero]

section RankOne

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

-- instance search on fibres of étale algebras is expensive
/-- **Rank one.** Let `C` be a finite étale `B`-algebra and `q` a prime of `C` which is the only
prime lying over `𝔮 = q ∩ B` and has trivial residue field extension. Then `C` has rank one
at `𝔮`. -/
theorem rankAtStalk_eq_one_of_forall_under_eq [Module.Finite B C] [Algebra.Etale B C]
    (q : Ideal C) [q.IsPrime]
    (huniq : ∀ (Q : Ideal C) [Q.IsPrime], Q.under B = q.under B → Q = q)
    (hres : Function.Bijective (Ideal.ResidueField.map (q.under B) q (algebraMap B C) rfl)) :
    Module.rankAtStalk (R := B) C ⟨q.under B, inferInstance⟩ = 1 := by
  classical
  set 𝔮 : Ideal B := q.under B with h𝔮
  have : q.LiesOver 𝔮 := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver 𝔮 q
  rw [← Ideal.finrank_fiber_eq_rankAtStalk]
  let F := 𝔮.Fiber C
  -- The canonical map from the fibre to `κ(q)`.
  let lam : F →ₐ[𝔮.ResidueField] q.ResidueField :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom B C _)
      (fun _ _ ↦ Commute.all _ _)
  have hsurj : Function.Surjective lam := Ideal.Fiber.lift_residueField_surjective 𝔮 q
  -- Its kernel is the unique prime of the fibre.
  let e := PrimeSpectrum.preimageEquivFiber B C ⟨𝔮, inferInstance⟩
  let Q₀ : PrimeSpectrum F := e ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext rfl⟩
  have hQ₀ : Q₀.asIdeal = RingHom.ker lam.toRingHom := by
    change RingHom.ker _ = _
    congr 1
  have huniqF : ∀ Q : PrimeSpectrum F, Q = Q₀ := by
    intro Q
    apply e.symm.injective
    apply Subtype.ext
    apply PrimeSpectrum.ext
    change Q.asIdeal.comap _ = _
    rw [e.symm_apply_apply]
    have : Q.asIdeal.LiesOver 𝔮 := inferInstance
    exact huniq _ ((Ideal.under_under (A := B) (B := C) Q.asIdeal).trans
      (Ideal.LiesOver.over (P := Q.asIdeal) (p := 𝔮)).symm)
  have hinj : Function.Injective lam := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hred : IsReduced F := Algebra.FormallyUnramified.isReduced_of_field 𝔮.ResidueField F
    refine IsNilpotent.eq_zero (x := x) ?_
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    rintro Q hQ
    have : Q = Q₀.asIdeal := congr($(huniqF ⟨Q, hQ⟩).asIdeal)
    rw [this, hQ₀]
    exact hx
  have hbij : Function.Bijective (algebraMap 𝔮.ResidueField q.ResidueField) := hres
  let e₁ : F ≃ₐ[𝔮.ResidueField] q.ResidueField := AlgEquiv.ofBijective lam ⟨hinj, hsurj⟩
  let e₂ : 𝔮.ResidueField ≃ₐ[𝔮.ResidueField] q.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  rw [e₁.toLinearEquiv.finrank_eq, ← e₂.toLinearEquiv.finrank_eq, Module.finrank_self]

end RankOne

section Main

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C]

-- long proof with many local algebra instances
/-- **Property (C) for a prime with trivial residue field extension.** Let `A → B` be finite,
`C` an étale `B`-algebra and `q` a prime of `C` whose residue field extension over `B` is
trivial and whose restriction to `B` is the only prime of `B` over `p = q ∩ A`. Then there is
an étale `A`-algebra `A'` and a `B`-algebra map `C → A' ⊗[A] B` whose image on spectra
contains `q`; more precisely there is a prime `P'` of `A'` over `p` with trivial residue field
extension and a prime `q'` of `A' ⊗[A] B` over `P'` which is mapped to `q`. -/
theorem exists_etale_algHom_comap_eq_of_bijective_residueFieldMap' [Module.Finite A B]
    [Algebra.Etale B C] (q : Ideal C) [q.IsPrime]
    (huniqB : ∀ (Q : Ideal B) [Q.IsPrime], Q.under A = q.under A → Q = q.under B)
    (hres : Function.Bijective (Ideal.ResidueField.map (q.under B) q (algebraMap B C) rfl)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (h : C →ₐ[A] A' ⊗[A] B), h.comp (IsScalarTower.toAlgHom A B C) =
        Algebra.TensorProduct.includeRight ∧
      ∃ (P' : Ideal A') (_ : P'.IsPrime) (_ : P'.LiesOver (q.under A)),
        Function.Bijective (Ideal.ResidueField.map (q.under A) P' (algebraMap A A')
          (P'.over_def (q.under A))) ∧
        ∃ (q' : Ideal (A' ⊗[A] B)) (_ : q'.IsPrime) (_ : q'.LiesOver P'),
          q = q'.comap h.toRingHom := by
  classical
  set p : Ideal A := q.under A with hp
  have : q.LiesOver p := ⟨rfl⟩
  have : Algebra.FiniteType A C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : Algebra.QuasiFiniteAt A q := Algebra.QuasiFinite.trans A B (Localization.AtPrime q)
  obtain ⟨A₂, _, _, _, P₂, _, _, e, he, P', _, _, hP'q, heP', hres₂, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  -- Transport the data to `T := (A₂ ⊗[A] B) ⊗[B] C`.
  let B₂ := A₂ ⊗[A] B
  let T := B₂ ⊗[B] C
  let ψ : T ≃ₐ[A₂] A₂ ⊗[A] C := Algebra.IsPushout.cancelBaseChangeAlg A A₂ B B₂ C
  have hψ_right : ∀ c : C, ψ (Algebra.TensorProduct.includeRight c) =
      Algebra.TensorProduct.includeRight c := fun c ↦
    Algebra.IsPushout.cancelBaseChangeAlg_tmul A A₂ B B₂ C c
  have hψ_comp : ψ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := RingHom.ext hψ_right
  have hψ_alg : ψ.toRingHom.comp (algebraMap A₂ T) = algebraMap A₂ (A₂ ⊗[A] C) :=
    RingHom.ext ψ.commutes
  have hψ_alg' : ψ.symm.toRingHom.comp (algebraMap A₂ (A₂ ⊗[A] C)) = algebraMap A₂ T :=
    RingHom.ext ψ.symm.commutes
  let e' : T := ψ.symm e
  have he' : IsIdempotentElem e' := he.map ψ.symm.toRingHom
  let q₂ : Ideal T := P'.comap ψ.toRingHom
  have : q₂.IsPrime := Ideal.IsPrime.comap _
  have hq₂C : q₂.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
    rw [Ideal.comap_comap, hψ_comp, hP'q]
  have hq₂P₂ : q₂.LiesOver P₂ := ⟨by
    rw [Ideal.LiesOver.over (P := P') (p := P₂), Ideal.under, Ideal.under, Ideal.comap_comap,
      hψ_alg]⟩
  have he'q₂ : e' ∉ q₂ := by
    change ψ (ψ.symm e) ∉ P'
    rwa [ψ.apply_symm_apply]
  have huniq' : ∀ (Q : Ideal T), Q.IsPrime → Q.LiesOver P₂ → e' ∉ Q → Q = q₂ := by
    intro Q hQ hQP hQe
    have h₁ : (Q.comap ψ.symm.toRingHom).LiesOver P₂ := ⟨by
      rw [Ideal.LiesOver.over (P := Q) (p := P₂), Ideal.under, Ideal.under, Ideal.comap_comap,
        hψ_alg']⟩
    have h₂ : e ∉ Q.comap ψ.symm.toRingHom := hQe
    have := huniq _ (Ideal.IsPrime.comap _) h₁ h₂
    change Q = P'.comap ψ.toRingHom
    rw [← this, Ideal.comap_comap]
    conv_lhs => rw [← Ideal.comap_id Q]
    congr 1
    exact RingHom.ext fun x ↦ (ψ.symm_apply_apply x).symm
  have hfin' : Module.Finite A₂ (Localization.Away e') :=
    Module.Finite.equiv (IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers e)
      (T := Submonoid.powers e') (Localization.Away e) (Localization.Away e') ψ.symm
      (by rw [Submonoid.map_powers])).toLinearEquiv
  -- The finite étale `B₂`-algebra `C₂`.
  let C₂ := Localization.Away e'
  have : Module.Finite B₂ C₂ := Module.Finite.of_restrictScalars_finite A₂ B₂ C₂
  have : Algebra.Etale B₂ C₂ := Algebra.Etale.comp B₂ T C₂
  have hdisj : Disjoint (Submonoid.powers e' : Set T) q₂ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime e').mpr he'q₂
  let q₃ : Ideal C₂ := q₂.map (algebraMap T C₂)
  have : q₃.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers e') C₂ q₂
    inferInstance hdisj
  have hq₃ : q₃.under T = q₂ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers e') C₂ inferInstance hdisj
  set 𝔮₂ : Ideal B₂ := q₃.under B₂ with h𝔮₂def
  have h𝔮₂ : 𝔮₂ = q₂.comap (algebraMap B₂ T) := by
    rw [h𝔮₂def, Ideal.under, IsScalarTower.algebraMap_eq B₂ T C₂, ← Ideal.comap_comap]
    exact congrArg _ hq₃
  -- `q₃` is the unique prime of `C₂` over `𝔮₂`.
  have huniq₃ : ∀ (Q : Ideal C₂) [Q.IsPrime], Q.under B₂ = 𝔮₂ → Q = q₃ := by
    intro Q hQ hQ𝔮
    have hQ₂ : Q.under T = q₂ := by
      refine huniq' _ inferInstance ⟨?_⟩ ?_
      · rw [Ideal.under_under, ← Ideal.under_under (B := B₂), hQ𝔮, h𝔮₂def, Ideal.under_under,
          ← Ideal.under_under (B := T), hq₃, Ideal.LiesOver.over (P := q₂) (p := P₂)]
      · intro h
        have : algebraMap T C₂ e' ∈ Q := h
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ this
          (IsLocalization.map_units C₂ ⟨e', Submonoid.mem_powers e'⟩))
    rw [← IsLocalization.map_under (Submonoid.powers e') C₂ Q, hQ₂]
  -- The residue field extension `κ(q₃)/κ(𝔮₂)` is trivial.
  have hBT : (algebraMap B₂ T).comp (algebraMap B B₂) =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B C) := by
    ext b
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply B B₂ T]
    exact (Algebra.TensorProduct.includeRight.commutes b).symm
  have hres₃ : Function.Bijective (Ideal.ResidueField.map 𝔮₂ q₃ (algebraMap B₂ C₂) rfl) := by
    have hres₂' : Function.Bijective
        (Ideal.ResidueField.map p P₂ (algebraMap A A₂) (P₂.over_def p)) := hres₂
    have hB₂ : q.under B = 𝔮₂.comap Algebra.TensorProduct.includeRight.toRingHom := by
      rw [h𝔮₂, Ideal.comap_comap]
      change q.under B = q₂.comap ((algebraMap B₂ T).comp (algebraMap B B₂))
      rw [hBT, ← Ideal.comap_comap, hq₂C]
    have hA₂ : P₂ = 𝔮₂.comap Algebra.TensorProduct.includeLeftRingHom := by
      rw [h𝔮₂, Ideal.comap_comap, Ideal.LiesOver.over (P := q₂) (p := P₂), Ideal.under,
        IsScalarTower.algebraMap_eq A₂ B₂ T]
      rfl
    have ha := Ideal.ResidueField.bijective_map_includeRight p P₂ (P₂.over_def p) hres₂'
      (q.under B) 𝔮₂ hB₂ hA₂
    have hb := Ideal.ResidueField.bijective_map_includeRight (q.under B) 𝔮₂ hB₂ ha q q₂ hq₂C.symm
      h𝔮₂
    have hc : Function.Bijective (Ideal.ResidueField.map 𝔮₂ q₂ (algebraMap B₂ T) h𝔮₂) := by
      have hsq : (Ideal.ResidueField.map 𝔮₂ q₂ (algebraMap B₂ T) h𝔮₂).comp
          (Ideal.ResidueField.map (q.under B) 𝔮₂ Algebra.TensorProduct.includeRight.toRingHom hB₂) =
          (Ideal.ResidueField.map q q₂ Algebra.TensorProduct.includeRight.toRingHom hq₂C.symm).comp
            (Ideal.ResidueField.map (q.under B) q (algebraMap B C) rfl) := by
        refine Ideal.ResidueField.ringHom_ext ?_
        ext b
        simp only [RingHom.coe_comp, Function.comp_apply, Ideal.ResidueField.map_algebraMap]
        congr 1
        exact RingHom.congr_fun hBT b
      refine ⟨RingHom.injective _, fun y ↦ ?_⟩
      obtain ⟨w, rfl⟩ := hb.2 y
      obtain ⟨v, rfl⟩ := hres.2 w
      exact ⟨_, RingHom.congr_fun hsq v⟩
    have hd : Function.Bijective (Ideal.ResidueField.map q₂ q₃ (algebraMap T C₂) hq₃.symm) :=
      (RingHom.surjectiveOnStalks_of_isLocalization (M := Submonoid.powers e')
        C₂).residueFieldMap_bijective q₂ q₃ hq₃.symm
    have hcomp : Ideal.ResidueField.map 𝔮₂ q₃ (algebraMap B₂ C₂) rfl =
        (Ideal.ResidueField.map q₂ q₃ (algebraMap T C₂) hq₃.symm).comp
          (Ideal.ResidueField.map 𝔮₂ q₂ (algebraMap B₂ T) h𝔮₂) := by
      refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun x ↦ ?_)
      simp only [RingHom.coe_comp, Function.comp_apply, Ideal.ResidueField.map_algebraMap]
      rw [IsScalarTower.algebraMap_apply B₂ T C₂]
    rw [hcomp]
    exact hd.comp hc
  have hrank : Module.rankAtStalk (R := B₂) C₂ ⟨𝔮₂, inferInstance⟩ = 1 :=
    rankAtStalk_eq_one_of_forall_under_eq q₃ huniq₃ hres₃
  -- The locus of rank one is clopen; push its complement down to `Spec A₂` and choose `a`.
  have : Module.FinitePresentation B₂ C₂ :=
    Module.FinitePresentation.of_finite_of_finitePresentation B₂ C₂
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := B₂) C₂) :=
    Module.isLocallyConstant_rankAtStalk
  let U : Set (PrimeSpectrum B₂) := {x | Module.rankAtStalk (R := B₂) C₂ x = 1}
  have hU : IsClopen U := hlc.isClopen_fiber 1
  let Z' : Set (PrimeSpectrum A₂) := PrimeSpectrum.comap (algebraMap A₂ B₂) '' Uᶜ
  have hZ' : IsClosed Z' :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _
      ((algebraMap_isIntegral_iff (R := A₂) (A := B₂)).mpr inferInstance) _
      hU.compl.isClosed
  have h𝔮₂P₂ : 𝔮₂.under A₂ = P₂ := by
    rw [h𝔮₂def, Ideal.under_under, ← Ideal.under_under (B := T), hq₃,
      Ideal.LiesOver.over (P := q₂) (p := P₂)]
  have hres₂' : Function.Bijective
      (Ideal.ResidueField.map p P₂ (algebraMap A A₂) (P₂.over_def p)) := hres₂
  have hB₂ : q.under B = 𝔮₂.comap Algebra.TensorProduct.includeRight.toRingHom := by
    rw [h𝔮₂, Ideal.comap_comap]
    change q.under B = q₂.comap ((algebraMap B₂ T).comp (algebraMap B B₂))
    rw [hBT, ← Ideal.comap_comap, hq₂C]
  have hP₂ : (⟨P₂, inferInstance⟩ : PrimeSpectrum A₂) ∉ Z' := by
    rintro ⟨x, hx, hxP⟩
    have hx₁ : x.asIdeal.LiesOver P₂ := ⟨(PrimeSpectrum.ext_iff.mp hxP).symm⟩
    have hx₂ : 𝔮₂.LiesOver P₂ := ⟨h𝔮₂P₂.symm⟩
    have hx₃ : (x.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom).under A = p := by
      rw [Ideal.under, Ideal.comap_comap]
      have : Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A B) =
          (algebraMap A₂ B₂).comp (algebraMap A A₂) := by
        ext a
        simp [Algebra.TensorProduct.algebraMap_apply]
        rfl
      rw [this, ← Ideal.comap_comap]
      change (x.asIdeal.under A₂).under A = p
      rw [← hx₁.over, P₂.over_def p]
    have : x = ⟨𝔮₂, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      refine Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hres₂' x.asIdeal 𝔮₂ ?_
      rw [← hB₂]
      exact huniqB _ hx₃
    exact hx (by rw [this]; exact hrank)
  obtain ⟨_, ⟨a, rfl⟩, ha, haZ'⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP₂ hZ'.isOpen_compl
  -- Base change to `A' := A₂[1/a]`.
  let A' := Localization.Away a
  have : Algebra.Etale A A' := Algebra.Etale.comp A A₂ A'
  let B₃ := B₂ ⊗[A₂] A'
  let C₃ := C₂ ⊗[A₂] A'
  let ρ : B₃ →ₐ[A₂] C₃ :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A₂ B₂ C₂) (AlgHom.id A₂ A')
  let : Algebra B₃ C₃ := ρ.toRingHom.toAlgebra
  have hρ : ∀ x, algebraMap B₃ C₃ x = ρ x := fun _ ↦ rfl
  have : IsScalarTower B₂ B₃ C₃ := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change algebraMap B₂ C₂ x ⊗ₜ (1 : A') = ρ (x ⊗ₜ 1)
    rw [Algebra.TensorProduct.map_tmul]
    rfl)
  have : IsScalarTower A₂ B₃ C₃ := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    rw [hρ, ρ.commutes])
  have : Algebra.IsPushout B₂ C₂ B₃ C₃ :=
    Algebra.IsPushout.tensorProduct_tensorProduct A₂ A' B₂ C₂ (by
      ext x
      change ρ (1 ⊗ₜ x) = 1 ⊗ₜ x
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)
  have : Algebra.IsPushout B₂ B₃ C₂ C₃ := Algebra.IsPushout.symm inferInstance
  let e₃ : B₃ ⊗[B₂] C₂ ≃ₐ[B₃] C₃ := Algebra.IsPushout.equiv B₂ B₃ C₂ C₃
  have : Module.Finite B₃ C₃ := Module.Finite.equiv e₃.toLinearEquiv
  have : Module.Flat B₃ C₃ := Module.Flat.of_linearEquiv e₃.toLinearEquiv.symm
  -- `C₃` has rank one everywhere over `B₃`.
  have hrank₃ : Module.rankAtStalk (R := B₃) C₃ = 1 := by
    funext x
    rw [Algebra.rankAtStalk_eq_of_isPushout B₂ C₂ B₃ C₃ x, Pi.one_apply]
    by_contra hx
    have hx' : PrimeSpectrum.comap (algebraMap B₂ B₃) x ∈ Uᶜ := hx
    refine haZ' ?_ ⟨_, hx', rfl⟩
    -- the image of `x` in `Spec A₂` avoids `a`, since `a` is a unit in `A'`
    change a ∉ (PrimeSpectrum.comap (algebraMap A₂ B₂)
      (PrimeSpectrum.comap (algebraMap B₂ B₃) x)).asIdeal
    intro hax
    have : algebraMap A₂ B₃ a ∈ x.asIdeal := by
      simpa [IsScalarTower.algebraMap_apply A₂ B₂ B₃] using hax
    rw [IsScalarTower.algebraMap_apply A₂ A' B₃] at this
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this
      ((IsLocalization.Away.algebraMap_isUnit a).map (algebraMap A' B₃)))
  have hbij : Function.Bijective (algebraMap B₃ C₃) :=
    Module.algebraMap_bijective_of_rankAtStalk hrank₃
  let χ : C₃ ≃ₐ[B₃] B₃ := (AlgEquiv.ofBijective (Algebra.ofId B₃ C₃) hbij).symm
  have hχ : ∀ y : B₃, χ (algebraMap B₃ C₃ y) = y := fun y ↦
    (AlgEquiv.ofBijective (Algebra.ofId B₃ C₃) hbij).symm_apply_apply y
  -- The identification `B₃ ≅ A' ⊗[A] B`.
  let κ : B₃ ≃ₐ[A'] A' ⊗[A] B :=
    (Algebra.TensorProduct.commRight A₂ A' B₂).symm.trans
      (Algebra.TensorProduct.cancelBaseChange A A₂ A' A' B)
  have hκ : ∀ b : B, κ (algebraMap B₂ B₃ (algebraMap B B₂ b)) =
      Algebra.TensorProduct.includeRight b := by
    intro b
    change Algebra.TensorProduct.cancelBaseChange A A₂ A' A' B
      ((Algebra.TensorProduct.commRight A₂ A' B₂).symm ((1 ⊗ₜ[A] b) ⊗ₜ[A₂] (1 : A'))) = _
    rw [Algebra.TensorProduct.commRight_symm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
      one_smul]
    rfl
  -- The morphism `h : C → A' ⊗[A] B`.
  let ρ₀ : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let ρ₁ : T →+* C₂ := algebraMap T C₂
  let ρ₂ : C₂ →+* C₃ := algebraMap C₂ C₃
  let h₀ : C →+* A' ⊗[A] B :=
    κ.toRingHom.comp (χ.toRingHom.comp (ρ₂.comp (ρ₁.comp ρ₀)))
  have hB : ∀ b : B, h₀ (algebraMap B C b) = Algebra.TensorProduct.includeRight b := by
    intro b
    have h1 : ρ₀ (algebraMap B C b) = algebraMap B₂ T (algebraMap B B₂ b) :=
      (RingHom.congr_fun hBT b).symm
    have h2 : ρ₂ (ρ₁ (algebraMap B₂ T (algebraMap B B₂ b))) =
        algebraMap B₃ C₃ (algebraMap B₂ B₃ (algebraMap B B₂ b)) := by
      rw [← IsScalarTower.algebraMap_apply B₂ B₃ C₃, ← IsScalarTower.algebraMap_apply B₂ T C₂,
        ← IsScalarTower.algebraMap_apply B₂ C₂ C₃]
    simp only [h₀, RingHom.comp_apply, h1, h2]
    change κ (χ (algebraMap B₃ C₃ _)) = _
    rw [hχ, hκ]
  let h : C →ₐ[A] A' ⊗[A] B :=
    { h₀ with
      commutes' := fun x ↦ by
        change h₀ (algebraMap A C x) = algebraMap A _ x
        rw [IsScalarTower.algebraMap_apply A B C, hB, Algebra.TensorProduct.includeRight.commutes] }
  -- The prime `P'` of `A' = A₂[1/a]` over `P₂`.
  have hdisjP : Disjoint (Submonoid.powers a : Set A₂) P₂ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr ha
  let P' : Ideal A' := P₂.map (algebraMap A₂ A')
  have hP' : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) A' P₂ inferInstance hdisjP
  have hP'P₂ : P'.under A₂ = P₂ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) A' inferInstance hdisjP
  have hP'p : P'.LiesOver p := ⟨by
    rw [Ideal.LiesOver.over (P := P₂) (p := p), ← hP'P₂, Ideal.under_under]⟩
  have hresP' : Function.Bijective
      (Ideal.ResidueField.map p P' (algebraMap A A') (P'.over_def p)) := by
    have h₁ : Function.Bijective (Ideal.ResidueField.map P₂ P' (algebraMap A₂ A') hP'P₂.symm) :=
      (RingHom.surjectiveOnStalks_of_isLocalization (M := Submonoid.powers a)
        A').residueFieldMap_bijective P₂ P' hP'P₂.symm
    have hcomp : Ideal.ResidueField.map p P' (algebraMap A A') (P'.over_def p) =
        (Ideal.ResidueField.map P₂ P' (algebraMap A₂ A') hP'P₂.symm).comp
          (Ideal.ResidueField.map p P₂ (algebraMap A A₂) (P₂.over_def p)) := by
      refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun x ↦ ?_)
      simp only [RingHom.coe_comp, Function.comp_apply, Ideal.ResidueField.map_algebraMap]
      rw [IsScalarTower.algebraMap_apply A A₂ A']
    rw [hcomp]
    exact h₁.comp hres₂'
  refine ⟨A', inferInstance, inferInstance, inferInstance, h, ?_, P', hP', hP'p, hresP', ?_⟩
  · ext b
    exact hB b
  · -- The prime `q'`.
    have hdisj₃ : Disjoint (Submonoid.powers (algebraMap A₂ C₂ a) : Set C₂) q₃ := by
      refine (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr ?_
      intro hmem
      have : a ∈ q₃.under A₂ := hmem
      rw [← Ideal.under_under (B := B₂), h𝔮₂P₂] at this
      exact ha this
    let q₄ : Ideal C₃ := q₃.map (algebraMap C₂ C₃)
    have : q₄.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers (algebraMap A₂ C₂ a)) C₃ q₃ inferInstance hdisj₃
    have hq₄ : q₄.under C₂ = q₃ := IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers (algebraMap A₂ C₂ a)) C₃ inferInstance hdisj₃
    let σ : A' ⊗[A] B →+* C₃ := (algebraMap B₃ C₃).comp κ.symm.toRingHom
    -- `q₄` lies over `P'`
    have hq₄P' : q₄.under A' = P' := by
      have h₁ : (q₄.under A').under A₂ = P₂ := by
        rw [Ideal.under_under, ← Ideal.under_under (B := C₂), hq₄, ← h𝔮₂P₂, h𝔮₂def,
          Ideal.under_under]
      have h₂ : (q₄.under A').IsPrime := Ideal.IsPrime.under _ _
      rw [← IsLocalization.map_under (Submonoid.powers a) A' (q₄.under A'), h₁]
    have hσA' : σ.comp (algebraMap A' (A' ⊗[A] B)) = algebraMap A' C₃ := by
      ext x
      change algebraMap B₃ C₃ (κ.symm (algebraMap A' (A' ⊗[A] B) x)) = algebraMap A' C₃ x
      rw [κ.symm.commutes]
      change ρ (1 ⊗ₜ x) = 1 ⊗ₜ x
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    refine ⟨q₄.comap σ, Ideal.IsPrime.comap _, ⟨?_⟩, ?_⟩
    · rw [Ideal.under, Ideal.comap_comap, hσA']
      exact hq₄P'.symm
    have hσ : σ.comp h.toRingHom = ρ₂.comp (ρ₁.comp ρ₀) := by
      ext x
      simp only [σ, h, h₀, RingHom.comp_apply]
      change algebraMap B₃ C₃ (κ.symm (κ (χ _))) = _
      rw [κ.symm_apply_apply]
      exact (AlgEquiv.ofBijective (Algebra.ofId B₃ C₃) hbij).apply_symm_apply _
    rw [Ideal.comap_comap, hσ, ← Ideal.comap_comap, ← Ideal.comap_comap]
    change q = ((q₄.under C₂).under T).comap ρ₀
    rw [hq₄, hq₃, hq₂C]

/-- **Property (C) for a prime with trivial residue field extension.** Let `A → B` be finite and
universally injective on spectra, `C` an étale `B`-algebra and `q` a prime of `C` whose residue
field extension over `B` is trivial. Then there is an étale `A`-algebra `A'` and a `B`-algebra
map `C → A' ⊗[A] B` whose image on spectra contains `q`. -/
theorem exists_etale_algHom_comap_eq_of_bijective_residueFieldMap [Module.Finite A B]
    [Algebra.Etale B C]
    (hinj : ∀ (A'' : Type u) [CommRing A''] [Algebra A A''],
      Function.Injective (PrimeSpectrum.comap (algebraMap A'' (A'' ⊗[A] B))))
    (q : Ideal C) [q.IsPrime]
    (hres : Function.Bijective (Ideal.ResidueField.map (q.under B) q (algebraMap B C) rfl)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (h : C →ₐ[A] A' ⊗[A] B), h.comp (IsScalarTower.toAlgHom A B C) =
        Algebra.TensorProduct.includeRight ∧
      ∃ (q' : Ideal (A' ⊗[A] B)) (_ : q'.IsPrime), q = q'.comap h.toRingHom := by
  -- uniqueness of the prime of `B` over `p`, from universal injectivity at `A'' = A`
  have huniqB : ∀ (Q : Ideal B) [Q.IsPrime], Q.under A = q.under A → Q = q.under B := by
    intro Q _ hQ
    let e : A ⊗[A] B ≃ₐ[A] B := Algebra.TensorProduct.lid A B
    have he : e.toRingHom.comp (algebraMap A (A ⊗[A] B)) = algebraMap A B :=
      RingHom.ext fun x ↦ e.commutes x
    have key : ∀ (I : Ideal B) [I.IsPrime], PrimeSpectrum.comap (algebraMap A (A ⊗[A] B))
        (PrimeSpectrum.comap e.toRingHom ⟨I, ‹_›⟩) = ⟨I.under A, inferInstance⟩ := fun I _ ↦ by
      rw [← PrimeSpectrum.comap_comp_apply, he]
      rfl
    have := hinj A (a₁ := PrimeSpectrum.comap e.toRingHom ⟨Q, ‹_›⟩)
      (a₂ := PrimeSpectrum.comap e.toRingHom ⟨q.under B, inferInstance⟩)
      (by rw [key, key]; exact PrimeSpectrum.ext (hQ.trans (Ideal.under_under q).symm))
    exact congrArg PrimeSpectrum.asIdeal
      (PrimeSpectrum.comap_injective_of_surjective _ e.surjective this)
  obtain ⟨A', _, _, _, h, hh, P', _, _, _, q', _, _, hq'⟩ :=
    exists_etale_algHom_comap_eq_of_bijective_residueFieldMap' (A := A) (B := B) q huniqB hres
  exact ⟨A', inferInstance, inferInstance, inferInstance, h, hh, q', inferInstance, hq'⟩

end Main

section PropertyC

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C]

-- long proof with many local algebra instances
/-- **Property (C) at the ring level**, [Stacks 04DW]. Let `A → B` be finite and universally
injective on spectra with purely inseparable residue field extensions, `C` an étale
`B`-algebra and `q` a prime of `C`. Then there is an étale `A`-algebra `A'` and a `B`-algebra
map `h : C → A' ⊗[A] B` such that `q` is in the image of `Spec h`. -/
@[stacks 04DW]
theorem exists_etale_algHom_comap_eq [Module.Finite A B] [Algebra.Etale B C]
    (hinj : ∀ (A'' : Type u) [CommRing A''] [Algebra A A''],
      Function.Injective (PrimeSpectrum.comap (algebraMap A'' (A'' ⊗[A] B))))
    (hpi : ∀ (𝔮 : Ideal B) [𝔮.IsPrime],
      (Ideal.ResidueField.map (𝔮.under A) 𝔮 (algebraMap A B) rfl).IsPurelyInseparable)
    (q : Ideal C) [q.IsPrime] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (h : C →ₐ[A] A' ⊗[A] B), h.comp (IsScalarTower.toAlgHom A B C) =
        Algebra.TensorProduct.includeRight ∧
      ∃ (q' : Ideal (A' ⊗[A] B)) (_ : q'.IsPrime), q = q'.comap h.toRingHom := by
  classical
  obtain ⟨A₁, _, _, _, q₁, _, hq₁, hres₁⟩ :=
    exists_etale_bijective_residueFieldMap (A := A) q (hpi (q.under B))
  let B₁ := A₁ ⊗[A] B
  let C₁ := B₁ ⊗[B] C
  -- Universal injectivity of `A₁ → B₁`.
  have hinj₁ : ∀ (A'' : Type u) [CommRing A''] [Algebra A₁ A''],
      Function.Injective (PrimeSpectrum.comap (algebraMap A'' (A'' ⊗[A₁] B₁))) := by
    intro A'' _ _
    let : Algebra A A'' := ((algebraMap A₁ A'').comp (algebraMap A A₁)).toAlgebra
    have : IsScalarTower A A₁ A'' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    let e : A'' ⊗[A₁] B₁ ≃ₐ[A''] A'' ⊗[A] B :=
      Algebra.TensorProduct.cancelBaseChange A A₁ A'' A'' B
    have he : e.symm.toRingHom.comp (algebraMap A'' (A'' ⊗[A] B)) =
        algebraMap A'' (A'' ⊗[A₁] B₁) := RingHom.ext fun x ↦ e.symm.commutes x
    intro x y hxy
    have hcomp : ∀ z, PrimeSpectrum.comap (algebraMap A'' (A'' ⊗[A] B))
        (PrimeSpectrum.comap e.symm.toRingHom z) =
        PrimeSpectrum.comap (algebraMap A'' (A'' ⊗[A₁] B₁)) z := fun z ↦ by
      rw [← PrimeSpectrum.comap_comp_apply, he]
    have := hinj A'' (a₁ := PrimeSpectrum.comap e.symm.toRingHom x)
      (a₂ := PrimeSpectrum.comap e.symm.toRingHom y) (by rw [hcomp, hcomp, hxy])
    exact PrimeSpectrum.comap_injective_of_surjective _ e.symm.surjective this
  obtain ⟨A₁', _, _, _, h₁, hh₁, q₁', _, hq₁'⟩ :=
    exists_etale_algHom_comap_eq_of_bijective_residueFieldMap (A := A₁) (B := B₁) (C := C₁)
      hinj₁ q₁ hres₁
  let : Algebra A A₁' := ((algebraMap A₁ A₁').comp (algebraMap A A₁)).toAlgebra
  have : IsScalarTower A A₁ A₁' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.Etale A A₁' := Algebra.Etale.comp A A₁ A₁'
  let κ : A₁' ⊗[A₁] B₁ ≃ₐ[A₁'] A₁' ⊗[A] B := Algebra.TensorProduct.cancelBaseChange A A₁ A₁' A₁' B
  let ι : C →ₐ[A] C₁ := (Algebra.TensorProduct.includeRight : C →ₐ[B] C₁).restrictScalars A
  let h : C →ₐ[A] A₁' ⊗[A] B :=
    (κ.toAlgHom.restrictScalars A).comp ((h₁.restrictScalars A).comp ι)
  refine ⟨A₁', inferInstance, inferInstance, inferInstance, h, ?_, ?_⟩
  · ext b
    have h1 : ι (algebraMap B C b) = algebraMap B₁ C₁ (algebraMap B B₁ b) := by
      change Algebra.TensorProduct.includeRight (algebraMap B C b) = _
      rw [Algebra.TensorProduct.includeRight.commutes, IsScalarTower.algebraMap_apply B B₁ C₁]
    have h2 : h₁ (algebraMap B₁ C₁ (algebraMap B B₁ b)) =
        Algebra.TensorProduct.includeRight (algebraMap B B₁ b) := by
      have := congr($hh₁ (algebraMap B B₁ b))
      simpa using this
    simp only [h, AlgHom.comp_apply, AlgHom.coe_restrictScalars']
    change κ (h₁ (ι (algebraMap B C b))) = _
    rw [h1, h2]
    change κ (1 ⊗ₜ[A₁] (1 ⊗ₜ[A] b)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    rfl
  · refine ⟨q₁'.comap κ.symm.toRingHom, Ideal.IsPrime.comap _, ?_⟩
    rw [Ideal.comap_comap]
    have : κ.symm.toRingHom.comp h.toRingHom = h₁.toRingHom.comp ι.toRingHom :=
      RingHom.ext fun x ↦ κ.symm_apply_apply _
    rw [this, ← Ideal.comap_comap, ← hq₁', hq₁]
    rfl

end PropertyC

end Algebra.Etale
