/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Fixed points of finite étale algebras

Let `A` be a finite étale `R`-algebra and `σ` a finite family of `R`-algebra endomorphisms of
`A`, e.g. the action of a finite group. We show that the subalgebra `A^σ` of common fixed
points is again finite étale over `R`, and compute its geometric points.

## Main definitions

- `AlgHom.fixedPoints`: the subalgebra of common fixed points of a family of endomorphisms.

## Main results

- `AlgHom.tensorFixedPointsEquiv`: base change along a flat algebra commutes with taking fixed
  points.

-/

@[expose] public section

universe u

open TensorProduct

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}

/-- The subalgebra of common fixed points of a family `σ` of `R`-algebra endomorphisms of `A`. -/
def fixedPoints (σ : ι → A →ₐ[R] A) : Subalgebra R A :=
  AlgHom.equalizer (AlgHom.pi σ) (AlgHom.pi fun _ ↦ AlgHom.id R A)

@[simp]
lemma mem_fixedPoints {σ : ι → A →ₐ[R] A} {a : A} : a ∈ fixedPoints σ ↔ ∀ i, σ i a = a := by
  simp [fixedPoints, AlgHom.mem_equalizer, funext_iff]

variable (T : Type*) [CommRing T] [Algebra R T]

/-- The base change `𝟙 ⊗ σᵢ` of a family of endomorphisms. -/
noncomputable abbrev baseChangeFamily (σ : ι → A →ₐ[R] A) : ι → T ⊗[R] A →ₐ[T] T ⊗[R] A :=
  fun i ↦ Algebra.TensorProduct.map (AlgHom.id T T) (σ i)

lemma equalizer_map_pi_eq_fixedPoints [_root_.Finite ι] (σ : ι → A →ₐ[R] A) :
    AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.pi σ))
      (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.pi fun _ ↦ AlgHom.id R A)) =
      fixedPoints (baseChangeFamily T σ) := by
  classical
  cases nonempty_fintype ι
  have key (τ : ι → A →ₐ[R] A) (x : T ⊗[R] A) :
      Algebra.TensorProduct.piRight R T T (fun _ : ι ↦ A)
        (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.pi τ) x) =
        fun i ↦ Algebra.TensorProduct.map (AlgHom.id T T) (τ i) x := by
    induction x using TensorProduct.inductionOn with
    | tmul t a => ext i; simp
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
  ext x
  rw [AlgHom.mem_equalizer, mem_fixedPoints,
    ← (Algebra.TensorProduct.piRight R T T fun _ : ι ↦ A).injective.eq_iff, key, key, funext_iff]
  simp

/-- Base change along a flat algebra commutes with taking common fixed points of a finite family
of endomorphisms. -/
noncomputable def tensorFixedPointsEquiv [_root_.Finite ι] [Module.Flat R T] (σ : ι → A →ₐ[R] A) :
    T ⊗[R] fixedPoints σ ≃ₐ[T] fixedPoints (baseChangeFamily T σ) :=
  (AlgHom.tensorEqualizerEquiv T T _ _).trans
    (Subalgebra.equivOfEq _ _ (equalizer_map_pi_eq_fixedPoints T σ))

@[simp]
lemma coe_tensorFixedPointsEquiv_tmul [_root_.Finite ι] [Module.Flat R T] (σ : ι → A →ₐ[R] A)
    (t : T) (a : fixedPoints σ) :
    (tensorFixedPointsEquiv T σ (t ⊗ₜ a) : T ⊗[R] A) = t ⊗ₜ (a : A) :=
  rfl

section Conj

variable {A' : Type*} [CommRing A'] [Algebra R A']

/-- The conjugate `e ∘ σᵢ ∘ e⁻¹` of a family of endomorphisms by an algebra isomorphism. -/
def conjFamily (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) : ι → A' →ₐ[R] A' :=
  fun i ↦ (e : A →ₐ[R] A').comp ((σ i).comp (e.symm : A' →ₐ[R] A))

@[simp]
lemma conjFamily_apply (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) (i : ι) (a : A') :
    conjFamily e σ i a = e (σ i (e.symm a)) :=
  rfl

lemma fixedPoints_conjFamily (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) :
    fixedPoints (conjFamily e σ) = (fixedPoints σ).map (e : A →ₐ[R] A') := by
  ext a
  simp only [mem_fixedPoints, conjFamily_apply, Subalgebra.mem_map]
  constructor
  · intro h
    refine ⟨e.symm a, fun i ↦ ?_, by simp⟩
    rw [← e.injective.eq_iff, h, AlgEquiv.apply_symm_apply]
  · rintro ⟨b, hb, rfl⟩ i
    simp [hb]

/-- An algebra isomorphism identifies the fixed points of a family with the fixed points of its
conjugate. -/
noncomputable def fixedPointsCongr (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) :
    fixedPoints σ ≃ₐ[R] fixedPoints (conjFamily e σ) :=
  (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (fixedPoints_conjFamily e σ).symm)

@[simp]
lemma coe_fixedPointsCongr_apply (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) (a : fixedPoints σ) :
    (fixedPointsCongr e σ a : A') = e a :=
  rfl

end Conj

end AlgHom

namespace Algebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Finite étale is local on the base: if every prime `p` of `R` has a basic open neighbourhood
`D(f)` over which `B` is finite étale, then `B` is finite étale over `R`. -/
theorem finite_and_etale_of_forall_exists_localizationAway
    (H : ∀ p : Ideal R, p.IsPrime → ∃ f ∉ p,
      Module.Finite (Localization.Away f) (Localization.Away f ⊗[R] B) ∧
        Algebra.Etale (Localization.Away f) (Localization.Away f ⊗[R] B)) :
    Module.Finite R B ∧ Algebra.Etale R B := by
  let s : Set R := {f | Module.Finite (Localization.Away f) (Localization.Away f ⊗[R] B) ∧
    Algebra.Etale (Localization.Away f) (Localization.Away f ⊗[R] B)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hfs⟩ := H m hm.isPrime
    exact hf (hsm (Ideal.subset_span hfs))
  have hcomp (f : R) : (algebraMap (Localization.Away f) (Localization.Away f ⊗[R] B)).comp
      (algebraMap R (Localization.Away f)) =
      (algebraMap B (Localization.Away f ⊗[R] B)).comp (algebraMap R B) := by
    ext r
    simp [Algebra.algebraMap_eq_smul_one]
  constructor
  · rw [← RingHom.finite_algebraMap]
    refine RingHom.finite_ofLocalizationSpan.ofIsLocalization RingHom.finite_respectsIso _ s hs
      fun f ↦ ⟨Localization.Away f.1, Localization.Away f.1 ⊗[R] B, _, _, _, _, inferInstance,
        inferInstance,
        algebraMap _ _, hcomp f.1, ?_⟩
    rw [RingHom.finite_algebraMap]
    exact f.2.1
  · rw [← RingHom.etale_algebraMap]
    refine RingHom.Etale.ofLocalizationSpan.ofIsLocalization RingHom.Etale.respectsIso _ s hs
      fun f ↦ ⟨Localization.Away f.1, Localization.Away f.1 ⊗[R] B, _, _, _, _, inferInstance,
        inferInstance,
        algebraMap _ _, hcomp f.1, ?_⟩
    rw [RingHom.etale_algebraMap]
    exact f.2.2

end Algebra

namespace Pi

variable {S X : Type*} [CommRing S] [Finite X] [DecidableEq X]

/-- A ring map out of `X → S` sending the idempotent `δ_{x₀}` to `1` only depends on the value
at `x₀`. -/
lemma ringHom_apply_eq_of_apply_single {B : Type*} [CommRing B] (ψ : (X → S) →+* B) (x₀ : X)
    (h : ψ (Pi.single x₀ 1) = 1) (f : X → S) : ψ f = ψ (fun _ ↦ f x₀) := by
  classical
  have := Fintype.ofFinite X
  have hsingle (x : X) : Pi.single x (f x) = (fun _ ↦ f x) * Pi.single x 1 := by
    ext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum, Finset.sum_eq_single x₀]
  · rw [hsingle, map_mul, h, mul_one]
  · intro x _ hx
    have h0 : (Pi.single x 1 : X → S) * Pi.single x₀ 1 = 0 := by
      ext y
      by_cases hy : y = x
      · subst hy; simp [hx]
      · simp [Pi.single_apply, hy]
    rw [hsingle, map_mul, ← mul_one (ψ (Pi.single x 1)), ← h, ← map_mul, h0, map_zero,
      mul_zero]
  · simp

end Pi

namespace AlgHom

variable {S X : Type*} [CommRing S] [_root_.Finite X] [DecidableEq X] {ι : Type*}

/-- The family of coordinate endomorphisms `f ↦ f ∘ πᵢ` of `X → S`. -/
def coordFamily (π : ι → X → X) : ι → (X → S) →ₐ[S] (X → S) :=
  fun i ↦ AlgHom.pi fun x ↦ Pi.evalAlgHom S (fun _ ↦ S) (π i x)

omit [_root_.Finite X] [DecidableEq X] in
@[simp]
lemma coordFamily_apply (π : ι → X → X) (i : ι) (f : X → S) :
    coordFamily (S := S) π i f = f ∘ π i :=
  rfl

/-- The fixed points of a family of coordinate endomorphisms are the functions on the quotient of
`X` by the relation generated by `x ~ πᵢ x`. -/
noncomputable def fixedPointsCoordFamilyEquiv (π : ι → X → X) :
    fixedPoints (coordFamily (S := S) π) ≃ₐ[S] (Quot (fun x y : X ↦ ∃ i, π i x = y) → S) where
  toFun f := Quot.lift f.1 fun x y ⟨i, hi⟩ ↦ by
    have := congr_fun (mem_fixedPoints.mp f.2 i) x
    simp only [coordFamily_apply, Function.comp_apply] at this
    rw [← hi, this]
  invFun g := ⟨g ∘ Quot.mk _, mem_fixedPoints.mpr fun i ↦ funext fun x ↦ by
    simp only [coordFamily_apply, Function.comp_apply]
    exact congr_arg g (Quot.sound ⟨i, rfl⟩).symm⟩
  left_inv f := rfl
  right_inv g := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl
  map_mul' f g := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl
  map_add' f g := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl
  commutes' r := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl

/-- After inverting a suitable element outside a given prime, every finite family of algebra
endomorphisms of `X → S` becomes a family of coordinate endomorphisms. -/
lemma exists_localizationAway_coordinate [_root_.Finite ι] (σ : ι → (X → S) →ₐ[S] (X → S))
    (q : Ideal S) [q.IsPrime] :
    ∃ h ∉ q, ∃ π : ι → X → X, ∀ i x,
      algebraMap S (Localization.Away h) (σ i (Pi.single (π i x) 1) x) = 1 := by
  classical
  have := Fintype.ofFinite X
  cases nonempty_fintype ι
  have hex (i : ι) (x : X) : ∃ y, σ i (Pi.single y 1) x ∉ q := by
    by_contra! H
    have : ∑ y, σ i (Pi.single y 1) x ∈ q := Ideal.sum_mem _ fun y _ ↦ H y
    rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single (fun _ ↦ (1 : S)),
      show (fun _ ↦ (1 : S)) = (1 : X → S) from rfl, map_one, Pi.one_apply] at this
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr this)
  choose π hπ using hex
  let u (i : ι) (x : X) : S := σ i (Pi.single (π i x) 1) x
  refine ⟨∏ i, ∏ x, u i x, ?_, π, fun i x ↦ ?_⟩
  · simp only [Ideal.IsPrime.prod_mem_iff, not_exists, not_and]
    exact fun i _ x _ ↦ hπ i x
  · have hunit : IsUnit (algebraMap S (Localization.Away (∏ i, ∏ x, u i x)) (u i x)) := by
      refine isUnit_of_dvd_unit (map_dvd _ ?_)
        (IsLocalization.Away.algebraMap_isUnit (R := S)
          (S := Localization.Away (∏ i, ∏ x, u i x)) (∏ i, ∏ x, u i x))
      exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ x)).trans
        (Finset.dvd_prod_of_mem (fun i ↦ ∏ x, u i x) (Finset.mem_univ i))
    have hidem : IsIdempotentElem (u i x) := by
      change σ i _ x * σ i _ x = σ i _ x
      rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (hidem.map (algebraMap S _))

end AlgHom

namespace AlgHom

/-- After inverting `h`, a family of endomorphisms of `Fin n → S` satisfying the conclusion of
`AlgHom.exists_localizationAway_coordinate` becomes the coordinate family of `π`. -/
lemma conjFamily_piScalarRight_eq_coordFamily {S : Type*} [CommRing S] {n : ℕ} {ι : Type*}
    (σ : ι → (Fin n → S) →ₐ[S] (Fin n → S)) (h : S) (π : ι → Fin n → Fin n)
    (hπ : ∀ i x, algebraMap S (Localization.Away h) (σ i (Pi.single (π i x) 1) x) = 1) :
    conjFamily (Algebra.TensorProduct.piScalarRight S (Localization.Away h)
      (Localization.Away h) (Fin n)) (baseChangeFamily (Localization.Away h) σ) =
      coordFamily π := by
  let Sh := Localization.Away h
  let e := Algebra.TensorProduct.piScalarRight S Sh Sh (Fin n)
  funext i
  ext f x
  let ψ : (Fin n → Sh) →+* Sh :=
    (Pi.evalRingHom _ x).comp (conjFamily e (baseChangeFamily Sh σ) i).toRingHom
  have hsymm (y : Fin n) : e.symm (Pi.single y 1) = 1 ⊗ₜ Pi.single y 1 := by
    rw [AlgEquiv.symm_apply_eq]
    ext z
    by_cases hz : z = y
    · subst hz; simp [e]
    · simp [e, hz]
  have h1 : ψ (Pi.single (π i x) 1) = 1 := by
    simp only [ψ, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, conjFamily_apply, hsymm, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    simp only [e, Algebra.TensorProduct.piScalarRight_tmul, Algebra.smul_def, mul_one]
    exact hπ i x
  have := Pi.ringHom_apply_eq_of_apply_single ψ (π i x) h1 f
  simp only [ψ, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at this
  rw [this, show (fun _ ↦ f (π i x)) = algebraMap Sh (Fin n → Sh) (f (π i x)) from rfl,
    AlgHom.commutes]
  rfl

/-- The fixed points of a finite family of algebra endomorphisms of `Fin n → S` form a finite
étale `S`-algebra: locally on `Spec S` the family consists of coordinate endomorphisms, whose
fixed points are the functions on a quotient of `Fin n`. -/
theorem finite_and_etale_fixedPoints_fun {S : Type u} [CommRing S] {n : ℕ} {ι : Type*}
    [_root_.Finite ι] (σ : ι → (Fin n → S) →ₐ[S] (Fin n → S)) :
    Module.Finite S (fixedPoints σ) ∧ Algebra.Etale S (fixedPoints σ) := by
  refine Algebra.finite_and_etale_of_forall_exists_localizationAway fun q _ ↦ ?_
  obtain ⟨h, hq, π, hπ⟩ := exists_localizationAway_coordinate σ q
  refine ⟨h, hq, ?_⟩
  let Sh := Localization.Away h
  let e := Algebra.TensorProduct.piScalarRight S Sh Sh (Fin n)
  let E : Sh ⊗[S] fixedPoints σ ≃ₐ[Sh] (Quot (fun x y : Fin n ↦ ∃ i, π i x = y) → Sh) :=
    (tensorFixedPointsEquiv Sh σ).trans <| (fixedPointsCongr e _).trans <|
      (Subalgebra.equivOfEq _ _ (by rw [conjFamily_piScalarRight_eq_coordFamily σ h π hπ])).trans
        (fixedPointsCoordFamilyEquiv π)
  exact ⟨Module.Finite.equiv E.symm.toLinearEquiv, Algebra.Etale.of_equiv E.symm⟩

/-- The rank of a finite étale algebra is locally constant: every prime `p` of `R` has a basic
open neighbourhood `D(f)` over which `A` has constant rank. -/
lemma _root_.Algebra.exists_rankAtStalk_localizationAway_eq {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] (p : Ideal R)
    [hp : p.IsPrime] :
    ∃ f ∉ p, ∃ n : ℕ,
      Module.rankAtStalk (R := Localization.Away f) (Localization.Away f ⊗[R] A) = n := by
  have : Module.FinitePresentation R A := .of_finite_of_finitePresentation R A
  have hopen := (Module.isLocallyConstant_rankAtStalk (R := R) (M := A)).isOpen_fiber
    (Module.rankAtStalk A ⟨p, hp⟩)
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := ⟨p, hp⟩) (show (⟨p, hp⟩ : PrimeSpectrum R) ∈
        {x | Module.rankAtStalk A x = Module.rankAtStalk A ⟨p, hp⟩} from rfl) hopen
  refine ⟨f, hpf, Module.rankAtStalk A ⟨p, hp⟩, ?_⟩
  ext q
  rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id]
  refine hf ?_
  change f ∉ (q.comap (algebraMap R (Localization.Away f))).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  exact fun h ↦ q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h
    (IsLocalization.Away.algebraMap_isUnit f))

/-- **Fixed points of a finite étale algebra.** The common fixed points of a finite family of
endomorphisms of a finite étale `R`-algebra form a finite étale `R`-algebra.

Locally on `Spec R` the algebra `A` has constant rank, hence becomes split, `T ⊗ A ≅ Fin n → T`,
after a faithfully flat finite étale base change `T`
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). Taking fixed points commutes with the
flat base change, and the fixed points of a family of endomorphisms of `Fin n → T` are finite
étale (`AlgHom.finite_and_etale_fixedPoints_fun`); finiteness and étaleness descend along `T`. -/
theorem finite_and_etale_fixedPoints {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] {ι : Type*} [_root_.Finite ι] (σ : ι → A →ₐ[R] A) :
    Module.Finite R (fixedPoints σ) ∧ Algebra.Etale R (fixedPoints σ) := by
  refine Algebra.finite_and_etale_of_forall_exists_localizationAway fun p hp ↦ ?_
  obtain ⟨f, hpf, n, hrank⟩ := Algebra.exists_rankAtStalk_localizationAway_eq (A := A) p
  refine ⟨f, hpf, ?_⟩
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  obtain ⟨m, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  obtain ⟨h₁, h₂⟩ :=
    finite_and_etale_fixedPoints_fun
      (conjFamily e (baseChangeFamily T (baseChangeFamily (Localization.Away f) σ)))
  let E : T ⊗[(Localization.Away f)] ((Localization.Away f) ⊗[R] fixedPoints σ) ≃ₐ[T]
      fixedPoints (conjFamily e (baseChangeFamily T (baseChangeFamily (Localization.Away f) σ))) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl
      (tensorFixedPointsEquiv (Localization.Away f) σ)).trans <|
      (tensorFixedPointsEquiv T _).trans (fixedPointsCongr e _)
  have : Module.Finite T (T ⊗[(Localization.Away f)] ((Localization.Away f) ⊗[R] fixedPoints σ)) :=
    Module.Finite.equiv E.symm.toLinearEquiv
  have : Algebra.Etale T (T ⊗[(Localization.Away f)] ((Localization.Away f) ⊗[R] fixedPoints σ)) :=
    Algebra.Etale.of_equiv E.symm
  exact ⟨.of_finite_tensorProduct_of_faithfullyFlat T,
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T⟩

end AlgHom

namespace Relation

/-- Transport of the equivalence closure along a bijection. -/
lemma eqvGen_equiv_iff {α β : Type*} (e : α ≃ β) {r : α → α → Prop} {s : β → β → Prop}
    (h : ∀ a a', r a a' ↔ s (e a) (e a')) (a a' : α) :
    EqvGen r a a' ↔ EqvGen s (e a) (e a') := by
  constructor
  · intro H
    induction H with
    | rel x y hxy => exact .rel _ _ ((h x y).mp hxy)
    | refl x => exact .refl _
    | symm x y _ ih => exact .symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro H
    have key : ∀ b b', EqvGen s b b' → EqvGen r (e.symm b) (e.symm b') := by
      intro b b' H
      induction H with
      | rel x y hxy => exact .rel _ _ ((h _ _).mpr (by simpa using hxy))
      | refl x => exact .refl _
      | symm x y _ ih => exact .symm _ _ ih
      | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
    simpa using key _ _ H

/-- Transport of a surjection whose fibres are the classes of an equivalence closure along
bijections compatible with the maps and the relations. -/
lemma surjective_and_iff_eqvGen_of_equiv {P P' Q Q' : Type*} (E : P' ≃ P) (EF : Q' ≃ Q)
    (res' : P' → Q')
    (res : P → Q) (h : ∀ s, EF (res' s) = res (E s)) {r' : P' → P' → Prop} {r : P → P → Prop}
    (hr : ∀ s s', r' s s' ↔ r (E s) (E s'))
    (H : Function.Surjective res' ∧ ∀ s s', res' s = res' s' ↔ Relation.EqvGen r' s s') :
    Function.Surjective res ∧ ∀ t t', res t = res t' ↔ Relation.EqvGen r t t' := by
  refine ⟨fun q ↦ ?_, fun t t' ↦ ?_⟩
  · obtain ⟨s, hs⟩ := H.1 (EF.symm q)
    exact ⟨E s, by rw [← h, hs, Equiv.apply_symm_apply]⟩
  · obtain ⟨s, rfl⟩ := E.surjective t
    obtain ⟨s', rfl⟩ := E.surjective t'
    rw [← h, ← h, EF.injective.eq_iff, H.2, Relation.eqvGen_equiv_iff E hr]

end Relation

namespace RingHom.PointsOver

variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] {φ : R →+* Ω}
  {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The restriction of points along an algebra map. -/
def comap (g : B →ₐ[R] C) (t : PointsOver φ C) : PointsOver φ B :=
  ⟨t.1.comp g.toRingHom, by ext r; simp [t.apply_algebraMap]⟩

@[simp]
lemma comap_apply (g : B →ₐ[R] C) (t : PointsOver φ C) (b : B) : comap g t b = t (g b) :=
  rfl

/-- The restriction of points along an algebra isomorphism, as an equivalence. -/
def comapEquiv (e : B ≃ₐ[R] C) : PointsOver φ C ≃ PointsOver φ B where
  toFun := comap (e : B →ₐ[R] C)
  invFun := comap (e.symm : C →ₐ[R] B)
  left_inv t := by ext; simp
  right_inv t := by ext; simp

@[simp]
lemma comapEquiv_apply (e : B ≃ₐ[R] C) (t : PointsOver φ C) (b : B) :
    comapEquiv e t b = t (e b) :=
  rfl

/-- The points of `X → R` over `φ` are the evaluations at the elements of `X`. -/
noncomputable def evalEquiv (X : Type*) [Fintype X] [DecidableEq X] :
    X ≃ PointsOver φ (X → R) :=
  Equiv.ofBijective (fun x ↦ ⟨φ.comp (Pi.evalRingHom _ x), by ext; simp⟩) <| by
    constructor
    · intro x y hxy
      by_contra hne
      have := congr_arg (fun t : PointsOver φ (X → R) ↦ t (Pi.single x 1)) hxy
      simp [Ne.symm hne] at this
    · intro t
      have hidem (x : X) : IsIdempotentElem (t (Pi.single x 1)) := by
        rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one]
      have hsum : ∑ x, t (Pi.single x 1) = 1 := by
        rw [← map_sum, Finset.univ_sum_single (fun _ ↦ (1 : R)),
          show (fun _ ↦ (1 : R)) = (1 : X → R) from rfl, map_one]
      obtain ⟨x, -, hx⟩ : ∃ x ∈ Finset.univ, t (Pi.single x 1) ≠ 0 := by
        by_contra! H
        rw [Finset.sum_eq_zero H] at hsum
        exact zero_ne_one hsum
      have hx1 : t (Pi.single x 1) = 1 :=
        (IsIdempotentElem.iff_eq_zero_or_one.mp (hidem x)).resolve_left hx
      refine ⟨x, ?_⟩
      ext f
      have := Pi.ringHom_apply_eq_of_apply_single t.1 x hx1 f
      change φ (f x) = t f
      rw [this, show (fun _ ↦ f x) = algebraMap R (X → R) (f x) from rfl, t.apply_algebraMap]

@[simp]
lemma evalEquiv_apply (X : Type*) [Fintype X] [DecidableEq X] (x : X) (f : X → R) :
    evalEquiv (φ := φ) X x f = φ (f x) :=
  rfl

end RingHom.PointsOver

namespace AlgHom

open RingHom

section Points

variable {Ω : Type*} [Field Ω]

/-- The restriction of points of `A` to points of the fixed points of `σ` is surjective, and two
points have the same restriction iff they are related by the equivalence relation generated by
`t ~ t ∘ σᵢ`. -/
private def PointsGood {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (φ : R →+* Ω)
    {ι : Type*} (σ : ι → A →ₐ[R] A) : Prop :=
  Function.Surjective (PointsOver.comap (φ := φ) (fixedPoints σ).val) ∧
    ∀ t t' : PointsOver φ A, PointsOver.comap (fixedPoints σ).val t =
      PointsOver.comap (fixedPoints σ).val t' ↔
        Relation.EqvGen (fun t t' : PointsOver φ A ↦ ∃ i, t' = PointsOver.comap (σ i) t) t t'

private lemma pointsGood_of_conj {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] {φ : R →+* Ω} {ι : Type*} (e : A ≃ₐ[R] A')
    (σ : ι → A →ₐ[R] A) (H : PointsGood φ (conjFamily e σ)) : PointsGood φ σ := by
  refine Relation.surjective_and_iff_eqvGen_of_equiv (PointsOver.comapEquiv e)
    (PointsOver.comapEquiv (fixedPointsCongr e σ))
    _ _ (fun s ↦ PointsOver.ext fun x ↦ rfl) (fun s s' ↦ exists_congr fun i ↦ ?_) H
  rw [← (PointsOver.comapEquiv e).injective.eq_iff]
  constructor <;> intro h <;> rw [h] <;> ext a <;> simp

private lemma pointsGood_of_tensor {R A T : Type*} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [Module.Flat R T] {φ : R →+* Ω} {φ' : T →+* Ω}
    (hφ' : φ'.comp (algebraMap R T) = φ) {ι : Type*} [_root_.Finite ι] (σ : ι → A →ₐ[R] A)
    (H : PointsGood φ' (baseChangeFamily T σ)) : PointsGood φ σ := by
  refine Relation.surjective_and_iff_eqvGen_of_equiv (PointsOver.tensorEquiv hφ')
    ((PointsOver.comapEquiv (tensorFixedPointsEquiv T σ)).trans (PointsOver.tensorEquiv hφ'))
    _ _ (fun s ↦ PointsOver.ext fun x ↦ rfl) (fun s s' ↦ exists_congr fun i ↦ ?_) H
  rw [← (PointsOver.tensorEquiv hφ').injective.eq_iff]
  constructor <;> intro h <;> rw [h] <;> ext a <;>
    simp [PointsOver.tensorEquiv_apply, Algebra.TensorProduct.includeRight_apply]

private lemma pointsGood_coordFamily {S : Type*} [CommRing S] (φ : S →+* Ω) {n : ℕ}
    {ι : Type*} (π : ι → Fin n → Fin n) : PointsGood φ (coordFamily (S := S) π) := by
  classical
  let r : Fin n → Fin n → Prop := fun x y ↦ ∃ i, π i x = y
  have : Fintype (Quot r) := Fintype.ofFinite _
  refine Relation.surjective_and_iff_eqvGen_of_equiv (PointsOver.evalEquiv (Fin n))
    ((PointsOver.evalEquiv (Quot r)).trans
      (PointsOver.comapEquiv (fixedPointsCoordFamilyEquiv π)))
    (Quot.mk r) _ (fun s ↦ PointsOver.ext fun x ↦ rfl) (fun s s' ↦ exists_congr fun i ↦ ?_)
    ⟨Quot.mk_surjective, fun _ _ ↦ ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩⟩
  have : PointsOver.comap (coordFamily (S := S) π i) (PointsOver.evalEquiv (φ := φ) (Fin n) s) =
      PointsOver.evalEquiv (Fin n) (π i s) :=
    PointsOver.ext fun f ↦ rfl
  rw [this, (PointsOver.evalEquiv (Fin n)).injective.eq_iff, eq_comm]

/-- A faithfully flat étale algebra has a point over every geometric point of the base. -/
lemma _root_.RingHom.PointsOver.nonempty_of_faithfullyFlat {S T : Type*} [CommRing S] [CommRing T]
    [Algebra S T] [Module.FaithfullyFlat S T] [Algebra.Etale S T] [IsSepClosed Ω]
    (φ : S →+* Ω) : Nonempty (PointsOver φ T) := by
  let := φ.toAlgebra
  have h : (RingHom.id Ω).comp (algebraMap S Ω) = φ := RingHom.id_comp _
  have : Nontrivial (Ω ⊗[S] T) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left S Ω).mpr inferInstance
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Ω (Ω ⊗[S] T)
  have hm : m ≠ 0 := by
    rintro rfl
    have : Subsingleton (Ω ⊗[S] T) := e.toEquiv.subsingleton
    exact not_subsingleton _ this
  exact ⟨PointsOver.tensorEquiv h (PointsOver.equivAlgHom.symm
    ((Pi.evalAlgHom Ω (fun _ : Fin m ↦ Ω) ⟨0, Nat.pos_of_ne_zero hm⟩).comp
      (e : Ω ⊗[S] T →ₐ[Ω] Fin m → Ω)))⟩

/-- **Geometric points of the fixed points of a finite étale algebra.** Let `A` be a finite
étale `R`-algebra, `σ` a finite family of endomorphisms of `A` and `φ : R →+* Ω` a geometric
point, `Ω` separably closed. Then every point of the fixed points `A^σ` over `φ` lifts to a point
of `A`, and two points of `A` have the same restriction to `A^σ` iff they are related by the
equivalence relation generated by `t ~ t ∘ σᵢ`.

After localizing `R` and a faithfully flat finite étale base change, `A` becomes `Fin m → T` and
`σ` a family of coordinate maps, for which this is the description of the points of the functions
on a quotient of `Fin m`. -/
theorem surjective_comap_fixedPoints_val_and_iff {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] {ι : Type*} [_root_.Finite ι]
    (σ : ι → A →ₐ[R] A) [IsSepClosed Ω] (φ : R →+* Ω) :
    Function.Surjective (PointsOver.comap (φ := φ) (fixedPoints σ).val) ∧
      ∀ t t' : PointsOver φ A, PointsOver.comap (fixedPoints σ).val t =
        PointsOver.comap (fixedPoints σ).val t' ↔
          Relation.EqvGen (fun t t' : PointsOver φ A ↦ ∃ i, t' = PointsOver.comap (σ i) t)
            t t' := by
  obtain ⟨f, hpf, n, hrank⟩ := Algebra.exists_rankAtStalk_localizationAway_eq (A := A)
    (RingHom.ker φ)
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  obtain ⟨m, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  let φf : Localization.Away f →+* Ω :=
    IsLocalization.Away.lift f (g := φ) (isUnit_iff_ne_zero.mpr hpf)
  have hφf : φf.comp (algebraMap R (Localization.Away f)) = φ := IsLocalization.lift_comp _
  obtain ⟨φT⟩ := PointsOver.nonempty_of_faithfullyFlat (T := T) φf
  let τ := conjFamily e (baseChangeFamily T (baseChangeFamily (Localization.Away f) σ))
  obtain ⟨h, hq, π, hπ⟩ := exists_localizationAway_coordinate τ (RingHom.ker φT.1)
  let φh : Localization.Away h →+* Ω :=
    IsLocalization.Away.lift h (g := φT.1) (isUnit_iff_ne_zero.mpr hq)
  have hφh : φh.comp (algebraMap T (Localization.Away h)) = φT.1 := IsLocalization.lift_comp _
  have H4 : PointsGood φh (conjFamily (Algebra.TensorProduct.piScalarRight T
      (Localization.Away h) (Localization.Away h) (Fin m))
      (baseChangeFamily (Localization.Away h) τ)) := by
    rw [conjFamily_piScalarRight_eq_coordFamily τ h π hπ]
    exact pointsGood_coordFamily φh π
  have H2 : PointsGood φT.1 τ := pointsGood_of_tensor hφh τ (pointsGood_of_conj _ _ H4)
  exact pointsGood_of_tensor hφf σ (pointsGood_of_tensor φT.2 _ (pointsGood_of_conj e _ H2))

end Points

end AlgHom

namespace AlgHom

/-- Flat base change of a injection whose image contains the fixed points of a finite family of
endomorphisms, stated for pushout squares: if `A' = S ⊗[R] A` and `B' = S ⊗[R] B` with `S` flat
over `R`, `α : B → A` is injective with image containing the fixed points of `σ`, and `α'`, `σ'`
are the base changes of `α`, `σ`, then `α'` is injective with image containing the fixed points
of `σ'`. -/
theorem injective_and_mem_range_of_isPushout {R S A B A' B' : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra R S] [Algebra R A]
    [Algebra R B] [Algebra S A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R S A']
    [IsScalarTower R A A'] [Algebra.IsPushout R S A A'] [Algebra S B'] [Algebra B B']
    [Algebra R B'] [IsScalarTower R S B'] [IsScalarTower R B B'] [Algebra.IsPushout R S B B']
    [Module.Flat R S] (α : B →ₐ[R] A) (hinj : Function.Injective α) (α' : B' →+* A')
    (h₁ : ∀ y, α' (algebraMap B B' y) = algebraMap A A' (α y))
    (h₂ : ∀ s, α' (algebraMap S B' s) = algebraMap S A' s) {ι : Type*} [_root_.Finite ι]
    (σ : ι → A →ₐ[R] A) (σ' : ι → A' →+* A')
    (h₁' : ∀ i x, σ' i (algebraMap A A' x) = algebraMap A A' (σ i x))
    (h₂' : ∀ i s, σ' i (algebraMap S A' s) = algebraMap S A' s)
    (hrange : ∀ x ∈ fixedPoints σ, x ∈ Set.range α) :
    Function.Injective α' ∧ ∀ x, (∀ i, σ' i x = x) → x ∈ Set.range α' := by
  let eA := Algebra.IsPushout.equiv R S A A'
  let eB := Algebra.IsPushout.equiv R S B B'
  let αS : S ⊗[R] B →ₐ[S] S ⊗[R] A := Algebra.TensorProduct.map (AlgHom.id S S) α
  have hcomm (z : S ⊗[R] B) : α' (eB z) = eA (αS z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s y =>
      simp [eA, eB, αS, Algebra.IsPushout.equiv_tmul, h₁, h₂]
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hσ (i : ι) (z : S ⊗[R] A) : σ' i (eA z) = eA (baseChangeFamily S σ i z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s x => simp [eA, Algebra.IsPushout.equiv_tmul, h₁', h₂']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hαS : Function.Injective αS :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) α.toLinearMap hinj
  refine ⟨fun x y hxy ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := eB.surjective x
    obtain ⟨y, rfl⟩ := eB.surjective y
    rw [hcomm, hcomm, eA.injective.eq_iff] at hxy
    rw [hαS hxy]
  · obtain ⟨y, rfl⟩ := eA.surjective x
    have hy : y ∈ fixedPoints (baseChangeFamily S σ) := mem_fixedPoints.mpr fun i ↦
      eA.injective (by rw [← hσ, hx])
    obtain ⟨z, hz⟩ := (tensorFixedPointsEquiv S σ).surjective ⟨y, hy⟩
    -- the inclusion of the fixed points factors through `α`
    have hle : (fixedPoints σ).toSubmodule ≤ LinearMap.range α.toLinearMap := fun x hx ↦ by
      obtain ⟨b, hb⟩ := hrange x hx
      exact ⟨b, hb⟩
    let β : fixedPoints σ →ₗ[R] B :=
      (LinearEquiv.ofInjective α.toLinearMap hinj).symm.toLinearMap ∘ₗ
        Submodule.inclusion hle
    have hβ (x : fixedPoints σ) : α (β x) = x :=
      congr_arg Subtype.val ((LinearEquiv.ofInjective α.toLinearMap hinj).apply_symm_apply
        (Submodule.inclusion hle x))
    refine ⟨eB (TensorProduct.AlgebraTensorModule.lTensor S S β z), ?_⟩
    rw [hcomm]
    congr 1
    have hz' := congr_arg Subtype.val hz
    simp only at hz'
    rw [← hz']
    clear hz hz'
    induction z using TensorProduct.inductionOn with
    | tmul s x => simp [αS, hβ]
    | add z z' hz hz' => simp only [map_add, hz, hz', Subalgebra.coe_add]

end AlgHom
