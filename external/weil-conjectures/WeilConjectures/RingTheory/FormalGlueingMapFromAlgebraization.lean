/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.RingTheory.FormalGlueingEquivalence
import WeilConjectures.RingTheory.FormalGlueingReplacePrime
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.RingTheory.FormalGlueingData

/-!
# Algebraization of a map that is an isomorphism away from an ideal

Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
using Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-from-algebraization).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private theorem local_comp {M N T : ModuleCat R} (a : R)
    (h : M →ₗ[R] N) (k : N →ₗ[R] T) :
    localMap a (k.comp h) = (localMap a k).comp (localMap a h) :=
  IsLocalizedModule.map_comp' _ _ _ _ _ _

private theorem local_mk_zero {M : Type*} [AddCommGroup M] [Module R M]
    (a : R) (x : M) :
    LocalizedModule.mk x (1 : Submonoid.powers a) = 0 ↔ ∃ n : ℕ, a ^ n • x = 0 := by
  rw [← LocalizedModule.mkLinearMap_apply,
    IsLocalizedModule.eq_zero_iff (Submonoid.powers a) (LocalizedModule.mkLinearMap _ M)]
  constructor
  · rintro ⟨⟨b, n, rfl⟩, hb⟩
    exact ⟨n, hb⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨a ^ n, ⟨n, rfl⟩⟩, hn⟩

private theorem local_bijective_of_torsion {M N : ModuleCat R}
    (I : Ideal R) (h : M →ₗ[R] N)
    (hk : ∀ x : h.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hc : ∀ x : N ⧸ h.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (a : R) (ha : a ∈ I) : Function.Bijective (localMap a h) := by
  have hp : ∀ n : ℕ, a ^ n ∈ I ^ n := fun n ↦ Ideal.pow_mem_pow ha n
  constructor
  · apply IsLocalizedModule.injective_of_map_zero (Submonoid.powers a)
      (LocalizedModule.mkLinearMap _ M)
    intro m hm
    have hz : LocalizedModule.mk (h m) (1 : Submonoid.powers a) = 0 := by
      simpa only [localMap, LocalizedModule.mkLinearMap_apply,
        IsLocalizedModule.map_LocalizedModules] using hm
    obtain ⟨n, hn⟩ := (local_mk_zero a (h m)).mp hz
    have hmem : a ^ n • m ∈ h.ker := by simp [LinearMap.mem_ker, hn]
    obtain ⟨k, hk⟩ := hk ⟨a ^ n • m, hmem⟩
    apply (local_mk_zero a m).mpr
    refine ⟨k + n, ?_⟩
    have hz := congrArg Subtype.val (hk (a ^ k) (hp k))
    simpa [pow_add, mul_smul] using hz
  · intro z
    induction z using LocalizedModule.induction_on with
    | _ m s =>
      obtain ⟨n, hn⟩ := hc (Submodule.Quotient.mk m)
      have hz : (a ^ n) • (Submodule.Quotient.mk m : N ⧸ h.range) = 0 :=
        hn _ (hp n)
      have hmem : a ^ n • m ∈ h.range := by
        exact (Submodule.Quotient.mk_eq_zero h.range).mp hz
      obtain ⟨p, hp⟩ := hmem
      refine ⟨LocalizedModule.mk p (⟨a ^ n, ⟨n, rfl⟩⟩ * s), ?_⟩
      rw [localMap, IsLocalizedModule.map_LocalizedModules, hp]
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, mul_smul]
      exact smul_comm _ _ _

private theorem torsion_of_local_mk_zero {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) {t : ℕ} (f : Fin t → R)
    (hf : Ideal.span (Set.range f) = I) (x : M)
    (hx : ∀ i, LocalizedModule.mk x (1 : Submonoid.powers (f i)) = 0) :
    ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0 := by
  let J : Ideal R := (LinearMap.toSpanSingleton R M x).ker
  have hIJ : I ≤ J.radical := by
    rw [← hf, Ideal.span_le]
    rintro a ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := (local_mk_zero (f i) x).mp (hx i)
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hI
  exact ⟨n, fun r hr ↦ hn hr⟩

private theorem torsion_of_local_bijective {M N : ModuleCat R}
    (I : Ideal R) (hI : I.FG) {t : ℕ} (f : Fin t → R)
    (hf : Ideal.span (Set.range f) = I) (h : M →ₗ[R] N)
    (hh : ∀ i, Function.Bijective (localMap (f i) h)) :
    (∀ x : h.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
    (∀ x : N ⧸ h.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) := by
  constructor
  · intro x
    have hx : ∀ i, LocalizedModule.mk (x : M) (1 : Submonoid.powers (f i)) = 0 := by
      intro i
      apply (hh i).1
      simp [localMap, IsLocalizedModule.map_LocalizedModules, LinearMap.mem_ker.mp x.property]
    obtain ⟨n, hn⟩ := torsion_of_local_mk_zero I hI f hf (x : M) hx
    exact ⟨n, fun r hr ↦ Subtype.ext (hn r hr)⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply torsion_of_local_mk_zero I hI f hf
      intro i
      obtain ⟨y, hy⟩ := (hh i).2 (LocalizedModule.mk x 1)
      let q := h.range.mkQ
      have hm : (localMap (f i) (M := N) (N := ModuleCat.of R (N ⧸ h.range)) q)
          ((localMap (f i) h) y) = 0 := by
        rw [localMap, localMap, ← LinearMap.comp_apply,
          ← IsLocalizedModule.map_comp' _ _ _ _ h q]
        have hqh : q.comp h = 0 := by ext z; simp [q]
        rw [hqh, map_zero, LinearMap.zero_apply]
      rw [hy] at hm
      simpa [localMap, IsLocalizedModule.map_LocalizedModules, q] using hm

private def primeFunctor (φ : R →+* S) {t : ℕ} (f : Fin t → R) :
    CategoryTheory.Functor (Data.{u, v, max u v w} φ f)
      (ModuleCat.{max u v w} S) where
  obj X := X.M'
  map h := ModuleCat.ofHom h.prime

private noncomputable def chartFunctor (φ : R →+* S) {t : ℕ} (f : Fin t → R) (i : Fin t) :
    CategoryTheory.Functor (Data.{u, v, max u v w} φ f)
      (ModuleCat.{max u v w} R) where
  obj X := piece (f i) (X.M i)
  map {X Y} h := ModuleCat.ofHom (R := R)
    (X := piece (f i) (X.M i)) (Y := piece (f i) (Y.M i)) (h.chart i)

private theorem restrict_algebraMap (M : Type*) [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M] :
    restrict (algebraMap R S) (ModuleCat.of S M) = ModuleCat.of R M := by
  dsimp [restrict, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
  congr 1
  ext r x
  exact IsScalarTower.algebraMap_smul S r x

private theorem module_cast_apply {M : Type*} [AddCommGroup M]
    (m₁ m₂ : Module R M) (hm : m₁ = m₂)
    (h : @ModuleCat.of R _ M _ m₁ = @ModuleCat.of R _ M _ m₂) (x : M) :
    (CategoryTheory.eqToIso h).hom.hom x = x ∧ (CategoryTheory.eqToIso h).inv.hom x = x := by
  cases hm
  exact ⟨rfl, rfl⟩

private theorem restrict_cast_apply (M : Type*) [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M] (x : M) :
    (CategoryTheory.eqToIso (restrict_algebraMap (R := R) (S := S) M)).hom.hom x = x ∧
    (CategoryTheory.eqToIso (restrict_algebraMap (R := R) (S := S) M)).inv.hom x = x := by
  have hm : Module.compHom M (algebraMap R S) = (inferInstance : Module R M) := by
    ext r x
    exact IsScalarTower.algebraMap_smul S r x
  exact module_cast_apply _ _ hm _ x

private theorem extend_algebra_eq (φ : R →+* S)
    (hφ : φ.toAlgebra = (inferInstance : Algebra R S)) (M : ModuleCat.{w} R) :
    extend φ M = ModuleCat.of S (S ⊗[R] M) := by
  cases hφ
  rfl

private theorem extendMap_algebra_heq (φ : R →+* S)
    (hφ : φ.toAlgebra = (inferInstance : Algebra R S))
    {M N : ModuleCat.{w} R} (h : M →ₗ[R] N) :
    HEq (extendMap φ h) (h.baseChange S) := by
  cases hφ
  rfl

private theorem transport_map {A B A' B' : ModuleCat.{w} R}
    (hA : A = A') (hB : B = B') (h : A →ₗ[R] B) (k : A' →ₗ[R] B')
    (hk : HEq h k) :
    (CategoryTheory.eqToIso hB).hom.hom.comp (h.comp (CategoryTheory.eqToIso hA).inv.hom) = k := by
  subst A' B'
  simpa using eq_of_heq hk

/-- Algebraize the map and retain ideal-power torsion of its kernel and cokernel.
Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
with Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-from-algebraization).

Choose a finite generating family of I. A direct fraction argument proves that
localizing the given map at each generator is bijective: for injectivity, clear
a denominator and then annihilate the resulting kernel element; for surjectivity,
annihilate the class of a numerator in the cokernel and lift the resulting multiple.
Apply exists_replace_prime to the canonical datum of P and the given map. This
replaces its prime component by Q and gives a morphism with bijective chart maps.
Essential surjectivity algebraizes this datum. Fullness lifts its morphism, composed
with the inverse algebraization isomorphism, to psi. Taking prime components proves
the displayed factorization; taking chart components shows each localization of
psi is bijective. Its kernel and cokernel therefore vanish after localization at
every generator, as follows directly on fractions. For each element x of either
module, every generator belongs to the radical of the annihilator of x. Thus I
lies in that radical. Mathlib's finitely generated ideal criterion (Stacks 00IM)
supplies a power of I contained in the annihilator. This also covers I = 0 and
an empty generating family. All auxiliary scalar-action identifications are proved
by module extensionality and the scalar-tower law. No comparison equivalence is
asserted here; those are proved separately using flat tensor exactness and torsion
base change.
-/
theorem exists_map_from_algebraization
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (P : Type (max u v w)) [AddCommGroup P] [Module R P]
    (Q : Type (max u v w)) [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q]
    (φ' : S ⊗[R] P →ₗ[S] Q)
    (hker : ∀ x : (φ'.restrictScalars R).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : _ ⧸ (φ'.restrictScalars R).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ T : ModuleCat.{max u v w} R,
      ∃ (ψ : P →ₗ[R] T) (β : S ⊗[R] T ≃ₗ[S] Q),
        β.toLinearMap.comp (ψ.baseChange S) = φ' ∧
        (∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∀ x : T ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) := by
  classical
  obtain ⟨t, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hf' : Ideal.span (Set.range f) = I := hf
  obtain ⟨_, Can, hobj, hmap, hequiv⟩ :=
    exists_canonical_equivalence.{u, v, w} (algebraMap R S) t f
  obtain ⟨hfull, hess⟩ := hequiv hflat (hf' ▸ hquot)
  let P₀ : ModuleCat.{max u v w} R := ModuleCat.of R P
  let Q₀ : ModuleCat.{max u v w} S := ModuleCat.of S Q
  have hext : ∀ M : ModuleCat.{max u v w} R,
      extend (algebraMap R S) M = ModuleCat.of S (S ⊗[R] M) := by
    intro M
    exact extend_algebra_eq (algebraMap R S) toAlgebra_algebraMap M
  let eP := CategoryTheory.eqToIso ((hobj P₀).1.trans (hext P₀))
  let γ : (Can.obj P₀).M' →ₗ[S] Q₀ := φ'.comp eP.hom.hom
  have hγ : ∀ i, Function.Bijective (localMap (f i) (restrictMap (algebraMap R S) γ)) := by
    intro i
    have ha : f i ∈ I := hf' ▸ Ideal.subset_span ⟨i, rfl⟩
    have hφ := local_bijective_of_torsion
      (M := ModuleCat.of R (S ⊗[R] P)) (N := ModuleCat.of R Q)
      I (φ'.restrictScalars R) hker hcoker (f i) ha
    let A := restrict (algebraMap R S) (Can.obj P₀).M'
    let B := ModuleCat.of R (S ⊗[R] P)
    let C := restrict (algebraMap R S) Q₀
    let D := ModuleCat.of R Q
    let eA : A ≅ B := (ModuleCat.restrictScalars (algebraMap R S)).mapIso eP ≪≫
      CategoryTheory.eqToIso (restrict_algebraMap (R := R) (S := S) (S ⊗[R] P))
    let eC : C ≅ D := CategoryTheory.eqToIso (restrict_algebraMap (R := R) (S := S) Q)
    have heA : Function.Bijective (localMap (f i) eA.hom.hom) :=
      ⟨IsLocalizedModule.map_injective _ _ _ _ eA.toLinearEquiv.injective,
        IsLocalizedModule.map_surjective _ _ _ _ eA.toLinearEquiv.surjective⟩
    have heC : Function.Bijective (localMap (f i) eC.inv.hom) :=
      ⟨IsLocalizedModule.map_injective _ _ _ _ eC.symm.toLinearEquiv.injective,
        IsLocalizedModule.map_surjective _ _ _ _ eC.symm.toLinearEquiv.surjective⟩
    have hγR : restrictMap (algebraMap R S) γ =
        eC.inv.hom.comp ((φ'.restrictScalars R).comp eA.hom.hom) := by
      ext x
      dsimp only [LinearMap.comp_apply, restrictMap, eA, eC]
      change γ x = (CategoryTheory.eqToIso (restrict_algebraMap (R := R) (S := S) Q)).inv.hom
        (φ' ((CategoryTheory.eqToIso (restrict_algebraMap (R := R) (S := S) (S ⊗[R] P))).hom.hom
          (eP.hom.hom x)))
      rw [(restrict_cast_apply (R := R) (S := S) Q _).2,
        (restrict_cast_apply (R := R) (S := S) (S ⊗[R] P) _).1]
      rfl
    rw [hγR]
    change Function.Bijective (localMap (f i)
      (eC.inv.hom.comp ((φ'.restrictScalars R).comp eA.hom.hom)))
    rw [local_comp]
    rw [local_comp (M := A) (N := B) (T := D) (f i) eA.hom.hom
      (φ'.restrictScalars R)]
    exact heC.comp (hφ.comp heA)
  obtain ⟨Y, hQ, μ, hμ, hμchart⟩ :=
    exists_replace_prime (algebraMap R S) f (Can.obj P₀) Q₀ γ hγ
  obtain ⟨T, ⟨θ⟩⟩ := hess Y
  obtain ⟨ψ, hψ⟩ := (hfull P₀ T).2 (CategoryTheory.CategoryStruct.comp μ θ.inv)
  let β : S ⊗[R] T ≃ₗ[S] Q :=
    (((CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).symm.trans
      ((primeFunctor (algebraMap R S) f).mapIso θ)).trans
      (CategoryTheory.eqToIso hQ)).toLinearEquiv
  refine ⟨T, ψ.hom, β, ?_, ?_⟩
  · have hprime := transport_map ((hobj P₀).1.trans (hext P₀))
      ((hobj T).1.trans (hext T)) (Can.map ψ).prime (ψ.hom.baseChange S)
      ((hmap P₀ T ψ).1.trans
        (extendMap_algebra_heq (algebraMap R S) toAlgebra_algebraMap ψ.hom))
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun hprime x
    rw [hψ] at he
    change (CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).hom.hom
      (θ.inv.prime (μ.prime (eP.inv.hom x))) = (ψ.hom.baseChange S) x at he
    change (CategoryTheory.eqToIso hQ).hom.hom
      (θ.hom.prime ((CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).inv.hom
        ((ψ.hom.baseChange S) x))) = φ' x
    rw [← he]
    have hcT := (CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).toLinearEquiv.symm_apply_apply
      (θ.inv.prime (μ.prime (eP.inv.hom x)))
    change (CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).inv.hom
      ((CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).hom.hom
        (θ.inv.prime (μ.prime (eP.inv.hom x)))) =
      θ.inv.prime (μ.prime (eP.inv.hom x)) at hcT
    rw [hcT]
    have hθ := LinearMap.congr_fun
      (congrArg (fun h ↦ h.prime) θ.inv_hom_id) (μ.prime (eP.inv.hom x))
    change θ.hom.prime (θ.inv.prime (μ.prime (eP.inv.hom x))) =
      μ.prime (eP.inv.hom x) at hθ
    rw [hθ]
    have hm := LinearMap.congr_fun hμ (eP.inv.hom x)
    dsimp only [LinearMap.comp_apply] at hm
    rw [hm]
    change φ' (eP.hom.hom (eP.inv.hom x)) = φ' x
    exact congrArg φ' (eP.toLinearEquiv.apply_symm_apply x)
  · apply torsion_of_local_bijective I hI f hf' ψ.hom
    intro i
    have hl : ∀ M : ModuleCat.{max u v w} R,
        piece (f i) (ModuleCat.of (Localization.Away (f i))
          (LocalizedModule.Away (f i) M)) = localize (f i) M := by
      intro M
      exact restrict_algebraMap (R := R) (S := Localization.Away (f i)) _
    have hc := transport_map
      ((congrArg (piece (f i)) ((hobj P₀).2.1 i)).trans (hl P₀))
      ((congrArg (piece (f i)) ((hobj T).2.1 i)).trans (hl T))
      ((Can.map ψ).chart i) (localMap (f i) ψ.hom) ((hmap P₀ T ψ).2 i)
    rw [← hc, hψ]
    have hθ : Function.Bijective (θ.inv.chart i) :=
      ((chartFunctor (algebraMap R S) f i).mapIso θ).symm.toLinearEquiv.bijective
    exact (CategoryTheory.eqToIso ((congrArg (piece (f i)) ((hobj T).2.1 i)).trans
      (hl T))).toLinearEquiv.bijective.comp
      ((hθ.comp (hμchart i)).comp
        (CategoryTheory.eqToIso ((congrArg (piece (f i)) ((hobj P₀).2.1 i)).trans
          (hl P₀))).symm.toLinearEquiv.bijective)

end FormalGlueing
