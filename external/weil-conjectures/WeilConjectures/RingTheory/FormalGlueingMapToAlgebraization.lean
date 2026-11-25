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
import WeilConjectures.RingTheory.IdealPowerTorsionLocalizationCriterion
import WeilConjectures.RingTheory.FormalGlueingReplacePrimeTo

/-!
# Algebraization of a map that is an isomorphism away from an ideal

Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (1),
using Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-to-algebraization).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private def primeFunctor (φ : R →+* S) {t : ℕ} (f : Fin t → R) :
    CategoryTheory.Functor (Data.{u, v, max u v w} φ f) (ModuleCat.{max u v w} S) where
  obj X := X.M'
  map a := ModuleCat.ofHom a.prime

private noncomputable def chartFunctor (φ : R →+* S) {t : ℕ} (f : Fin t → R) (i : Fin t) :
    CategoryTheory.Functor (Data.{u, v, max u v w} φ f) (ModuleCat.{max u v w} R) where
  obj X := piece (f i) (X.M i)
  map {X Y} a := ModuleCat.ofHom (X := piece (f i) (X.M i))
    (Y := piece (f i) (Y.M i)) (a.chart i)

private theorem apply_eq_of_heq {A B A' B' : ModuleCat.{w} S}
    (ha : A = A') (hb : B = B') (h : A →ₗ[S] B) (g : A' →ₗ[S] B')
    (hg : HEq h g) (x : A) :
    (CategoryTheory.eqToIso hb).hom (h x) = g ((CategoryTheory.eqToIso ha).hom x) := by
  subst A'
  subst B'
  cases hg
  rfl

private theorem restrict_of_eq (A : Type w) [AddCommGroup A] [Module S A]
    [Module R A] [IsScalarTower R S A] :
    restrict (algebraMap R S) (ModuleCat.of S A) = ModuleCat.of R A := by
  have hm : Module.compHom A (algebraMap R S) = ‹Module R A› :=
    Module.ext' _ _ fun r x => algebraMap_smul S r x
  exact congrArg (fun m : Module R A => @ModuleCat.of R _ A _ m) hm

private theorem restrictMap_algebraMap {A B : Type w}
    [AddCommGroup A] [AddCommGroup B] [Module S A] [Module S B]
    [Module R A] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
    (h : A →ₗ[S] B) :
    HEq (restrictMap (algebraMap R S) (M := ModuleCat.of S A)
      (N := ModuleCat.of S B) h) (h.restrictScalars R) := by
  have hma : Module.compHom A (algebraMap R S) = ‹Module R A› :=
    Module.ext' _ _ fun r x => algebraMap_smul S r x
  have hmb : Module.compHom B (algebraMap R S) = ‹Module R B› :=
    Module.ext' _ _ fun r x => algebraMap_smul S r x
  cases hma
  cases hmb
  rfl

private theorem bijective_of_heq {A B A' B' : ModuleCat.{w} S}
    (ha : A = A') (hb : B = B') (h : A →ₗ[S] B) (g : A' →ₗ[S] B')
    (hg : HEq h g) (hh : Function.Bijective h) : Function.Bijective g := by
  subst A'
  subst B'
  cases hg
  exact hh

private theorem localMap_bijective (r : R) {A B : ModuleCat.{w} R}
    (h : A →ₗ[R] B) (hh : Function.Bijective h) :
    Function.Bijective (localMap r h) := by
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) B)).mpr
  exact ⟨LocalizedModule.map_injective _ h hh.1, LocalizedModule.map_surjective _ h hh.2⟩

private theorem localMap_bijective_of_heq (r : R)
    {A B A' B' : ModuleCat.{w} R}
    (ha : A = A') (hb : B = B') (h : A →ₗ[R] B) (g : A' →ₗ[R] B')
    (hg : HEq h g) (hh : Function.Bijective (localMap r h)) :
    Function.Bijective (localMap r g) := by
  subst A'
  subst B'
  cases hg
  exact hh

private theorem localMap_comp (r : R) {A B C : ModuleCat.{w} R}
    (h : A →ₗ[R] B) (k : B →ₗ[R] C) :
    localMap r (k.comp h) = (localMap r k).comp (localMap r h) :=
  IsLocalizedModule.map_comp' (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) B)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) C) h k

private theorem extend_algebraMap (M : ModuleCat.{w} R) :
    extend (algebraMap R S) M = ModuleCat.of S (S ⊗[R] M) := by
  generalize he : algebraMap R S = φ
  have ha : φ.toAlgebra = ‹Algebra R S› := by rw [← he]; exact toAlgebra_algebraMap
  unfold extend
  cases ha
  rfl

private theorem extendMap_algebraMap {M N : ModuleCat.{w} R} (h : M →ₗ[R] N) :
    HEq (extendMap (algebraMap R S) h) (h.baseChange S) := by
  generalize he : algebraMap R S = φ
  have ha : φ.toAlgebra = ‹Algebra R S› := by rw [← he]; exact toAlgebra_algebraMap
  unfold extendMap
  cases ha
  rfl

/-- Algebraize the map and retain ideal-power torsion of its kernel and cokernel.
Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (1),
with Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-to-algebraization).

Choose a finite generating family of I. At each generator f, every torsion element
vanishes after localization: an annihilating ideal power supplies an annihilating
power of f. Exact localization therefore makes the given map bijective on each
chart. Start with the canonical datum of P, replace its S-component by Q, and
compose its comparison with the localized given map.
The overlap and cocycle identities follow from those for the canonical datum and
naturality of localization. The given map and the identity chart maps form a
morphism of data to the canonical datum. Essential surjectivity of the canonical equivalence
algebraizes the modified datum. Fullness algebraizes that morphism; its first
component gives the displayed factorization, and each chart component is an
isomorphism. Exact localization now makes the kernel and cokernel of the descended
map vanish on every chart. For any element choose positive exponents e_i killing
it at the finitely many generators. Every monomial of degree 1 + sum e_i contains
one generator to at least its e_i-th power, so that power of I kills the element.
If there are no generators then I = 0, and its first power already kills every
element. This proves both torsion assertions. No comparison equivalence is asserted
here; those are proved separately using flat tensor exactness and torsion base change.
-/
theorem exists_map_to_algebraization
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (P : Type (max u v w)) [AddCommGroup P] [Module R P]
    (Q : Type (max u v w)) [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q]
    (φ' : Q →ₗ[S] S ⊗[R] P)
    (hker : ∀ x : (φ'.restrictScalars R).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : _ ⧸ (φ'.restrictScalars R).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ T : ModuleCat.{max u v w} R,
      ∃ (ψ : T →ₗ[R] P) (β : Q ≃ₗ[S] S ⊗[R] T),
        (ψ.baseChange S).comp β.toLinearMap = φ' ∧
        (∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∀ x : P ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) := by
  classical
  obtain ⟨t, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hfI : Ideal.span (Set.range f) = I := hf
  obtain ⟨_, Can, hobj, hmap, hdesc⟩ :=
    exists_canonical_equivalence.{u, v, w} (algebraMap R S) t f
  obtain ⟨hfull, hess⟩ := hdesc hflat (by rw [hfI]; exact hquot)
  let P₀ : ModuleCat.{max u v w} R := ModuleCat.of R P
  let Q₀ : ModuleCat.{max u v w} S := ModuleCat.of S Q
  have hext (M : ModuleCat.{max u v w} R) :
      extend (algebraMap R S) M = ModuleCat.of S (S ⊗[R] M) := by
    exact extend_algebraMap M
  let cP := (CategoryTheory.eqToIso ((hobj P₀).1.trans (hext P₀))).toLinearEquiv
  let a : Q₀ →ₗ[S] (Can.obj P₀).M' := cP.symm.toLinearMap.comp φ'
  have hloc : ∀ i : Fin t, Function.Bijective
      (localMap (f i) (restrictMap (algebraMap R S) a)) := by
    intro i
    have hφ := (idealPowerTorsion_iff_localMap_bijective t f
      (φ'.restrictScalars R)).mp (by simpa only [hfI] using And.intro hker hcoker) i
    have hφ₀ : Function.Bijective
        (localMap (f i) (restrictMap (algebraMap R S)
          (M := Q₀) (N := ModuleCat.of S (S ⊗[R] P)) φ')) := by
      have hQ := restrict_of_eq (R := R) (S := S) Q
      have hP := restrict_of_eq (R := R) (S := S) (S ⊗[R] P)
      have hr := restrictMap_algebraMap (R := R) φ'
      exact localMap_bijective_of_heq (f i) hQ.symm hP.symm
        (φ'.restrictScalars R) _ hr.symm hφ
    have hc : Function.Bijective
        (restrictMap (algebraMap R S) cP.symm.toLinearMap) := cP.symm.bijective
    have hlc := localMap_bijective (f i)
      (restrictMap (algebraMap R S) cP.symm.toLinearMap) hc
    have he : localMap (f i) (restrictMap (algebraMap R S) a) =
        (localMap (f i) (restrictMap (algebraMap R S) cP.symm.toLinearMap)).comp
          (localMap (f i) (restrictMap (algebraMap R S)
            (M := Q₀) (N := ModuleCat.of S (S ⊗[R] P)) φ')) :=
      localMap_comp (f i)
        (restrictMap (algebraMap R S) (M := Q₀)
          (N := ModuleCat.of S (S ⊗[R] P)) φ')
        (restrictMap (algebraMap R S) cP.symm.toLinearMap)
    rw [he]
    exact hlc.comp hφ₀
  obtain ⟨X, aX, eQ, haX, hcharts⟩ :=
    exists_replace_prime_to (algebraMap R S) f (Can.obj P₀) Q₀ a hloc
  obtain ⟨T, ⟨e⟩⟩ := hess X
  obtain ⟨ψ, hψ⟩ := (hfull T P₀).2 (CategoryTheory.CategoryStruct.comp e.hom aX)
  let eT := ((primeFunctor (algebraMap R S) f).mapIso e).toLinearEquiv
  let cT := (CategoryTheory.eqToIso ((hobj T).1.trans (hext T))).toLinearEquiv
  let β : Q ≃ₗ[S] S ⊗[R] T := eQ.symm.trans (eT.symm.trans cT)
  have hfactor : (ψ.hom.baseChange S).comp β.toLinearMap = φ' := by
    ext q
    have hmapψ : HEq (Can.map ψ).prime (ψ.hom.baseChange S) := by
      exact (hmap T P₀ ψ).1.trans (extendMap_algebraMap ψ.hom)
    have hh := apply_eq_of_heq ((hobj T).1.trans (hext T))
      ((hobj P₀).1.trans (hext P₀))
      (Can.map ψ).prime (ψ.hom.baseChange S) hmapψ
      (eT.symm (eQ.symm q))
    rw [hψ] at hh
    change cP (aX.prime (eT (eT.symm (eQ.symm q)))) =
      (ψ.hom.baseChange S) (cT (eT.symm (eQ.symm q))) at hh
    rw [eT.apply_symm_apply, haX] at hh
    change (ψ.hom.baseChange S) (cT (eT.symm (eQ.symm q))) = φ' q
    replace hh := hh.symm
    change (ψ.hom.baseChange S) (cT (eT.symm (eQ.symm q))) =
      cP (cP.symm (φ' (eQ (eQ.symm q)))) at hh
    rw [eQ.apply_symm_apply, cP.apply_symm_apply] at hh
    exact hh
  have hψloc : ∀ i : Fin t, Function.Bijective (localMap (f i) ψ.hom) := by
    intro i
    have hc := (hmap T P₀ ψ).2 i
    rw [hψ] at hc
    have he : Function.Bijective (e.hom.chart i) :=
      ((chartFunctor (algebraMap R S) f i).mapIso e).toLinearEquiv.bijective
    have hb : Function.Bijective
        ((CategoryTheory.CategoryStruct.comp e.hom aX).chart i) := (hcharts i).comp he
    apply bijective_of_heq
      ((congrArg (piece (f i)) ((hobj T).2.1 i)).trans
        (restrict_of_eq (S := Localization.Away (f i)) (LocalizedModule.Away (f i) T)))
      ((congrArg (piece (f i)) ((hobj P₀).2.1 i)).trans
        (restrict_of_eq (S := Localization.Away (f i)) (LocalizedModule.Away (f i) P₀)))
      _ _ hc hb
  have htors := (idealPowerTorsion_iff_localMap_bijective t f ψ.hom).mpr hψloc
  exact ⟨T, ψ.hom, β, hfactor, by simpa only [hfI] using htors⟩

end FormalGlueing
