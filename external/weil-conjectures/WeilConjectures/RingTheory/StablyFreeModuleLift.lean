/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.Prod
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal

/-!
# Lifting a finite stably free module

Source: Stacks Project, More on Algebra, Tag 0BC5.
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

private theorem lift_reduced_map {R : Type u} [CommRing R] (I : Ideal R)
    (M N : ModuleCat.{max u v} R) [Module.Projective R M]
    (a : ((R ⧸ I) ⊗[R] M) →ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] N)) :
    ∃ f : M →ₗ[R] N, f.baseChange (R ⧸ I) = a := by
  let qN : N →ₗ[R] (R ⧸ I) ⊗[R] N := TensorProduct.mk R (R ⧸ I) N 1
  have hqN : Function.Surjective qN := by
    intro t
    let eqN := TensorProduct.quotTensorEquivQuotSMul N I
    obtain ⟨n, hn⟩ := (I • (⊤ : Submodule R N)).mkQ_surjective (eqN t)
    refine ⟨n, eqN.injective ?_⟩
    change eqN ((1 : R ⧸ I) ⊗ₜ[R] n) = eqN t
    change Submodule.Quotient.mk n = eqN t at hn
    simpa only [eqN, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using hn
  obtain ⟨f, hf⟩ := Module.projective_lifting_property qN
    (a.restrictScalars R ∘ₗ TensorProduct.mk R (R ⧸ I) M 1) hqN
  refine ⟨f, ?_⟩
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro s m
  have hm := DFunLike.congr_fun hf m
  change (1 : R ⧸ I) ⊗ₜ[R] f m = a ((1 : R ⧸ I) ⊗ₜ[R] m) at hm
  change s ⊗ₜ[R] f m = a (s ⊗ₜ[R] m)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← a.map_smul]
    using congrArg (s • ·) hm

/-- A finite stably free module over a Jacobson quotient lifts to a finite stably free module.
Source: Stacks Project, More on Algebra, Tag 0BC5 (lemma-lift-stably-free)
(blueprint: lem-sc-finite-stably-free-module-lift).

Proof: Choose a finite free complement F such that E × F is finite free. Choose free
R-modules A and B with bases indexed by bases of E × F and F; their reductions are
isomorphic to these modules. Lift the reduced projection E × F → F to f : A → B
by projectivity of A and surjectivity of B → B/IB. The reduction of f is surjective,
so Nakayama makes f surjective. The free target B supplies a section g. Let P = ker f.
The splitting A ≃ P × B shows P is finite stably free. The kernel inclusion has a
left inverse, so its base change is injective. Tensor right exactness identifies its
image with the kernel of the reduced projection. Projection onto E then gives a
linear equivalence (R/I) ⊗ P ≃ E, and hence the requested module isomorphism.
This is the kernel construction in Tag 0BC5, obtaining the splitting directly by
Nakayama and projectivity instead of normalizing a separately lifted section.
Zero rings and empty basis indices require no separate choice or nontriviality hypothesis. -/
theorem exists_finite_stablyFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    (E : ModuleCat.{max u v} (R ⧸ I))
    [Module.Finite (R ⧸ I) E] [Module.IsStablyFree (R ⧸ I) E] :
    ∃ P : ModuleCat.{max u v} R,
      (Module.Finite R P ∧ Module.IsStablyFree R P) ∧
      Nonempty (E ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P) := by
  classical
  obtain ⟨F, _, _, hFfin, hFfree, hEFfree⟩ := Module.IsStablyFree.exist_free_prod (R ⧸ I) E
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) (E × F)
  let κ := ULift.{v} (Module.Free.ChooseBasisIndex (R ⧸ I) F)
  let bEF := Module.Free.chooseBasis (R ⧸ I) (E × F)
  let bF : Module.Basis κ (R ⧸ I) F :=
    (Module.Free.chooseBasis (R ⧸ I) F).reindex Equiv.ulift.symm
  let A := ι →₀ R
  let B := κ →₀ R
  let bA : Module.Basis ι R A := Finsupp.basisSingleOne
  let bB : Module.Basis κ R B := Finsupp.basisSingleOne
  let eA : ((R ⧸ I) ⊗[R] A) ≃ₗ[R ⧸ I] (E × F) :=
    (bA.baseChange (R ⧸ I)).repr ≪≫ₗ bEF.repr.symm
  let eB : ((R ⧸ I) ⊗[R] B) ≃ₗ[R ⧸ I] F :=
    (bB.baseChange (R ⧸ I)).repr ≪≫ₗ bF.repr.symm
  let a : ((R ⧸ I) ⊗[R] A) →ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] B) :=
    eB.symm.toLinearMap ∘ₗ LinearMap.snd (R ⧸ I) E F ∘ₗ eA.toLinearMap
  obtain ⟨f, hf⟩ := lift_reduced_map I (ModuleCat.of R A) (ModuleCat.of R B) a
  have haredsurj : Function.Surjective a := by
    intro t
    refine ⟨eA.symm (0, eB t), ?_⟩
    simp [a]
  have hfsurj : Function.Surjective f :=
    surjective_of_extendScalars_mod_ideal I hunits (ModuleCat.of R A) (ModuleCat.of R B)
      (ModuleCat.ofHom f)
      (by change Function.Surjective (f.baseChange (R ⧸ I)); rw [hf]; exact haredsurj)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hfsurj
  let K := LinearMap.ker f
  let p : A →ₗ[R] K :=
    (LinearMap.id - g.comp f).codRestrict K (by
      intro x
      change f (x - g (f x)) = 0
      have hx := DFunLike.congr_fun hg (f x)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, map_sub] using sub_eq_zero.mpr hx.symm)
  have hpi : p.comp K.subtype = LinearMap.id := by
    ext x
    simp [p, K, LinearMap.mem_ker.mp x.property]
  have hpfin : Module.Finite R K := Module.Finite.of_surjective p (by
    intro k
    refine ⟨k.val, ?_⟩
    exact DFunLike.congr_fun hpi k)
  let split : K × B →ₗ[R] A := K.subtype.coprod g
  have hsplit : Function.Bijective split := by
    constructor
    · intro x y h
      have hxy : x.2 = y.2 := by
        have hh := congrArg f h
        have hx := DFunLike.congr_fun hg x.2
        have hy := DFunLike.congr_fun hg y.2
        change f (x.1.val + g x.2) = f (y.1.val + g y.2) at hh
        change f (g x.2) = x.2 at hx
        change f (g y.2) = y.2 at hy
        simpa only [map_add, LinearMap.mem_ker.mp x.1.property,
          LinearMap.mem_ker.mp y.1.property, hx, hy, zero_add] using hh
      apply Prod.ext
      · apply Subtype.ext
        have hh : x.1.val + g x.2 = y.1.val + g x.2 := by simpa [split, hxy] using h
        exact add_right_cancel hh
      · exact hxy
    · intro x
      refine ⟨(p x, f x), ?_⟩
      simp [split, p]
  have : Module.Free R (K × B) :=
    Module.Free.of_equiv (LinearEquiv.ofBijective split hsplit).symm
  have hKsf : Module.IsStablyFree R K := Module.IsStablyFree.of_free_prod R K B
  let i := K.subtype
  let u := i.baseChange (R ⧸ I)
  have hui : Function.Injective u := by
    have hi : (p.baseChange (R ⧸ I)).comp u = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
    intro x y h
    have hh := congrArg (p.baseChange (R ⧸ I)) h
    simpa only [← LinearMap.comp_apply, hi, LinearMap.id_apply] using hh
  have huexact : Function.Exact u (f.baseChange (R ⧸ I)) :=
    lTensor_exact (R ⧸ I) f.exact_subtype_ker_map hfsurj
  have hzero : ∀ t, (eA (u t)).2 = 0 := by
    intro t
    have ht := huexact.apply_apply_eq_zero t
    rw [hf] at ht
    have hh := congrArg eB ht
    simpa [a] using hh
  let kmap : ((R ⧸ I) ⊗[R] K) →ₗ[R ⧸ I] E :=
    LinearMap.fst (R ⧸ I) E F ∘ₗ eA.toLinearMap ∘ₗ u
  have hkmap : Function.Bijective kmap := by
    constructor
    · intro x y h
      apply hui
      apply eA.injective
      exact Prod.ext h ((hzero x).trans (hzero y).symm)
    · intro x
      let t := eA.symm (x, 0)
      have ht : (f.baseChange (R ⧸ I)) t = 0 := by simp [hf, a, t]
      obtain ⟨z, hz⟩ := (huexact t).mp ht
      refine ⟨z, ?_⟩
      change (eA (u z)).1 = x
      rw [hz]
      simp [t]
  refine ⟨ModuleCat.of R K, ⟨hpfin, hKsf⟩, ?_⟩
  exact ⟨(LinearEquiv.toModuleIso (LinearEquiv.ofBijective kmap hkmap)).symm⟩

end ModuleCat
