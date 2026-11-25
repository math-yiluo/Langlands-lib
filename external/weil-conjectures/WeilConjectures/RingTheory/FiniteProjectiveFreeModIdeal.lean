/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal

/-!
# Freeness of a finite projective module detected modulo an ideal

Source: Stacks Project, More on Algebra, Tag 0BC6.
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

/-- A finite projective module with free reduction over a Jacobson quotient is free.
Source: Stacks Project, More on Algebra, Tag 0BC6 (lemma-lift-isomorphism)
(blueprint: lem-sc-finite-projective-free-mod-ideal).

Proof: Choose a finite basis of the reduction and the free R-module A with the same
basis index. Lift the resulting map A → P/IP through P → P/IP by projectivity of A.
The reduced map is the basis isomorphism, so Nakayama makes the lift f : A → P
surjective. Since P is projective, choose a section g : P → A. Reduction gives
f̄ ḡ = id, and injectivity of f̄ gives ḡ f̄ = id. Nakayama therefore makes gf
surjective. A surjective endomorphism of a finite module over a commutative ring is
injective (the Orzech property). Consequently f is injective, hence bijective, and
its linear equivalence transfers freeness from A to P. This is the isomorphism-lifting
argument of Tag 0BC6, using the splitting instead of a separately lifted inverse.
The zero ring and empty basis cases are included by the same construction. -/
theorem free_of_free_extendScalars_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    (P : ModuleCat.{max u v} R) [Module.Finite R P] [Module.Projective R P]
    [Module.Free (R ⧸ I) ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)] :
    Module.Free R P := by
  classical
  have hfin : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] P) := inferInstance
  have hfree : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] P) :=
    ‹Module.Free (R ⧸ I) ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)›
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) ((R ⧸ I) ⊗[R] P)
  let b := Module.Free.chooseBasis (R ⧸ I) ((R ⧸ I) ⊗[R] P)
  let A := ι →₀ R
  let bA : Module.Basis ι R A := Finsupp.basisSingleOne
  let e : ((R ⧸ I) ⊗[R] A) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P) :=
    (bA.baseChange (R ⧸ I)).repr ≪≫ₗ b.repr.symm
  let qP : P →ₗ[R] (R ⧸ I) ⊗[R] P := TensorProduct.mk R (R ⧸ I) P 1
  have hqP : Function.Surjective qP := by
    intro t
    let eqP := TensorProduct.quotTensorEquivQuotSMul P I
    obtain ⟨p, hp⟩ := (I • (⊤ : Submodule R P)).mkQ_surjective (eqP t)
    refine ⟨p, eqP.injective ?_⟩
    change eqP ((1 : R ⧸ I) ⊗ₜ[R] p) = eqP t
    change Submodule.Quotient.mk p = eqP t at hp
    simpa only [qP, eqP, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using hp
  let a : A →ₗ[R] (R ⧸ I) ⊗[R] P :=
    e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R (R ⧸ I) A 1
  obtain ⟨f, hf⟩ := Module.projective_lifting_property qP a hqP
  have hfe : f.baseChange (R ⧸ I) = e.toLinearMap := by
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro s m
    have hm := DFunLike.congr_fun hf m
    change (1 : (R ⧸ I)) ⊗ₜ[R] f m = e ((1 : (R ⧸ I)) ⊗ₜ[R] m) at hm
    change s ⊗ₜ[R] f m = e (s ⊗ₜ[R] m)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← e.map_smul]
      using congrArg (s • ·) hm
  have hfsurj : Function.Surjective f :=
    surjective_of_extendScalars_mod_ideal I hunits (ModuleCat.of R A) P (ModuleCat.ofHom f)
      (by change Function.Surjective (f.baseChange (R ⧸ I)); rw [hfe]; exact e.surjective)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hfsurj
  have hgfreduce : (g.comp f).baseChange (R ⧸ I) = LinearMap.id := by
    have hfgreduce : (f.baseChange (R ⧸ I)).comp (g.baseChange (R ⧸ I)) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hg, LinearMap.baseChange_id]
    rw [LinearMap.baseChange_comp]
    apply LinearMap.ext
    intro t
    apply e.injective
    have ht := DFunLike.congr_fun hfgreduce ((f.baseChange (R ⧸ I)) t)
    change (f.baseChange (R ⧸ I)) ((g.baseChange (R ⧸ I))
      ((f.baseChange (R ⧸ I)) t)) = (f.baseChange (R ⧸ I)) t at ht
    simpa only [hfe, LinearEquiv.coe_coe, LinearMap.comp_apply, LinearMap.id_apply] using ht
  have hgfsurj : Function.Surjective (g.comp f) :=
    surjective_of_extendScalars_mod_ideal I hunits (ModuleCat.of R A) (ModuleCat.of R A)
      (ModuleCat.ofHom (g.comp f))
      (by change Function.Surjective ((g.comp f).baseChange (R ⧸ I))
          rw [hgfreduce]; exact Function.surjective_id)
  have hgfinj := OrzechProperty.injective_of_surjective_endomorphism (g.comp f) hgfsurj
  have hfinj : Function.Injective f := fun x y h ↦ hgfinj (congrArg g h)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩)

end ModuleCat
