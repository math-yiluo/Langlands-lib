/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.LimitFlatModules
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Flatness of completed flat modules

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0AGW (lemma-flat-after-completion).
(blueprint: lem-weil-pbc-flat-module-completion-flat)
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite in
private def quotientTower {A : Type u} [CommRing A] (J : Ideal A)
    (N : Type v) [AddCommGroup N] [Module A N] : ℕᵒᵖ ⥤ ModuleCat.{v} A where
  obj n := ModuleCat.of A (N ⧸ (J ^ (n.unop + 1) • ⊤ : Submodule A N))
  map f := ModuleCat.ofHom (Submodule.factorPow J N (Nat.add_le_add_right f.unop.le 1))
  map_id n := by
    apply ModuleCat.hom_ext
    exact Submodule.mapQ_id _
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (Submodule.factor_comp
      (Submodule.pow_smul_top_le J N (Nat.add_le_add_right f.unop.le 1))
      (Submodule.pow_smul_top_le J N (Nat.add_le_add_right g.unop.le 1))).symm

open CategoryTheory CategoryTheory.Limits Opposite in
private def quotientCone {A : Type u} [CommRing A] (J : Ideal A)
    (N : Type v) [AddCommGroup N] [Module A N] : Cone (quotientTower J N) where
  pt := ModuleCat.of A N
  π :=
    { app n := ModuleCat.ofHom (Submodule.mkQ (J ^ (n.unop + 1) • ⊤))
      naturality := fun _ _ f ↦ by
        apply ModuleCat.hom_ext
        exact (Submodule.factor_comp_mk
          (Submodule.pow_smul_top_le J N (Nat.add_le_add_right f.unop.le 1))).symm }

open CategoryTheory CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def quotientConeIsLimit {A : Type u} [CommRing A] (J : Ideal A)
    (N : Type v) [AddCommGroup N] [Module A N] [IsAdicComplete J N] :
    IsLimit (quotientCone J N) := by
  let ha : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1
  let f (s : Cone (quotientTower J N)) (n : ℕ) :
      s.pt →ₗ[A] N ⧸ (J ^ (n + 1) • ⊤ : Submodule A N) := (s.π.app (op n)).hom
  have hf (s : Cone (quotientTower J N)) {n : ℕ} :
      Submodule.factorPow J N (ha.monotone n.le_succ) ∘ₗ f s (n + 1) = f s n := by
    simpa [f, quotientTower] using
      congrArg ModuleCat.Hom.hom (s.π.naturality (homOfLE n.le_succ).op).symm
  let lift (s : Cone (quotientTower J N)) : s.pt ⟶ (quotientCone J N).pt :=
    ModuleCat.ofHom (IsAdicComplete.StrictMono.lift J ha (f s) (hf s))
  refine
    { lift := lift
      fac := ?_
      uniq := ?_ }
  · intro s n
    apply ModuleCat.hom_ext
    exact IsAdicComplete.StrictMono.mkQ_comp_lift J ha (f s) (hf s) (n := n.unop)
  · intro s m hm
    apply ModuleCat.hom_ext
    apply IsAdicComplete.StrictMono.eq_lift J ha (f s) (hf s)
    intro n
    exact congrArg ModuleCat.Hom.hom (hm (op n))

namespace AdicCompletion

set_option backward.isDefEq.respectTransparency false in
/-- The quotients of a completed flat module are flat over the corresponding quotients
of the completed ring.

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0AGW,
Steps 1--3 of the specialized proof for a flat module over a Noetherian ring.
(blueprint: lem-weil-pbc-flat-module-completion-flat)

Proof: Put A = AdicCompletion I R and J = I A. Finite generation of I identifies
A/J^n with R/I^n, by the surjective evaluation map whose kernel is I^n A = J^n.
Similarly, evaluation identifies (AdicCompletion I M)/J^n(AdicCompletion I M) with
M/I^n M; the kernel formula holds for arbitrary M when I is finitely generated.
The scalar tower identifies the R-submodule I^n(AdicCompletion I M) with the restriction
of J^n(AdicCompletion I M). On representatives the quotient actions agree because
completion scalar multiplication is componentwise. Flat base change identifies M/I^n M
with the flat R/I^n-module (R/I^n) tensor M. Transport this flatness along the ring and
module identifications above. For n = 0 both quotient rings and modules are zero, so
this argument also covers that case. -/
private theorem flat_completed_quotients
    (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] [IsNoetherianRing R] [Module.Flat R M] :
    ∀ n : ℕ,
      Module.Flat
        (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (AdicCompletion I M ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n •
          (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I M))) := by
  classical
  intro n
  let A := AdicCompletion I R
  let J := I.map (algebraMap R A)
  let N := AdicCompletion I M
  let P := (J ^ n • ⊤ : Submodule A N)
  let Q := M ⧸ (I ^ n • ⊤ : Submodule R M)
  have hker : RingHom.ker (evalₐ I n).toRingHom = J ^ n := by
    ext x
    rw [RingHom.mem_ker]
    rw [← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)]
    change (evalₐ I n) x = 0 ↔ eval I R n x = 0
    let e₀ := Ideal.quotientEquivAlgOfEq R
      (show (I ^ n • ⊤ : Ideal R) = I ^ n by simp)
    change e₀ (eval I R n x) = 0 ↔ eval I R n x = 0
    exact map_eq_zero_iff e₀ e₀.injective
  let eA : A ⧸ J ^ n ≃+* R ⧸ I ^ n :=
    (Ideal.quotEquivOfEq hker.symm).trans
      ((evalₐ I n).toRingHom.quotientKerEquivOfSurjective (surjective_evalₐ I n))
  have heA (x : A) : eA (Ideal.Quotient.mk (J ^ n) x) = evalₐ I n x := by
    change (evalₐ I n).toRingHom.quotientKerEquivOfSurjective
      (surjective_evalₐ I n) (Ideal.Quotient.mk _ x) = _
    exact RingHom.quotientKerEquivOfSurjective_apply_mk _ _
  have hP : P.restrictScalars R = (eval I M n).ker := by
    dsimp only [P]
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
    exact pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)
  let eN : (N ⧸ P) ≃ₗ[R] Q :=
    (Submodule.Quotient.restrictScalarsEquiv R P).symm.trans
      ((Submodule.quotEquivOfEq _ _ hP).trans
        ((eval I M n).quotKerEquivOfSurjective (eval_surjective I M n)))
  let eT := TensorProduct.quotTensorEquivQuotSMul M (I ^ n)
  have eTlinear : ∀ (r : R ⧸ I ^ n) x, eT (r • x) = r • eT x := by
    intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    change eT ((algebraMap R (R ⧸ I ^ n) r) • x) = r • eT x
    rw [algebraMap_smul (R ⧸ I ^ n) r x]
    exact eT.map_smul r x
  let eTQ := eT.toAddEquiv.toLinearEquiv eTlinear
  have : Module.Flat (R ⧸ I ^ n) Q := Module.Flat.of_linearEquiv eTQ.symm
  let : Algebra (A ⧸ J ^ n) (R ⧸ I ^ n) := eA.toRingHom.toAlgebra
  let : Module (A ⧸ J ^ n) Q := Module.compHom Q eA.toRingHom
  have : IsScalarTower (A ⧸ J ^ n) (R ⧸ I ^ n) Q := ⟨fun _ _ _ => mul_smul _ _ _⟩
  have : Module.Flat (A ⧸ J ^ n) (R ⧸ I ^ n) :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective eA.bijective)
  have : Module.Flat (A ⧸ J ^ n) Q := Module.Flat.trans _ (R ⧸ I ^ n) _
  have eNlinear : ∀ (r : A ⧸ J ^ n) x, eN (r • x) = r • eN x := by
    intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P x
    have heN (y : N) : eN (Submodule.Quotient.mk (p := P) y) = eval I M n y := by
      simp only [eN, LinearEquiv.trans_apply,
        Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk]
      exact LinearMap.quotKerEquivOfSurjective_apply_mk (eval I M n) (eval_surjective I M n) y
    change eN (Submodule.Quotient.mk (p := P) (r • x)) =
      eA (Ideal.Quotient.mk (J ^ n) r) • eN (Submodule.Quotient.mk (p := P) x)
    rw [heN, heN, heA]
    exact val_smul_eq_evalₐ_smul I n r (eval I M n x)
  exact Module.Flat.of_linearEquiv (eN.toAddEquiv.toLinearEquiv eNlinear)

end AdicCompletion

namespace Module

/-- The adic completion of a flat module over a Noetherian ring is flat over the completed ring.

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0AGW (lemma-flat-after-completion).
(blueprint: lem-weil-pbc-flat-module-completion-flat)

Proof: For every positive `n`, flat base change identifies `M / I ^ n M` with a flat
`R / I ^ n`-module. The completion of a Noetherian ring is Noetherian, and its quotient by
the `n`-th power of the extended ideal is `R / I ^ n`. Thus these quotients, viewed as
modules over the completed ring, are flat with surjective transition maps. The inverse
limit flatness lemma (Tag 0912) then gives flatness of `AdicCompletion I M` over
`AdicCompletion I R`, with the componentwise module structure.
-/
theorem flat_adicCompletion
    (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] [IsNoetherianRing R] [Module.Flat R M] :
    Module.Flat (AdicCompletion I R) (AdicCompletion I M) := by
  let A := AdicCompletion I R
  let J := I.map (algebraMap R A)
  let N := AdicCompletion I M
  let : IsNoetherianRing A := AdicCompletion.isNoetherianRing I
  let : IsAdicComplete I N := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
  let : IsAdicComplete J N := (IsAdicComplete.map_algebraMap_iff I N).mpr inferInstance
  let F := quotientTower J N
  let : ∀ n : ℕ, Module (A ⧸ J ^ (n + 1)) (F.obj (Opposite.op n)) :=
    fun n ↦ inferInstanceAs
      (Module (A ⧸ J ^ (n + 1)) (N ⧸ (J ^ (n + 1) • ⊤ : Submodule A N)))
  let : ∀ n : ℕ, IsScalarTower A (A ⧸ J ^ (n + 1)) (F.obj (Opposite.op n)) :=
    fun n ↦ inferInstanceAs
      (IsScalarTower A (A ⧸ J ^ (n + 1)) (N ⧸ (J ^ (n + 1) • ⊤ : Submodule A N)))
  have hflat (n : ℕ) : Module.Flat (A ⧸ J ^ (n + 1)) (F.obj (Opposite.op n)) :=
    AdicCompletion.flat_completed_quotients R I M (n + 1)
  have hsurj (n : ℕ) :
      Function.Surjective (F.map (CategoryTheory.homOfLE (Nat.le_succ n)).op).hom := by
    exact Submodule.factor_surjective
      (Submodule.pow_smul_top_le J N (Nat.add_le_add_right (Nat.le_succ n) 1))
  have hF := (ModuleCat.limit_flat_of_flat_quotients.{u, v, u} A J F hflat hsurj).1
  let e := (quotientConeIsLimit J N).conePointUniqueUpToIso (CategoryTheory.Limits.limit.isLimit F)
  exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr hF

end Module
