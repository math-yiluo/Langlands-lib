/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.RankIdempotent
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian

/-!
# Retracts of constructible `ℓ`-adic sheaves

A retract of a lisse `ℓ`-adic sheaf is lisse, on an arbitrary scheme: on the members of a
trivialising cover, the retract is the kernel of `1 - p` for an idempotent endomorphism `p` of a
finite free module `ℚ̄_ℓⁿ`. The pointwise ranks of `p` and of `1 - p` add up to `n`
(`Matrix.rank_one_sub_add_rank_of_isIdempotentElem`) and are both lower semicontinuous, so they
are locally constant, and the kernel of `1 - p` is lisse
(`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_kernel_cokernel_of_isLocallyConstant`).
Consequently retracts of stratified lisse and of constructible sheaves are stratified lisse,
respectively constructible.

## Main results

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_retract`,
  `AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf.of_retract`,
  `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.of_retract`, and the instance
  `(adicConstructibleSheaf l X).IsStableUnderRetracts`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Retract

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C} (e : Retract X Y)

/-- A retract `X` of `Y` is a kernel of `𝟙 Y - e.r ≫ e.i`, through `e.i`. -/
noncomputable def isLimitKernelFork :
    IsLimit (KernelFork.ofι (f := 𝟙 Y - e.r ≫ e.i) e.i (by simp)) :=
  KernelFork.IsLimit.ofι _ _ (fun k _ ↦ k ≫ e.r)
    (fun k hk ↦ by
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hk
      rw [Category.assoc, ← hk])
    (fun k _ m hm ↦ by rw [← hm, Category.assoc, e.retract, Category.comp_id])

/-- A retract `X` of `Y` is isomorphic to the kernel of `𝟙 Y - e.r ≫ e.i`. -/
noncomputable def kernelIso [HasKernel (𝟙 Y - e.r ≫ e.i)] : kernel (𝟙 Y - e.r ≫ e.i) ≅ X :=
  (kernelIsKernel _).conePointUniqueUpToIso e.isLimitKernelFork

end CategoryTheory.Retract

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AdicSheaf

variable {V : Scheme.{u}} {ι κ : Type} [Fintype ι] [Fintype κ]

lemma unitMatrix_sub (ψ ψ' : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V) :
    unitMatrix (ψ - ψ') = unitMatrix ψ - unitMatrix ψ' := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, Preadditive.sub_comp, Preadditive.comp_sub, Matrix.sub_apply]
  exact unitEndFunAddHom.map_sub _ _

set_option linter.unusedFintypeInType false in
/-- For an idempotent endomorphism `p` of a finite free `ℚ̄_ℓ,V`-module, the kernel of `1 - p`
is lisse: the pointwise ranks of `p` and `1 - p` are lower semicontinuous and add up to the rank
of the module, so they are locally constant. -/
theorem isAdicLisseSheaf_kernel_one_sub_of_idempotent
    (p : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : ι ↦ unit l V) (hp : p ≫ p = p) :
    IsAdicLisseSheaf (kernel (𝟙 _ - p)) := by
  classical
  refine (isAdicLisseSheaf_kernel_cokernel_of_isLocallyConstant _ ?_).1
  have hM : unitMatrix (𝟙 _ - p) = 1 - unitMatrix p := by
    rw [unitMatrix_sub, unitMatrix_id]
  have hP : IsIdempotentElem (unitMatrix p) := by
    rw [IsIdempotentElem, ← unitMatrix_comp, hp]
  have hsum (t : V) :
      ((unitMatrix (𝟙 _ - p)).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank +
      ((unitMatrix p).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank = Fintype.card ι := by
    rw [hM, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    refine Matrix.rank_one_sub_add_rank_of_isIdempotentElem ?_
    rw [IsIdempotentElem, ← Matrix.map_mul, hP.eq]
  refine (IsLocallyConstant.iff_exists_open _).2 fun t ↦
    ⟨_, (PadicAlgCl.isOpen_setOf_le_rank (unitMatrix (𝟙 _ - p))
      ((unitMatrix (𝟙 _ - p)).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank).inter
      (PadicAlgCl.isOpen_setOf_le_rank (unitMatrix p)
      ((unitMatrix p).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank),
      ⟨Set.mem_ofPred.2 le_rfl, Set.mem_ofPred.2 le_rfl⟩, fun s hs ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hs
  rw [Set.mem_ofPred] at h₁ h₂
  have := hsum s
  have := hsum t
  exact le_antisymm (by lia) h₁

end AdicSheaf

open AdicSheaf

variable {X : Scheme.{u}}

/-- A retract of a lisse sheaf is lisse. -/
theorem IsAdicLisseSheaf.of_retract {F G : AdicSheaf l X} (e : Retract G F)
    (hF : IsAdicLisseSheaf F) : IsAdicLisseSheaf G := by
  obtain ⟨R, hR, h⟩ := hF
  refine IsAdicLisseSheaf.of_presieve R hR fun V f hf ↦ ?_
  obtain ⟨n, ⟨φ⟩⟩ := h f hf
  let e' : Retract ((f)^*ᵃ[l].obj G) (⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) :=
    { i := (f)^*ᵃ[l].map e.i ≫ φ.hom
      r := φ.inv ≫ (f)^*ᵃ[l].map e.r
      retract := by simp [← Functor.map_comp] }
  have hp : (e'.r ≫ e'.i) ≫ e'.r ≫ e'.i = e'.r ≫ e'.i := by
    simp only [Category.assoc, e'.retract_assoc]
  exact (isAdicLisseSheaf_kernel_one_sub_of_idempotent _ hp).of_iso e'.kernelIso

/-- A retract of a stratified lisse sheaf is stratified lisse. -/
theorem IsAdicStratifiedLisseSheaf.of_retract {F G : AdicSheaf l X} (e : Retract G F)
    (hF : IsAdicStratifiedLisseSheaf F) : IsAdicStratifiedLisseSheaf G := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  exact ⟨ι, hι, Z, i, hi, hc, hcover, fun k ↦ (h k).of_retract (e.map (i k)^*ᵃ[l])⟩

/-- A retract of a constructible sheaf is constructible. -/
theorem IsAdicConstructibleSheaf.of_retract {F G : AdicSheaf l X} (e : Retract G F)
    (hF : IsAdicConstructibleSheaf F) : IsAdicConstructibleSheaf G := by
  intro x
  obtain ⟨W, j, hj, hx, h⟩ := hF x
  exact ⟨W, j, hj, hx, h.of_retract (e.map (j)^*ᵃ[l])⟩

instance : (adicConstructibleSheaf l X).IsStableUnderRetracts where
  of_retract e h := IsAdicConstructibleSheaf.of_retract e h

end AlgebraicGeometry.ProEtale
