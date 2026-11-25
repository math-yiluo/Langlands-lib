/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ExtensionByZeroAdicCohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange

/-!
# The `ℚ̄_ℓ`-cohomology of an extension by zero is the extension of scalars of the integral one

Let `j : U ⟶ T` be an open immersion into a quasi-compact quasi-separated scheme. The pro-étale
cohomology `Hⁿ(T, j_! ℚ̄_ℓ) = Hⁿ(T_proét, j_! ℚ̄_ℓ,U)` of the extension by zero of the constant
`ℓ`-adic sheaf (computed in abelian sheaves,
`AlgebraicGeometry.ProEtale.CompactAdicConstantH`) is a `ℚ̄_ℓ`-vector space, and the inclusion
`C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ,U` induces a `ℤ_ℓ`-linear map `ι : Hⁿ(T, j_! ℤ_ℓ) ⟶ Hⁿ(T, j_! ℚ̄_ℓ)`. This
file proves that `ι` is a base change:

`ℚ̄_ℓ ⊗_{ℤ_ℓ} Hⁿ(T, j_! ℤ_ℓ) ≅ Hⁿ(T, j_! ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.isBaseChange_integralToCompactAdicConstantH`).

This is the compactly supported counterpart of
`AlgebraicGeometry.ProEtale.isBaseChange_integralToAdicConstantH`, with the same proof: the
extension by zero is a left adjoint, so `j_! ℚ̄_ℓ,U` is the filtered colimit of the sheaves
`j_! C(-, Λ)` over the compact lattices `Λ` of `ℚ̄_ℓ`, and `j_!` commutes with the decomposition
of `C(-, Λ)` along a basis of `Λ`. It feeds the `ℚ̄_ℓ` stage of the compactly supported case
of blueprint `corollary-degreewise-duality-over-fields--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-- The action of `ℚ̄_ℓ` on `j_! ℚ̄_ℓ,U`. -/
noncomputable abbrev compactAdicScalarRingHom :
    PadicAlgCl l →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj (adicConstantSheafAb l U)) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (adicScalarRingHom l U)

/-- The pro-étale cohomology `Hⁿ(T, j_! ℚ̄_ℓ) = Hⁿ(T_proét, j_! ℚ̄_ℓ,U)` of the extension by zero
of the constant `ℓ`-adic sheaf along an open immersion `j : U ⟶ T`, computed in abelian sheaves,
as a `ℚ̄_ℓ`-vector space. For `T` proper over an algebraically closed field this is the compactly
supported cohomology `Hⁿ_c(U, ℚ̄_ℓ)`. -/
def CompactAdicConstantH (n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj (adicConstantSheafAb l U)) n

noncomputable instance (n : ℕ) : AddCommGroup (CompactAdicConstantH l j n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (adicConstantSheafAb l U)) n))

noncomputable instance (n : ℕ) : Module (PadicAlgCl l) (CompactAdicConstantH l j n) :=
  Ext.moduleOfRingHom (compactAdicScalarRingHom l j) n

noncomputable instance (n : ℕ) : Module ℤ_[l] (CompactAdicConstantH l j n) :=
  Module.compHom _ (algebraMap ℤ_[l] (PadicAlgCl l))

instance (n : ℕ) : IsScalarTower ℤ_[l] (PadicAlgCl l) (CompactAdicConstantH l j n) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The extension by zero `j_! C(-, ℤ_ℓ) ⟶ j_! ℚ̄_ℓ,U` of the inclusion. -/
noncomputable abbrev integralToCompactAdicConstantSheaf :
    (j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[l]) ⟶
      (j)_!open[AddCommGrpCat.{u + 1}].obj (adicConstantSheafAb l U) :=
  (j)_!open[AddCommGrpCat.{u + 1}].map (continuousSheafToAdicConstantSheaf l U)

/-- The map `ι : Hⁿ(T, j_! ℤ_ℓ) ⟶ Hⁿ(T, j_! ℚ̄_ℓ)` induced by the inclusion
`C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ,U`. -/
noncomputable def integralToCompactAdicConstantH (n : ℕ) :
    CompactIntegralAdicH j l n →ₗ[ℤ_[l]] CompactAdicConstantH l j n where
  toFun x := Ext.comp (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
    x (Ext.mk₀ (integralToCompactAdicConstantSheaf l j)) (add_zero n)
  map_add' x y := Ext.add_comp _ _ _ _
  map_smul' c x := by
    change (Ext.comp x (Ext.mk₀ (compactIntegralSmulRingHom j l c).asHom) (add_zero n)).comp
        (Ext.mk₀ (integralToCompactAdicConstantSheaf l j)) (add_zero n) =
      (Ext.comp x (Ext.mk₀ (integralToCompactAdicConstantSheaf l j)) (add_zero n)).comp
        (Ext.mk₀ (compactAdicScalarRingHom l j (algebraMap ℤ_[l] (PadicAlgCl l) c)).asHom)
          (add_zero n)
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀]
    simp only [Functor.mapRingHom_apply_asHom, ← Functor.map_comp,
      integralSmulRingHom_comp_continuousSheafToAdicConstantSheaf]

lemma integralToCompactAdicConstantH_apply (n : ℕ) (x : CompactIntegralAdicH j l n) :
    integralToCompactAdicConstantH l j n x =
      Ext.comp (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        x (Ext.mk₀ (integralToCompactAdicConstantSheaf l j)) (add_zero n) :=
  rfl

section Decomposition

variable {C : Type*} [Category* C] [Abelian C] [HasExt C]

/-- A class of `Ext X Y n` decomposes along a decomposition `∑ πᵢ ≫ ιᵢ = 𝟙` of `Y`. -/
private lemma ext_eq_sum_comp' {X Y : C} {ι : Type*} (s : Finset ι) {Z : ι → C}
    (π : ∀ i, Y ⟶ Z i) (ι' : ∀ i, Z i ⟶ Y) (h : ∑ i ∈ s, π i ≫ ι' i = 𝟙 Y) {n : ℕ}
    (y : Ext X Y n) :
    y = ∑ i ∈ s, (y.comp (Ext.mk₀ (π i)) (add_zero n)).comp (Ext.mk₀ (ι' i)) (add_zero n) := by
  classical
  have hsum (t : Finset ι) : y.comp (Ext.mk₀ (∑ i ∈ t, π i ≫ ι' i)) (add_zero n) =
      ∑ i ∈ t, (y.comp (Ext.mk₀ (π i)) (add_zero n)).comp (Ext.mk₀ (ι' i)) (add_zero n) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.mk₀_add, Ext.comp_add, ih,
        Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [← hsum, h, Ext.comp_mk₀_id]

/-- Composition distributes over finite sums in the first variable. -/
private lemma ext_sum_comp' {X Y Z : C} {ι : Type*} (s : Finset ι) {n m p : ℕ}
    (x : ι → Ext X Y n) (β : Ext Y Z m) (h : n + m = p) :
    (∑ i ∈ s, x i).comp β h = ∑ i ∈ s, (x i).comp β h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.add_comp, ih]

end Decomposition

/-- **The `ℚ̄_ℓ`-cohomology of an extension by zero is the extension of scalars of the integral
one.** For an open immersion `j : U ⟶ T` into a quasi-compact quasi-separated scheme, the map
`ι : Hⁿ(T, j_! ℤ_ℓ) ⟶ Hⁿ(T, j_! ℚ̄_ℓ)` induced by `C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ,U` identifies
`Hⁿ(T, j_! ℚ̄_ℓ)` with `ℚ̄_ℓ ⊗_{ℤ_ℓ} Hⁿ(T, j_! ℤ_ℓ)`. This is the `ℚ̄_ℓ` stage of the compactly
supported case of blueprint `corollary-degreewise-duality-over-fields--1`. -/
theorem isBaseChange_integralToCompactAdicConstantH [CompactSpace T] [QuasiSeparatedSpace T]
    (n : ℕ) : IsBaseChange (PadicAlgCl l) (integralToCompactAdicConstantH l j n) := by
  classical
  set E := (j)_!open[AddCommGrpCat.{u + 1}]
  set L := (integralToCompactAdicConstantH l j n).liftBaseChange (PadicAlgCl l)
  have hcol := Scheme.ProEt.H_map_isColimit_of_isFiltered_small T
    (isColimitOfPreserves E (isColimitAdicConstantSheafCocone l U)) n
  -- the image of a combination of the classes `bᵢ` along the basis `eᵢ` of a lattice
  have hcomb (Λ : CompactLattice l) (b : Λ.BasisIndex → CompactIntegralAdicH j l n) :
      Sheaf.H.map (E.map (compactLatticeToAdicConstantSheaf l U Λ)) n
          (∑ i, Ext.comp (b i) (Ext.mk₀ (E.map (continuousSheafMap U
            (Λ.mulHom (Λ.basis i) (Λ.basis i).2)))) (add_zero n)) =
        L (∑ i, (Λ.basis i : PadicAlgCl l) ⊗ₜ b i) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← E.map_comp,
      continuousSheafMap_mulHom_comp, E.map_comp, LinearMap.liftBaseChange_tmul,
      ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
    rfl
  -- every class on a lattice is such a combination
  have hdec (Λ : CompactLattice l) (y : Sheaf.H (E.obj (continuousSheaf U Λ.1)) n) :
      y = ∑ i, Ext.comp (Ext.comp y (Ext.mk₀ (E.map (continuousSheafMap U (Λ.coordHom i))))
        (add_zero n)) (Ext.mk₀ (E.map (continuousSheafMap U
          (Λ.mulHom (Λ.basis i) (Λ.basis i).2)))) (add_zero n) := by
    refine ext_eq_sum_comp' _ _ _ ?_ y
    rw [← E.map_id, ← continuousSheafMap_id, ← Λ.sum_mulHom_comp_coordHom, continuousSheafMap_sum,
      E.map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← E.map_comp, continuousSheafMap_comp]
  have hsurj : Function.Surjective L := by
    intro v
    obtain ⟨⟨Λ⟩, y, rfl⟩ := hcol.1 v
    rw [hdec Λ y]
    exact ⟨_, (hcomb Λ _).symm⟩
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    -- a lattice containing the coefficients
    obtain ⟨Λ, hΛ⟩ := exists_compactLattice_of_isCompact
      (s.image Prod.fst).finite_toSet.isCompact
      (FiniteDimensional.span_of_finite ℚ_[l] (s.image Prod.fst).finite_toSet)
    have hmem (p : PadicAlgCl l × CompactIntegralAdicH j l n) (hp : p ∈ s) : p.1 ∈ Λ.1 :=
      hΛ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hp))
    let b (i : Λ.BasisIndex) : CompactIntegralAdicH j l n :=
      ∑ p ∈ s.attach, Λ.coord i ⟨p.1.1, hmem p.1 p.2⟩ • p.1.2
    have ht' : ∑ p ∈ s, p.1 ⊗ₜ[ℤ_[l]] p.2 = ∑ i, (Λ.basis i : PadicAlgCl l) ⊗ₜ b i := by
      rw [← Finset.sum_attach]
      simp only [b, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      have hp := Λ.sum_coord_smul ⟨p.1.1, hmem p.1 p.2⟩
      calc p.1.1 ⊗ₜ[ℤ_[l]] p.1.2 =
          (∑ i, Λ.coord i ⟨p.1.1, hmem p.1 p.2⟩ • (Λ.basis i : PadicAlgCl l)) ⊗ₜ[ℤ_[l]] p.1.2 := by
            rw [hp]
        _ = _ := by
          rw [TensorProduct.sum_tmul]
          simp_rw [TensorProduct.smul_tmul']
    rw [ht'] at ht ⊢
    set y := ∑ i, Ext.comp (b i) (Ext.mk₀ (E.map (continuousSheafMap U
      (Λ.mulHom (Λ.basis i) (Λ.basis i).2)))) (add_zero n)
    have hy : Sheaf.H.map (E.map (compactLatticeToAdicConstantSheaf l U Λ)) n y = 0 := by
      rw [hcomb Λ b]
      exact ht
    obtain ⟨⟨Λ'⟩, a, ha⟩ := hcol.2 ⟨Λ⟩ y hy
    have hΛΛ' : Λ.1 ≤ Λ'.1 :=
      (leOfHom a : (⟨Λ⟩ : ULift.{u + 1} (CompactLattice l)) ≤ ⟨Λ'⟩)
    -- the coordinates of the images of the `bᵢ` in the bigger lattice vanish
    have hcoef (k : Λ'.BasisIndex) :
        ∑ i, Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩ • b i = 0 := by
      have h := congrArg (fun z ↦ Ext.comp z
        (Ext.mk₀ (E.map (continuousSheafMap U (Λ'.coordHom k)))) (add_zero n)) ha
      simp only [Sheaf.H.map_apply, Ext.zero_comp] at h
      rw [← h]
      rw [ext_sum_comp', ext_sum_comp']
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have e : continuousSheafMap U (Λ.mulHom (Λ.basis i) (Λ.basis i).2) ≫
          (compactLatticeDiagram l U).map a ≫ continuousSheafMap U (Λ'.coordHom k) =
          (integralSmulRingHom U l (Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩)).asHom := by
        have e1 : (compactLatticeDiagram l U).map a ≫ continuousSheafMap U (Λ'.coordHom k) =
            continuousSheafMap U ((Λ'.coordHom k).comp
              ⟨AddSubgroup.inclusion hΛΛ', continuous_subtype_val.subtype_mk _⟩) :=
          (continuousSheafMap_comp U _ _).symm
        rw [e1, ← continuousSheafMap_comp]
        refine continuousSheafMap_congr U fun c ↦ ?_
        exact (Λ'.coord_smul k c ⟨_, hΛΛ' (Λ.basis i).2⟩).trans (mul_comm _ _)
      have e' : E.map (continuousSheafMap U (Λ.mulHom (Λ.basis i) (Λ.basis i).2)) ≫
          (compactLatticeDiagram l U ⋙ E).map a ≫
            E.map (continuousSheafMap U (Λ'.coordHom k)) =
          (compactIntegralSmulRingHom j l (Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩)).asHom := by
        rw [Functor.comp_map, ← E.map_comp, ← E.map_comp, e]
        rfl
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
        Ext.mk₀_comp_mk₀, e']
      rfl
    calc ∑ i, (Λ.basis i : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b i =
        ∑ i, (∑ k, Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩ • (Λ'.basis k : PadicAlgCl l))
          ⊗ₜ[ℤ_[l]] b i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Λ'.sum_coord_smul]
      _ = ∑ k, (Λ'.basis k : PadicAlgCl l) ⊗ₜ[ℤ_[l]]
          ∑ i, Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩ • b i := by
          simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
          exact Finset.sum_comm
      _ = 0 := by simp [hcoef]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩) fun x ↦ by
    simp [L]

end AlgebraicGeometry.ProEtale
