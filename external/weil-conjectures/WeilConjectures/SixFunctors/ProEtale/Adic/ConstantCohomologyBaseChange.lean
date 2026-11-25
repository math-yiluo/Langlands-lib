/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.CompactLatticeBasis

/-!
# The cohomology of `ℚ̄_ℓ` is the extension of scalars of the cohomology of `ℤ_ℓ`

Let `S` be a quasi-compact quasi-separated scheme. The pro-étale cohomology
`Hⁿ(S, ℚ̄_ℓ) = Hⁿ(S_proét, ℚ̄_ℓ,S)` of the constant `ℓ`-adic sheaf (computed in abelian sheaves,
`AlgebraicGeometry.ProEtale.AdicConstantH`) is a `ℚ̄_ℓ`-vector space through the action of `ℚ̄_ℓ`
on the coefficients, and the inclusion `C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ,S` induces a `ℤ_ℓ`-linear map
`ι : Hⁿ(S, ℤ_ℓ) ⟶ Hⁿ(S, ℚ̄_ℓ)`. This file proves that `ι` is a base change:

`ℚ̄_ℓ ⊗_{ℤ_ℓ} Hⁿ(S, ℤ_ℓ) ≅ Hⁿ(S, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.isBaseChange_integralToAdicConstantH`).

The sheaf `ℚ̄_ℓ,S` is the filtered union of the sheaves `C(-, Λ)` over the compact lattices `Λ`
of `ℚ̄_ℓ` (`AlgebraicGeometry.ProEtale.isColimitAdicConstantSheafCocone`), cohomology of the qcqs
`S` commutes with this filtered colimit
(`AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_of_isFiltered_small`), and each `Λ` is a free
`ℤ_ℓ`-module with continuous coordinates (`PadicAlgCl.CompactLattice.continuous_coord`), so that
`Hⁿ(S, C(-, Λ)) = Λ ⊗_{ℤ_ℓ} Hⁿ(S, ℤ_ℓ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

section Maps

variable {S} {A B : Type} [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]
  [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

lemma continuousSheafMap_sum {ι : Type*} (s : Finset ι) (φ : ι → ContinuousAddMonoidHom A B) :
    continuousSheafMap S (∑ i ∈ s, φ i) = ∑ i ∈ s, continuousSheafMap S (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousSheafMap_zero S
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, continuousSheafMap_add, ih]

end Maps

/-- Multiplication by `c ∈ ℚ̄_ℓ` on the underlying abelian sheaf of `ℚ̄_ℓ,S`. -/
noncomputable def adicScalar (c : PadicAlgCl l) :
    adicConstantSheafAb l S ⟶ adicConstantSheafAb l S :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun f := ULift.up (c • ULift.down f)
          map_zero' := congrArg ULift.up (smul_zero c)
          map_add' x y := congrArg ULift.up (smul_add c x.down y.down) }
     naturality _ _ _ := rfl }⟩

lemma adicScalar_one : adicScalar l S 1 = 𝟙 _ := by
  ext _ f
  exact congrArg ULift.up (one_smul _ f.down)

lemma adicScalar_mul (c d : PadicAlgCl l) :
    adicScalar l S (c * d) = adicScalar l S d ≫ adicScalar l S c := by
  ext _ f
  exact congrArg ULift.up (mul_smul c d f.down)

lemma adicScalar_zero : adicScalar l S 0 = 0 := by
  ext _ f
  exact congrArg ULift.up (zero_smul _ f.down)

lemma adicScalar_add (c d : PadicAlgCl l) :
    adicScalar l S (c + d) = adicScalar l S c + adicScalar l S d := by
  ext _ f
  exact congrArg ULift.up (add_smul c d f.down)

/-- The action of `ℚ̄_ℓ` on the underlying abelian sheaf of `ℚ̄_ℓ,S`. -/
noncomputable def adicScalarRingHom : PadicAlgCl l →+* End (adicConstantSheafAb l S) where
  toFun c := .of (adicScalar l S c)
  map_one' := End.ext (adicScalar_one l S)
  map_mul' c d := End.ext (adicScalar_mul l S c d)
  map_zero' := End.ext (adicScalar_zero l S)
  map_add' c d := End.ext (adicScalar_add l S c d)

/-- The inclusion `C(-, ℤ_ℓ) ⟶ ℚ̄_ℓ,S` of abelian sheaves: `ℤ_ℓ`-valued functions are locally
finite, their values spanning the line `ℚ_ℓ`. -/
noncomputable def continuousSheafToAdicConstantSheaf :
    continuousSheaf S ℤ_[l] ⟶ adicConstantSheafAb l S :=
  ⟨{ app V := AddCommGrpCat.ofHom
        { toFun f := ULift.up ⟨⟨fun t ↦ algebraMap ℤ_[l] (PadicAlgCl l)
            ((ULift.down f : C(V.unop.left, ℤ_[l])) t), continuous_algebraMap_padicInt.comp
              (ULift.down f : C(V.unop.left, ℤ_[l])).continuous⟩,
            mem_locallyFiniteFunctions_of_finiteDimensional
              (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] {1})
                (Submodule.span_le.2 (by
                  rintro _ ⟨t, rfl⟩
                  simp only [ContinuousMap.coe_mk]
                  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l),
                    Algebra.algebraMap_eq_smul_one]
                  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl))))⟩
          map_zero' := congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun _ ↦
            map_zero (algebraMap ℤ_[l] (PadicAlgCl l))))
          map_add' x y := congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun t ↦
            map_add (algebraMap ℤ_[l] (PadicAlgCl l))
              ((ULift.down x : C(V.unop.left, ℤ_[l])) t)
              ((ULift.down y : C(V.unop.left, ℤ_[l])) t))) }
     naturality _ _ _ := rfl }⟩

lemma integralSmulRingHom_comp_continuousSheafToAdicConstantSheaf (c : ℤ_[l]) :
    (integralSmulRingHom S l c).asHom ≫ continuousSheafToAdicConstantSheaf l S =
      continuousSheafToAdicConstantSheaf l S ≫
        (adicScalarRingHom l S (algebraMap ℤ_[l] (PadicAlgCl l) c)).asHom := by
  ext V f
  let g : C(V.unop.left, ℤ_[l]) := f.down
  refine congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun t ↦ ?_))
  exact (map_mul (algebraMap ℤ_[l] (PadicAlgCl l)) c (g t)).trans (smul_eq_mul _ _).symm

/-- The pro-étale cohomology `Hⁿ(S, ℚ̄_ℓ) = Hⁿ(S_proét, ℚ̄_ℓ,S)` of the constant `ℓ`-adic sheaf,
computed in abelian sheaves, as a `ℚ̄_ℓ`-vector space. -/
def AdicConstantH (n : ℕ) : Type (u + 1) :=
  Sheaf.H (adicConstantSheafAb l S) n

noncomputable instance (n : ℕ) : AddCommGroup (AdicConstantH l S n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H (adicConstantSheafAb l S) n))

noncomputable instance (n : ℕ) : Module (PadicAlgCl l) (AdicConstantH l S n) :=
  Ext.moduleOfRingHom (adicScalarRingHom l S) n

noncomputable instance (n : ℕ) : Module ℤ_[l] (AdicConstantH l S n) :=
  Module.compHom _ (algebraMap ℤ_[l] (PadicAlgCl l))

instance (n : ℕ) : IsScalarTower ℤ_[l] (PadicAlgCl l) (AdicConstantH l S n) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The map `ι : Hⁿ(S, ℤ_ℓ) ⟶ Hⁿ(S, ℚ̄_ℓ)` induced by the inclusion `C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ,S`. -/
noncomputable def integralToAdicConstantH (n : ℕ) :
    IntegralAdicH S l n →ₗ[ℤ_[l]] AdicConstantH l S n where
  toFun x := Ext.comp (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    x (Ext.mk₀ (continuousSheafToAdicConstantSheaf l S)) (add_zero n)
  map_add' x y := Ext.add_comp _ _ _ _
  map_smul' c x := by
    change (Ext.comp x (Ext.mk₀ (integralSmulRingHom S l c).asHom) (add_zero n)).comp
        (Ext.mk₀ (continuousSheafToAdicConstantSheaf l S)) (add_zero n) =
      (Ext.comp x (Ext.mk₀ (continuousSheafToAdicConstantSheaf l S)) (add_zero n)).comp
        (Ext.mk₀ (adicScalarRingHom l S (algebraMap ℤ_[l] (PadicAlgCl l) c)).asHom) (add_zero n)
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀, integralSmulRingHom_comp_continuousSheafToAdicConstantSheaf]

section Lattice

variable {l S}

/-- The inclusion of `C(-, ℤ_ℓ)` into `C(-, Λ)` along `c ↦ c • e`, followed by the inclusion of
`C(-, Λ)` into `ℚ̄_ℓ,S`, is the inclusion of `C(-, ℤ_ℓ)` followed by multiplication by `e`. -/
lemma continuousSheafMap_mulHom_comp (Λ : CompactLattice l) (e : PadicAlgCl l) (he : e ∈ Λ.1) :
    continuousSheafMap S (Λ.mulHom e he) ≫ compactLatticeToAdicConstantSheaf l S Λ =
      continuousSheafToAdicConstantSheaf l S ≫ adicScalar l S e := by
  ext V f
  let g : C(V.unop.left, ℤ_[l]) := f.down
  refine congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun t ↦ ?_))
  exact (Algebra.smul_def (g t) e).trans ((mul_comm _ _).trans (smul_eq_mul _ _).symm)

end Lattice

section Decomposition

variable {C : Type*} [Category* C] [Abelian C] [HasExt C]

/-- A class of `Ext X Y n` decomposes along a decomposition `∑ πᵢ ≫ ιᵢ = 𝟙` of `Y`. -/
private lemma ext_eq_sum_comp {X Y : C} {ι : Type*} (s : Finset ι) {Z : ι → C}
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
private lemma ext_sum_comp {X Y Z : C} {ι : Type*} (s : Finset ι) {n m p : ℕ}
    (x : ι → Ext X Y n) (β : Ext Y Z m) (h : n + m = p) :
    (∑ i ∈ s, x i).comp β h = ∑ i ∈ s, (x i).comp β h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.add_comp, ih]

end Decomposition

/-- **The cohomology of `ℚ̄_ℓ` is the extension of scalars of that of `ℤ_ℓ`.** For a
quasi-compact quasi-separated scheme `S`, the map `ι : Hⁿ(S, ℤ_ℓ) ⟶ Hⁿ(S, ℚ̄_ℓ)` induced by
`C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ,S` identifies `Hⁿ(S, ℚ̄_ℓ)` with `ℚ̄_ℓ ⊗_{ℤ_ℓ} Hⁿ(S, ℤ_ℓ)`. -/
theorem isBaseChange_integralToAdicConstantH [CompactSpace S] [QuasiSeparatedSpace S] (n : ℕ) :
    IsBaseChange (PadicAlgCl l) (integralToAdicConstantH l S n) := by
  classical
  set L := (integralToAdicConstantH l S n).liftBaseChange (PadicAlgCl l)
  have hcol := Scheme.ProEt.H_map_isColimit_of_isFiltered_small S
    (isColimitAdicConstantSheafCocone l S) n
  -- the image of a combination of the classes `bᵢ` along the basis `eᵢ` of a lattice
  have hcomb (Λ : CompactLattice l) (b : Λ.BasisIndex → IntegralAdicH S l n) :
      Sheaf.H.map (compactLatticeToAdicConstantSheaf l S Λ) n
          (∑ i, Ext.comp (b i) (Ext.mk₀ (continuousSheafMap S
            (Λ.mulHom (Λ.basis i) (Λ.basis i).2))) (add_zero n)) =
        L (∑ i, (Λ.basis i : PadicAlgCl l) ⊗ₜ b i) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      continuousSheafMap_mulHom_comp, LinearMap.liftBaseChange_tmul, ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_third_deg_zero]
    rfl
  -- every class on a lattice is such a combination
  have hdec (Λ : CompactLattice l) (y : Sheaf.H (continuousSheaf S Λ.1) n) :
      y = ∑ i, Ext.comp (Ext.comp y (Ext.mk₀ (continuousSheafMap S (Λ.coordHom i))) (add_zero n))
        (Ext.mk₀ (continuousSheafMap S (Λ.mulHom (Λ.basis i) (Λ.basis i).2))) (add_zero n) := by
    refine ext_eq_sum_comp _ _ _ ?_ y
    rw [← continuousSheafMap_id, ← Λ.sum_mulHom_comp_coordHom, continuousSheafMap_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (continuousSheafMap_comp S _ _).symm
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
    have hmem (p : PadicAlgCl l × IntegralAdicH S l n) (hp : p ∈ s) : p.1 ∈ Λ.1 :=
      hΛ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hp))
    let b (i : Λ.BasisIndex) : IntegralAdicH S l n :=
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
    set y := ∑ i, Ext.comp (b i) (Ext.mk₀ (continuousSheafMap S
      (Λ.mulHom (Λ.basis i) (Λ.basis i).2))) (add_zero n)
    have hy : Sheaf.H.map (compactLatticeToAdicConstantSheaf l S Λ) n y = 0 := by
      rw [hcomb Λ b]
      exact ht
    obtain ⟨⟨Λ'⟩, a, ha⟩ := hcol.2 ⟨Λ⟩ y hy
    have hΛΛ' : Λ.1 ≤ Λ'.1 :=
      (leOfHom a : (⟨Λ⟩ : ULift.{u + 1} (CompactLattice l)) ≤ ⟨Λ'⟩)
    -- the coordinates of the images of the `bᵢ` in the bigger lattice vanish
    have hcoef (k : Λ'.BasisIndex) :
        ∑ i, Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩ • b i = 0 := by
      have h := congrArg (fun z ↦ Ext.comp z
        (Ext.mk₀ (continuousSheafMap S (Λ'.coordHom k))) (add_zero n)) ha
      simp only [Sheaf.H.map_apply, Ext.zero_comp] at h
      rw [← h]
      rw [ext_sum_comp, ext_sum_comp]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have e : continuousSheafMap S (Λ.mulHom (Λ.basis i) (Λ.basis i).2) ≫
          (compactLatticeDiagram l S).map a ≫ continuousSheafMap S (Λ'.coordHom k) =
          (integralSmulRingHom S l (Λ'.coord k ⟨Λ.basis i, hΛΛ' (Λ.basis i).2⟩)).asHom := by
        have e1 : (compactLatticeDiagram l S).map a ≫ continuousSheafMap S (Λ'.coordHom k) =
            continuousSheafMap S ((Λ'.coordHom k).comp
              ⟨AddSubgroup.inclusion hΛΛ', continuous_subtype_val.subtype_mk _⟩) :=
          (continuousSheafMap_comp S _ _).symm
        rw [e1, ← continuousSheafMap_comp]
        refine continuousSheafMap_congr S fun c ↦ ?_
        exact (Λ'.coord_smul k c ⟨_, hΛΛ' (Λ.basis i).2⟩).trans (mul_comm _ _)
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
        Ext.mk₀_comp_mk₀, e]
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
