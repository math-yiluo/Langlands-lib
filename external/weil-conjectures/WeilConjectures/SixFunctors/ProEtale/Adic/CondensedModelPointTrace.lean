/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelScalar
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix
public import WeilConjectures.TraceFormula.UnitBasis

/-!
# Categorical traces at a separably closed point in the two models

Let `Ω` be a separably closed field and `N` a finite free `ℓ`-adic sheaf on `Spec Ω`, that is
`N ≅ ℚ̄_ℓʳ`. For an endomorphism `ψ` of `N`, the categorical trace of its image `E ψ` under the
equivalence `E : AdicSheaf ℓ (Spec Ω) ≌ Mod_{ℚ̲̄_ℓ,Spec Ω}`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), read in `ℚ̄_ℓ` through
`End (𝟙_ Mod_{Spec Ω}) ≅ ℚ̄_ℓ`, is the trace of the linear map induced by `ψ` on the global
sections `Γ(Spec Ω, N)`
(`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_traceOrZero_map_of_iso_biproduct`).

Both are the sum of the diagonal entries of the matrix of `ψ`, an endomorphism of `ℚ̄_ℓ` on
`Spec Ω` being the multiplication by a scalar
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_eq_smul_unit`), and `E` being `ℚ̄_ℓ`-linear on the
unit (`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_adicSheafEquivCondensedMod_map_smul`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace LinearMap

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, FiniteDimensional R (N i)]

/-- **The trace through a direct sum decomposition**: if `M` is decomposed into finitely many
finite-dimensional pieces `N i` by maps `inc i : N i → M` and `proj i : M → N i` with
`∑ inc i ∘ proj i = 𝟙`, the trace of an endomorphism `f` of `M` is the sum of the traces of the
diagonal blocks `proj i ∘ f ∘ inc i`. -/
theorem trace_eq_sum_trace_comp_comp (inc : ∀ i, N i →ₗ[R] M) (proj : ∀ i, M →ₗ[R] N i)
    (h : ∑ i, inc i ∘ₗ proj i = LinearMap.id) (f : M →ₗ[R] M) :
    LinearMap.trace R M f = ∑ i, LinearMap.trace R (N i) (proj i ∘ₗ f ∘ₗ inc i) := by
  classical
  have : FiniteDimensional R M := by
    refine Module.Finite.of_surjective (LinearMap.lsum R N R inc) fun m ↦ ⟨fun i ↦ proj i m, ?_⟩
    have hm := LinearMap.congr_fun h m
    simpa [LinearMap.sum_apply] using hm
  conv_lhs => rw [← LinearMap.comp_id f, ← h]
  have hs : f ∘ₗ (∑ i, inc i ∘ₗ proj i) = ∑ i, f ∘ₗ (inc i ∘ₗ proj i) :=
    map_sum (LinearMap.llcomp R M M M f) _ _
  rw [hs, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']

end LinearMap

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- On a scheme with at most one point, every endomorphism of the constant `ℓ`-adic sheaf
`ℚ̄_ℓ` is the multiplication by a scalar. -/
lemma AdicSheaf.exists_eq_smul_unit {V : Scheme.{u}} [Subsingleton V]
    (ψ : AdicSheaf.unit l V ⟶ AdicSheaf.unit l V) :
    ∃ c : PadicAlgCl l, ψ = AdicSheaf.smul (ULift.up c) (AdicSheaf.unit l V) := by
  have hs (c : PadicAlgCl l) (x : V) :
      (AdicSheaf.unitEndFun (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit l V))).1 x = c := by
    change c * 1 = c
    exact mul_one c
  rcases isEmpty_or_nonempty V with hV | ⟨⟨x⟩⟩
  · exact ⟨0, AdicSheaf.unitEndFun_injective (Subtype.ext (ContinuousMap.ext fun y ↦
      (IsEmpty.false y).elim))⟩
  · refine ⟨(AdicSheaf.unitEndFun ψ).1 x, AdicSheaf.unitEndFun_injective
      (Subtype.ext (ContinuousMap.ext fun y ↦ ?_))⟩
    obtain rfl := Subsingleton.elim y x
    exact (hs _ y).symm

variable (l) in
/-- The unit basis of the image of `ℚ̄_ℓʳ` in `Mod_{ℚ̲̄_ℓ,X}`: the images of the inclusions and
projections of the summands, through `E ℚ̄_ℓ,X ≅ ℚ̲̄_ℓ,X`. -/
noncomputable def adicSheafEquivCondensedModUnitBasis (X : Scheme.{u}) (r : ℕ) :
    UnitBasis ((adicSheafEquivCondensedMod l X).functor.obj
      (⨁ fun _ : Fin r ↦ AdicSheaf.unit l X)) (Fin r) where
  incl i := (adicSheafEquivCondensedModUnitIso l X).inv ≫
    (adicSheafEquivCondensedMod l X).functor.map
      (biproduct.ι (fun _ : Fin r ↦ AdicSheaf.unit l X) i)
  proj i := (adicSheafEquivCondensedMod l X).functor.map
      (biproduct.π (fun _ : Fin r ↦ AdicSheaf.unit l X) i) ≫
    (adicSheafEquivCondensedModUnitIso l X).hom
  incl_proj i j := by
    rw [Category.assoc, ← Functor.map_comp_assoc]
    split_ifs with h
    · subst h
      rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
    · rw [biproduct.ι_π_ne _ h, Functor.map_zero, zero_comp, comp_zero]
  total := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_sum,
      biproduct.total, CategoryTheory.Functor.map_id]

variable (l) in
/-- The global sections of an `ℓ`-adic sheaf, as a `ℚ̄_ℓ`-vector space. -/
noncomputable abbrev adicGlobalSectionsModule (X : Scheme.{u}) :
    AdicSheaf l X ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  AdicSheaf.forget X ⋙ Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l

instance (X : Scheme.{u}) : (adicGlobalSectionsModule l X).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp only [adicGlobalSectionsModule]
  infer_instance

/-- On global sections, the multiplication by a scalar `c` is the multiplication by `c`. -/
lemma adicGlobalSections_map_smul (X : Scheme.{u}) (c : PadicAlgCl l) (M : AdicSheaf l X) :
    ((adicGlobalSectionsModule l X).map (AdicSheaf.smul (ULift.up c) M)).hom = c • LinearMap.id :=
  LinearMap.ext fun x ↦ Sheaf.Γ_map_smulEnd (Scheme.ProEt.isTerminalMkId X) M.X (ULift.up c) x

/-- **Traces of endomorphisms of `ℚ̄_ℓʳ` at a separably closed point in the two models**: for an
endomorphism `ψ` of `ℚ̄_ℓʳ` on `Spec Ω`, the categorical trace of its image in
`Mod_{ℚ̲̄_ℓ,Spec Ω}`, read in `ℚ̄_ℓ`, is the trace of `ψ` on the global sections. -/
theorem endTensorUnitRingEquiv_traceOrZero_map_biproduct (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (r : ℕ) (ψ : (⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) ⟶
      ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) :
    CondensedRing.endTensorUnitRingEquiv l Ω
        (traceOrZero ((adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.map ψ)) =
      LinearMap.trace (PadicAlgCl l) _ ((adicGlobalSectionsModule l (Spec (.of Ω))).map ψ).hom := by
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have : ConnectedSpace (Spec (.of Ω)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum Ω))
  have h1 : Module.finrank (PadicAlgCl l)
      ((adicGlobalSectionsModule l (Spec (.of Ω))).obj (AdicSheaf.unit l (Spec (.of Ω)))) = 1 :=
    finrank_globalSections_adicConstantSheaf _
  have : FiniteDimensional (PadicAlgCl l)
      ((adicGlobalSectionsModule l (Spec (.of Ω))).obj (AdicSheaf.unit l (Spec (.of Ω)))) :=
    Module.finite_of_finrank_eq_succ h1
  rw [(adicSheafEquivCondensedModUnitBasis l (Spec (.of Ω)) r).traceOrZero_eq_sum, map_sum,
    LinearMap.trace_eq_sum_trace_comp_comp
      (N := fun _ : Fin r ↦ (adicGlobalSectionsModule l (Spec (.of Ω))).obj
        (AdicSheaf.unit l (Spec (.of Ω))))
      (fun i ↦ ((adicGlobalSectionsModule l (Spec (.of Ω))).map
        (biproduct.ι (fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) i)).hom)
      (fun i ↦ ((adicGlobalSectionsModule l (Spec (.of Ω))).map
        (biproduct.π (fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) i)).hom)]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    obtain ⟨c, hc⟩ := AdicSheaf.exists_eq_smul_unit
      (biproduct.ι (fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) i ≫ ψ ≫
        biproduct.π (fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) i)
    have hl : (adicSheafEquivCondensedModUnitBasis l (Spec (.of Ω)) r).incl i ≫
        (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.map ψ ≫
          (adicSheafEquivCondensedModUnitBasis l (Spec (.of Ω)) r).proj i =
        (adicSheafEquivCondensedModUnitIso l (Spec (.of Ω))).inv ≫
          (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.map
            (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit l (Spec (.of Ω)))) ≫
          (adicSheafEquivCondensedModUnitIso l (Spec (.of Ω))).hom := by
      rw [← hc]
      simp only [adicSheafEquivCondensedModUnitBasis, Functor.map_comp, Category.assoc]
    have hr : ((adicGlobalSectionsModule l (Spec (.of Ω))).map
        (biproduct.π (fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) i)).hom ∘ₗ
          ((adicGlobalSectionsModule l (Spec (.of Ω))).map ψ).hom ∘ₗ
          ((adicGlobalSectionsModule l (Spec (.of Ω))).map
            (biproduct.ι (fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) i)).hom =
        c • LinearMap.id := by
      rw [← adicGlobalSections_map_smul, ← hc, Functor.map_comp, Functor.map_comp,
        ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
    rw [hl, endTensorUnitRingEquiv_adicSheafEquivCondensedMod_map_smul, hr, map_smul,
      LinearMap.trace_id, h1, Nat.cast_one, smul_eq_mul, mul_one]
  · rw [← ModuleCat.hom_id, ← CategoryTheory.Functor.map_id, ← biproduct.total, Functor.map_sum,
      ModuleCat.hom_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Functor.map_comp, ModuleCat.hom_comp]

/-- **Traces at a separably closed point in the two models**: for a finite free `ℓ`-adic sheaf
`N ≅ ℚ̄_ℓʳ` on `Spec Ω` and an endomorphism `ψ` of `N`, the categorical trace of its image in
`Mod_{ℚ̲̄_ℓ,Spec Ω}`, read in `ℚ̄_ℓ` through `End (𝟙_ Mod_{Spec Ω}) ≅ ℚ̄_ℓ`, is the trace of `ψ`
on the global sections `Γ(Spec Ω, N)`. -/
theorem endTensorUnitRingEquiv_traceOrZero_map_of_iso_biproduct (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] {N : AdicSheaf l (Spec (.of Ω))} {r : ℕ}
    (e : N ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) (ψ : N ⟶ N) :
    CondensedRing.endTensorUnitRingEquiv l Ω
        (traceOrZero ((adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.map ψ)) =
      LinearMap.trace (PadicAlgCl l) _ ((adicGlobalSectionsModule l (Spec (.of Ω))).map ψ).hom := by
  have h := endTensorUnitRingEquiv_traceOrZero_map_biproduct Ω r (e.inv ≫ ψ ≫ e.hom)
  rw [Functor.map_comp, Functor.map_comp, ← Functor.mapIso_inv, ← Functor.mapIso_hom,
    traceOrZero_conj] at h
  rw [h, Functor.map_comp, Functor.map_comp, ← Functor.mapIso_inv, ← Functor.mapIso_hom,
    ← LinearMap.trace_conj' _ ((adicGlobalSectionsModule l (Spec (.of Ω))).mapIso e).toLinearEquiv]
  congr 1

end AlgebraicGeometry.ProEtale
