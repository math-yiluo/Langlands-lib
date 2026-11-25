/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangle
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Extension of scalars along a quotient by a nonzerodivisor `r` of `R`

Let `C` be a closed symmetric monoidal Grothendieck abelian category, `φ : R ⟶ S` a morphism of
commutative algebra objects and `r : R ⟶ R` an `R`-linear endomorphism of the regular module
such that `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact: `S = R ⧸ r` (for instance the residue
field of a discrete valuation ring, `r` a uniformizer). Write `r_M : M ⟶ M` for the action of
`r` on an `R`-module `M` (`CategoryTheory.Mod.regularEndSMul`). We show:

* `CategoryTheory.Mod.exact_regularEndSMul_extendUnit`: `M --r--> M ⟶ S ⊗_R M ⟶ 0` is exact,
  `- ⊗_R M` being right exact;
* `CategoryTheory.Mod.shortExact_regularEndSMul_extendUnit`: if `r_M` is a monomorphism,
  `0 ⟶ M --r--> M ⟶ S ⊗_R M ⟶ 0` is short exact; this applies to flat `M`
  (`CategoryTheory.Mod.mono_regularEndSMul_of_flat`);
* `CategoryTheory.Mod.isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul`: the derived
  extension of scalars `S ⊗ᴸ_R -` is computed levelwise on every complex `P` of `R`-modules on
  which `r` acts injectively: compare `P` with a K-flat resolution through the short exact
  sequences `0 ⟶ P --r--> P ⟶ S ⊗_R P ⟶ 0` and the five lemma.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]

section

variable (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R))

/-- The action `r_M : M ⟶ M` of an endomorphism `r` of the regular module `R` on an `R`-module
`M`, through the left unitor `R ⊗_R M ≅ M`. -/
noncomputable def regularEndSMul (M : Mod C R) : M ⟶ M :=
  (λ_ M).inv ≫ r ▷ M ≫ (λ_ M).hom

omit [MonoidalPreadditive C] in
/-- `r_M` is natural in `M`. -/
@[reassoc]
lemma regularEndSMul_naturality {M N : Mod C R} (g : M ⟶ N) :
    regularEndSMul r M ≫ g = g ≫ regularEndSMul r N := by
  simp only [regularEndSMul, Category.assoc, ← leftUnitor_naturality, whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

omit [MonoidalPreadditive C] in
/-- Through the left unitor `R ⊗_R M ≅ M`, the map `r ⊗_R M` is the action `r_M`. -/
@[reassoc]
lemma leftUnitor_hom_hom_comp_regularEndSMul_hom (M : Mod C R) :
    (λ_ M).hom.hom ≫ (regularEndSMul r M).hom = (r ▷ M).hom ≫ (λ_ M).hom.hom := by
  rw [← comp_hom', ← comp_hom', regularEndSMul, Iso.hom_inv_id_assoc]

omit [MonoidalPreadditive C] in
/-- For a global section `σ : 𝟙 ⟶ R`, the action of the endomorphism `regularLift σ` of the
regular module is the action `globalSmul σ` of `σ`. -/
lemma regularEndSMul_regularLift_hom (σ : 𝟙_ C ⟶ R) (M : Mod C R) :
    (regularEndSMul (regularLift (regular R) σ) M).hom = globalSmul σ M := by
  have key : (λ_ R).inv ≫ σ ▷ R ≫ μ[R] = (ρ_ R).inv ≫ R ◁ σ ≫ μ[R] := by
    conv_lhs => rw [← IsCommMonObj.mul_comm R]
    rw [BraidedCategory.braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc]
  have h : (λ_ R).inv ▷ M.X ≫ (σ ▷ R) ▷ M.X =
      (λ_ (R ⊗ M.X)).inv ≫ σ ▷ (R ⊗ M.X) ≫ (α_ R R M.X).inv := by
    monoidal
  rw [← cancel_epi (λ_ M).hom.hom, leftUnitor_hom_hom_comp_regularEndSMul_hom,
    ← cancel_epi (tensorObjπ (𝟙_ (Mod C R)) M), tensorObjπ_whiskerRight_assoc,
    tensorObjπ_leftUnitor_hom_hom_assoc]
  erw [tensorObjπ_leftUnitor_hom_hom]
  change ((ρ_ R).inv ≫ R ◁ σ ≫ μ[R]) ▷ M.X ≫ act M.X = act M.X ≫ globalSmul σ M
  rw [← key, globalSmul, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    reassoc_of% h, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    ModObj.mul_smul_self_flip]

variable {r}

/-- If `r ≫ φ = 0`, the unit `M ⟶ S ⊗_R M` kills the action of `r`. -/
lemma regularEndSMul_comp_extendUnit (w : r.hom ≫ φ = 0) (M : Mod C R) :
    regularEndSMul r M ≫ extendUnit φ M = 0 := by
  have w' : r ≫ regularToComapRegular φ = 0 := hom_ext _ _ w
  refine hom_ext _ _ ?_
  rw [comp_hom', extendUnit_hom, ← cancel_epi (λ_ M).hom.hom,
    leftUnitor_hom_hom_comp_regularEndSMul_hom_assoc,
    ← regularToComapRegular_whiskerRight_hom_extendForgetTensorObjIso_inv, ← Category.assoc,
    ← comp_hom', ← comp_whiskerRight, w', MonoidalPreadditive.zero_whiskerRight]
  erw [Limits.zero_comp, Limits.comp_zero]

/-- **Reduction modulo `r`**: if `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, then for every
`R`-module `M` the sequence `M --r--> M --unit--> S ⊗_R M ⟶ 0` is exact, and the unit is an
epimorphism: `S ⊗_R M = M ⧸ r M`. -/
theorem exact_regularEndSMul_extendUnit (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (M : Mod C R) :
    (ShortComplex.mk (regularEndSMul r M) (extendUnit φ M)
        (regularEndSMul_comp_extendUnit w M)).Exact ∧
      Epi (extendUnit φ M) := by
  have w' : r ≫ regularToComapRegular φ = 0 := hom_ext _ _ w
  have h₀ : (ShortComplex.mk _ _ w').ShortExact := shortExact_of_shortExact_map_forget hφ
  have := h₀.epi_g
  have : PreservesColimitsOfSize.{v, v} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  let F := tensorRight M ⋙ forget R
  have e : (ShortComplex.mk _ _ w').map F ≅
      (ShortComplex.mk (regularEndSMul r M) (extendUnit φ M)
        (regularEndSMul_comp_extendUnit w M)).map (forget R) :=
    ShortComplex.isoMk ((forget R).mapIso (λ_ M)) ((forget R).mapIso (λ_ M))
      (extendForgetTensorObjIso φ M).symm
      (leftUnitor_hom_hom_comp_regularEndSMul_hom r M)
      (regularToComapRegular_whiskerRight_hom_extendForgetTensorObjIso_inv φ M).symm
  have h₁ : ((ShortComplex.mk _ _ w').map F).Exact :=
    h₀.exact.map_of_epi_of_preservesCokernel F inferInstance inferInstance
  have : Epi ((ShortComplex.mk _ _ w').map F).g := F.map_epi _
  refine ⟨(ShortComplex.exact_map_iff_of_faithful _ (forget R)).1
    ((ShortComplex.exact_iff_of_iso e).1 h₁), (forget R).epi_of_epi_map ?_⟩
  exact epi_of_epi_fac e.hom.comm₂₃

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact and `r` acts injectively on an `R`-module
`M`, then `0 ⟶ M --r--> M --unit--> S ⊗_R M ⟶ 0` is short exact. -/
theorem shortExact_regularEndSMul_extendUnit (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (M : Mod C R) [Mono (regularEndSMul r M)] :
    (ShortComplex.mk (regularEndSMul r M) (extendUnit φ M)
        (regularEndSMul_comp_extendUnit w M)).ShortExact :=
  have := (exact_regularEndSMul_extendUnit w hφ M).2
  ⟨(exact_regularEndSMul_extendUnit w hφ M).1⟩

omit [IsCommMonObj S] in
/-- If `r : R ⟶ R` is a monomorphism, it acts injectively on every flat `R`-module. -/
lemma mono_regularEndSMul_of_flat [Mono r.hom] (M : Mod C R) (hM : ObjectProperty.flat M) :
    Mono (regularEndSMul r M) := by
  have := hM.tensorRight.preservesFiniteLimits
  have : Mono r := (forget R).mono_of_mono_map (by assumption)
  have : Mono (r ▷ M) := (tensorRight M).map_mono r
  rw [regularEndSMul]
  infer_instance

end

section Complex

variable (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R))

/-- The action `r_P : P ⟶ P` of `r` on a complex of `R`-modules. -/
@[simps]
noncomputable def regularEndSMulComplex (P : CochainComplex (Mod C R) ℤ) : P ⟶ P where
  f i := regularEndSMul r (P.X i)
  comm' i j _ := regularEndSMul_naturality r (P.d i j)

variable {r}

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact and `r` acts injectively on the terms of a
complex `P` of `R`-modules, then `0 ⟶ P --r--> P ⟶ S ⊗_R P ⟶ 0` is a short exact sequence of
complexes. -/
lemma shortExact_regularEndSMulComplex (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (P : CochainComplex (Mod C R) ℤ)
    (hP : ∀ n, Mono (regularEndSMul r (P.X n))) :
    (ShortComplex.mk (regularEndSMulComplex r P) (extendUnitComplexHom φ P) (by
      ext i
      exact congrArg Hom.hom (regularEndSMul_comp_extendUnit w (P.X i)))).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  have := hP i
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))
    (shortExact_regularEndSMul_extendUnit w hφ (P.X i))

variable [Abelian.HasFunctorialFlatResolution C]

-- the five lemma for complexes of module objects is slow to elaborate
/-- **The derived extension of scalars along `R ⟶ R ⧸ r` is computed levelwise on complexes on
which `r` acts injectively**: if `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact and `r` acts
injectively on the terms of a complex `P` of `R`-modules, then the counit
`S ⊗ᴸ_R P ⟶ S ⊗_R P` is an isomorphism. -/
theorem isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul [Mono r.hom]
    (w : r.hom ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)
    (P : CochainComplex (Mod C R) ℤ) (hP : ∀ n, Mono (regularEndSMul r (P.X n))) :
    IsIso ((extendScalars φ).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj P)) := by
  obtain ⟨Q, π, _, hflat, hQ⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat Q hQ
  have hQ' : ∀ n, Mono (regularEndSMul r (Q.X n)) := fun n ↦
    mono_regularEndSMul_of_flat (Q.X n) (hflat n)
  let ψ : ShortComplex.mk (regularEndSMulComplex r Q) (extendUnitComplexHom φ Q) (by
      ext i
      exact congrArg Hom.hom (regularEndSMul_comp_extendUnit w (Q.X i))) ⟶
      ShortComplex.mk (regularEndSMulComplex r P) (extendUnitComplexHom φ P) (by
      ext i
      exact congrArg Hom.hom (regularEndSMul_comp_extendUnit w (P.X i))) :=
    { τ₁ := π
      τ₂ := π
      τ₃ := ((extendScalars φ ⋙ comap φ).mapHomologicalComplex _).map π
      comm₁₂ := by
        ext i : 1
        exact (regularEndSMul_naturality r (π.f i)).symm
      comm₂₃ := by
        ext i : 1
        rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, extendUnitComplexHom_f,
          extendUnitComplexHom_f, ← extendRestrictAdjunction_unit_app,
          ← extendRestrictAdjunction_unit_app]
        exact (extendRestrictAdjunction φ).unit.naturality (π.f i) }
  have h₃ : QuasiIso ψ.τ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (shortExact_regularEndSMulComplex w hφ Q hQ') (shortExact_regularEndSMulComplex w hφ P hP)
    (inferInstanceAs (QuasiIso π)) (inferInstanceAs (QuasiIso π))
  have h₃' : QuasiIso (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map π) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (comap φ)).1 h₃
  have hL : IsIso ((extendScalars φ).leftDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map π))) :=
    have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map π)) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (show QuasiIso π from inferInstance))
    inferInstance
  have hE : IsIso (DerivedCategory.Qh.map (((extendScalars φ).mapHomotopyCategory _).map
      ((HomotopyCategory.quotient _ _).map π))) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 h₃')
  have hn := (extendScalars φ).leftDerivedFunctorCounit.naturality
    ((HomotopyCategory.quotient _ _).map π)
  dsimp only [Functor.comp_map] at hn
  have : IsIso ((extendScalars φ).leftDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map π)) ≫
      (extendScalars φ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj P)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((extendScalars φ).leftDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map π))) _

end Complex

end CategoryTheory.Mod
