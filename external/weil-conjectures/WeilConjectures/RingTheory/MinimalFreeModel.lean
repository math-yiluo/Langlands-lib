/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.RingTheory.StablyFreeComplexLift
import WeilConjectures.RingTheory.ResidueCohomologySplit
import WeilConjectures.RingTheory.MinimalFreeComparison
import Mathlib.RingTheory.LocalRing.Module

/-!
# Minimal finite free models over local rings

Source: Stacks Project, More on Algebra, Tag 0BCC, lemma-lift-pseudo-coherent-from-residue-field
(blueprint: lem-sc-perfect-local-pseudocoherent-free-model).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace DerivedCategory

noncomputable section

private theorem free_iso_of_residue_finrank
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{max u v} R) [Module.Free R M] [Module.Finite R M]
    (n : ℕ)
    (h : Module.finrank (IsLocalRing.ResidueField R)
      ((ModuleCat.extendScalars (IsLocalRing.residue R)).obj M) = n) :
    Nonempty (M ≅ ModuleCat.of R (ULift.{v} (Fin n → R))) := by
  let := (IsLocalRing.residue R).toAlgebra
  have hrank : Module.finrank R M = n := by
    rw [← Module.finrank_baseChange (R := IsLocalRing.ResidueField R)]
    exact h
  exact ⟨((Module.finBasisOfFinrankEq R M hrank).equivFun.trans
    (ULift.moduleEquiv.symm)).toModuleIso⟩

private theorem isIso_of_residue_isIso
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : ModuleCat.{max u v} R}
    [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]
    (f : M ⟶ N)
    [IsIso ((ModuleCat.extendScalars (IsLocalRing.residue R)).map f)] : IsIso f := by
  let := (IsLocalRing.residue R).toAlgebra
  have hf := ConcreteCategory.bijective_of_isIso
    ((ModuleCat.extendScalars (IsLocalRing.residue R)).map f)
  change Function.Bijective (f.hom.baseChange (IsLocalRing.ResidueField R)) at hf
  rw [LinearMap.baseChange_eq_lTensor] at hf
  obtain ⟨g, hg⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f.hom).mpr hf.1
  have hgf : g.lTensor (IsLocalRing.ResidueField R) ∘ₗ
      f.hom.lTensor (IsLocalRing.ResidueField R) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hg, LinearMap.lTensor_id]
  have hginj : Function.Injective (g.lTensor (IsLocalRing.ResidueField R)) := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := hf.2 x
    obtain ⟨y, rfl⟩ := hf.2 y
    apply congrArg (f.hom.lTensor (IsLocalRing.ResidueField R))
    simpa only [← LinearMap.comp_apply, hgf, LinearMap.id_apply] using hxy
  obtain ⟨g', hg'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective g).mpr hginj
  have hgi : Function.Injective g := by
    intro x y hxy
    have := congrArg g' hxy
    simpa only [← LinearMap.comp_apply, hg', LinearMap.id_apply] using this
  have hfg : f.hom ∘ₗ g = LinearMap.id := by
    ext x
    apply hgi
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hg (g x)
  exact ⟨⟨ModuleCat.ofHom g, by ext x; exact LinearMap.congr_fun hg x,
    by ext x; exact LinearMap.congr_fun hfg x⟩⟩

/-- A pseudo-coherent object over a local ring has a bounded above finite free model with
ranks equal to the dimensions of its derived residue cohomology, unique as a complex.
Source: Stacks Project, More on Algebra, Tag 0BCC
(blueprint: lem-sc-perfect-local-pseudocoherent-free-model).
The finite free representative chosen from `hK` is bounded above, hence K-flat; its
termwise extension of scalars computes `K ⊗ᴸ κ`. Thus `hd` specifies the intrinsic ranks,
independently of the representative chosen by classical choice.

Proof:
1. Choose an upper bound for the nonzero `d i`. Split the residue complex over the field
   by choosing complements to boundaries in cycles and to cycles in terms. Its derived
   object is represented by the zero-differential complex with terms `κ^(d i)`.
2. Apply `lem-sc-pseudo-coherent-lift-stably-free-complex` (Tag 0BCB) with the maximal ideal.
   Every element of one plus that ideal is a unit. This lifts the residue complex to a
   bounded above finite free complex representing `K` with the prescribed reduction.
3. Reduction preserves finite free ranks, so the lifted term in degree `i` has rank `d i`.
   Transport the differentials along termwise isomorphisms to the displayed free modules.
4. For uniqueness, `lem-pc-ring-derived-map-representative` represents a derived isomorphism
   and its inverse by chain maps, whose composites are homotopic to the identities.
   `lem-pc-module-bounded-flat-kflat` identifies termwise reduction with derived reduction.
   The formula dim H^i = dim C^i - rank d^i - rank d^(i-1) forces both reduced differentials
   to vanish. The reduced comparison is therefore a termwise isomorphism. Nakayama
   (`lem-weil-pbc-nakayama-local-generators`) makes each comparison surjective; splitting
   onto its free target and applying Nakayama to the finite kernel makes it injective.
   Consequently the comparison is an isomorphism of complexes. -/
theorem exists_unique_minimalFreeModel
    {R : Type u} [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (d : ℤ → ℕ)
    (hfinite : ∀ i : ℤ, Module.Finite (IsLocalRing.ResidueField R)
      ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i))
    (hd : ∀ i : ℤ, d i = Module.finrank (IsLocalRing.ResidueField R)
      ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i))
    (hbound : ∃ b : ℤ, ∀ i : ℤ, b < i → d i = 0) :
    ∃ F : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, F.IsStrictlyLE b) ∧ Nonempty (Q.obj F ≅ K) ∧
      (∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))) ∧
      (∀ G : CochainComplex (ModuleCat.{max u v} R) ℤ,
        (∃ b : ℤ, G.IsStrictlyLE b) → Nonempty (Q.obj G ≅ K) →
        (∀ i : ℤ, Nonempty (G.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))) →
        Nonempty (F ≅ G)) := by
  classical
  let κ := IsLocalRing.ResidueField R
  let E : CochainComplex (ModuleCat.{max u v} κ) ℤ :=
    { X := fun i ↦ ModuleCat.of κ (ULift.{v} (Fin (d i) → κ))
      d := fun _ _ ↦ 0 }
  have hEterms (i : ℤ) :
      Nonempty (E.X i ≅ ModuleCat.of κ (ULift.{v} (Fin (d i) → κ))) :=
    ⟨Iso.refl _⟩
  have hEbound : ∃ b : ℤ, E.IsStrictlyLE b := by
    obtain ⟨b, hb⟩ := hbound
    refine ⟨b, (E.isStrictlyLE_iff b).mpr ?_⟩
    intro i hi
    change CategoryTheory.Limits.IsZero (ModuleCat.of κ (ULift.{v} (Fin (d i) → κ)))
    rw [hb i hi]
    exact ModuleCat.isZero_of_subsingleton _
  let C := ((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (Classical.choose hK)
  obtain ⟨φ, hφ⟩ := CochainComplex.exists_quasiIso_from_zeroDifferential
    C E d hfinite hd (fun _ _ ↦ rfl) hEterms
  let : HasDerivedCategory.{max (u + 1) (v + 1)} (ModuleCat.{max u v} κ) :=
    HasDerivedCategory.standard (ModuleCat.{max u v} κ)
  let : HasDerivedCategory.{max (u + 1) (v + 1)}
      (ModuleCat.{max u v} (R ⧸ IsLocalRing.maximalIdeal R)) :=
    inferInstanceAs (HasDerivedCategory.{max (u + 1) (v + 1)} (ModuleCat.{max u v} κ))
  have : QuasiIso φ := hφ
  have hE : Nonempty (Q.obj C ≅ Q.obj E) := ⟨(asIso (Q.map φ)).symm⟩
  have hunits : ∀ x : IsLocalRing.maximalIdeal R, IsUnit (1 + (x : R)) := by
    intro x
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    rw [IsLocalRing.jacobson_eq_maximalIdeal, add_sub_cancel_left]
    · exact x.property
    · exact bot_ne_top
  obtain ⟨P, hPbound, hPterms, hPK, ⟨e⟩, hPfree⟩ :=
    exists_stablyFree_lift_mod_ideal (IsLocalRing.maximalIdeal R) hunits K hK E
      hEbound (fun i ↦ by
        change Module.Finite κ (ULift.{v} (Fin (d i) → κ)) ∧
          Module.IsStablyFree κ (ULift.{v} (Fin (d i) → κ))
        exact ⟨inferInstance, inferInstance⟩) hE
  have hPrank (i : ℤ) :
      Nonempty (P.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R))) := by
    have : Module.Finite R (P.X i) := (hPterms i).1
    have : Module.Free R (P.X i) := hPfree i (by
      change Module.Free κ (ULift.{v} (Fin (d i) → κ)); infer_instance)
    apply free_iso_of_residue_finrank (P.X i) (d i)
    have hi := ((HomologicalComplex.eval _ _ i).mapIso e).toLinearEquiv.finrank_eq
    change Module.finrank κ ((ModuleCat.extendScalars (IsLocalRing.residue R)).obj
      (P.X i)) = Module.finrank κ (ULift.{v} (Fin (d i) → κ)) at hi
    rw [hi, ULift.moduleEquiv.finrank_eq]
    simp
  refine ⟨P, hPbound, hPK, hPrank, ?_⟩
  intro G hGbound hGK hGterms
  obtain ⟨β, hβ⟩ := exists_minimalFree_comparison_residue
    K hK d hd P G hPbound hGbound hPK hGK hPrank hGterms
  have (i : ℤ) : IsIso (β.f i) := by
    have : Module.Finite R (P.X i) := (hPterms i).1
    have : Module.Free R (P.X i) := hPfree i (by
      change Module.Free κ (ULift.{v} (Fin (d i) → κ)); infer_instance)
    let eG := (hGterms i).some.toLinearEquiv
    have : Module.Finite R (G.X i) := Module.Finite.equiv eG.symm
    have : Module.Free R (G.X i) := Module.Free.of_equiv eG.symm
    have := hβ i
    exact isIso_of_residue_isIso (β.f i)
  have : IsIso β := HomologicalComplex.Hom.isIso_of_components β
  exact ⟨asIso β⟩

end

end DerivedCategory
