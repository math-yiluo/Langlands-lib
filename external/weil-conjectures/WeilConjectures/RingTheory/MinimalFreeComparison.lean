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
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Comparisons of minimal free models after reduction

Source: Stacks Project, More on Algebra, Tag 0BCC, uniqueness paragraph.
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace DerivedCategory

private theorem nonempty_homotopyEquiv_of_derivedIso
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (F G : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [F.IsKProjective] [G.IsKProjective] (e : Q.obj F ≅ Q.obj G) :
    Nonempty (HomotopyEquiv F G) := by
  let e' := (quotientCompQhIso (ModuleCat.{max u v} R)).app F ≪≫ e ≪≫
    ((quotientCompQhIso (ModuleCat.{max u v} R)).app G).symm
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective F
    ((HomotopyCategory.quotient _ _).obj G)).surjective e'.hom
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective G
    ((HomotopyCategory.quotient _ _).obj F)).surjective e'.inv
  have hfg : f ≫ g = 𝟙 _ := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective F
      ((HomotopyCategory.quotient _ _).obj F)).injective
    simp only [Functor.map_comp, hf, hg, Iso.hom_inv_id]
    exact (Qh.map_id _).symm
  have hgf : g ≫ f = 𝟙 _ := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective G
      ((HomotopyCategory.quotient _ _).obj G)).injective
    simp only [Functor.map_comp, hg, hf, Iso.inv_hom_id]
    exact (Qh.map_id _).symm
  exact ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩

private theorem differential_eq_zero_of_finrank_homology
    {κ : Type u} [Field κ]
    (C : CochainComplex (ModuleCat.{max u v} κ) ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite κ (C.X i))
    (hdim : ∀ i : ℤ, Module.finrank κ (C.homology i) = Module.finrank κ (C.X i)) :
    ∀ i j : ℤ, C.d i j = 0 := by
  intro i j
  have : Module.Finite κ (C.X i) := hfinite i
  have hi := (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
  have hp := (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance
  have : Module.Finite κ (C.cycles i) := Module.Finite.of_injective (C.iCycles i).hom hi
  have : Module.Finite κ (C.homology i) :=
    Module.Finite.of_surjective (C.homologyπ i).hom hp
  have hrank : Module.finrank κ (C.cycles i) = Module.finrank κ (C.X i) :=
    Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hi) (by
      rw [← hdim i]
      exact LinearMap.finrank_le_finrank_of_surjective hp)
  have hsurj : Function.Surjective (C.iCycles i).hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hi
  have : Epi (C.iCycles i) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  apply (cancel_epi (C.iCycles i)).mp
  rw [CategoryTheory.Limits.comp_zero]
  exact C.iCycles_d i j

private theorem residue_finite_finrank
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{max u v} R) (n : ℕ)
    (h : Nonempty (M ≅ ModuleCat.of R (ULift.{v} (Fin n → R)))) :
    Module.Finite (IsLocalRing.ResidueField R)
      ((ModuleCat.extendScalars (IsLocalRing.residue R)).obj M) ∧
    Module.finrank (IsLocalRing.ResidueField R)
      ((ModuleCat.extendScalars (IsLocalRing.residue R)).obj M) = n := by
  classical
  let e := h.some.toLinearEquiv
  have : Module.Free R M := Module.Free.of_equiv e.symm
  have : Module.Finite R M := Module.Finite.equiv e.symm
  let := (IsLocalRing.residue R).toAlgebra
  constructor
  · change Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)
    infer_instance
  · change Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = n
    rw [Module.finrank_baseChange, e.finrank_eq, ULift.moduleEquiv.finrank_eq]
    simp

private theorem component_isIso_of_zeroDifferential
    {κ : Type u} [Field κ]
    {F G : CochainComplex (ModuleCat.{max u v} κ) ℤ}
    (hF : ∀ i j : ℤ, F.d i j = 0) (hG : ∀ i j : ℤ, G.d i j = 0)
    (f : F ⟶ G) [QuasiIso f] (i : ℤ) : IsIso (f.f i) := by
  have : IsIso (F.iCycles i) := F.isIso_iCycles i _ rfl (hF _ _)
  have : IsIso (G.iCycles i) := G.isIso_iCycles i _ rfl (hG _ _)
  have : IsIso (F.homologyπ i) := F.isIso_homologyπ _ i rfl (hF _ _)
  have : IsIso (G.homologyπ i) := G.isIso_homologyπ _ i rfl (hG _ _)
  have : IsIso (HomologicalComplex.cyclesMap f i ≫ G.homologyπ i) := by
    rw [← HomologicalComplex.homologyπ_naturality]
    infer_instance
  have : IsIso (HomologicalComplex.cyclesMap f i) :=
    IsIso.of_isIso_comp_right _ (G.homologyπ i)
  have : IsIso (F.iCycles i ≫ f.f i) := by
    rw [← HomologicalComplex.cyclesMap_i]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.iCycles i) (f.f i)

/-- Two bounded above free representatives with minimal ranks admit a chain comparison
which is an isomorphism in every degree after reduction to the residue field.
Source: Stacks Project, More on Algebra, Tag 0BCC, uniqueness paragraph
(blueprint: lem-sc-minimal-free-comparison-residue).

Proof: The bounded above free complexes F and G are K-projective. The bijection from
homotopy classes of chain maps to derived morphisms represents the derived isomorphism
between them and its inverse by chain maps β and α. Injectivity of that bijection shows
that αβ and βα are homotopic to the identities. Extending scalars preserves these
homotopies. Hence the reduced comparison β is a homotopy equivalence.
The same applies to comparisons with the bounded above free representative chosen by
hK, so the reduced F and G have cohomology dimensions d_i. Their term dimensions are
also d_i, by base change of the given free bases. In each degree, the equality between
term dimension and cohomology dimension forces both the incoming and outgoing
reduced differentials to vanish: dim C_i = dim H_i + rank d_(i-1) + rank d_i.
The reduced comparison is a quasi-isomorphism between zero-differential complexes,
so each of its components is an isomorphism. This theorem stops before the Nakayama
argument which lifts these component isomorphisms to the original ring. -/
theorem exists_minimalFree_comparison_residue
    {R : Type u} [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (d : ℤ → ℕ)
    (hd : ∀ i : ℤ, d i = Module.finrank (IsLocalRing.ResidueField R)
      ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i))
    (F G : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hFbound : ∃ b : ℤ, F.IsStrictlyLE b)
    (hGbound : ∃ b : ℤ, G.IsStrictlyLE b)
    (hF : Nonempty (Q.obj F ≅ K)) (hG : Nonempty (Q.obj G ≅ K))
    (hFterms : ∀ i : ℤ,
      Nonempty (F.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R))))
    (hGterms : ∀ i : ℤ,
      Nonempty (G.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))) :
    ∃ β : F ⟶ G,
      ∀ i : ℤ, IsIso ((ModuleCat.extendScalars (IsLocalRing.residue R)).map (β.f i)) :=
  by
    classical
    let C := Classical.choose hK
    obtain ⟨bC, hCbound, hCterms, ⟨eCK⟩⟩ := Classical.choose_spec hK
    have (i : ℤ) : Module.Free R (C.X i) := (hCterms i).1
    have (i : ℤ) : Projective (C.X i) := inferInstance
    have : C.IsStrictlyLE bC := hCbound
    have : C.IsKProjective := CochainComplex.isKProjective_of_projective C bC
    have : (ModuleCat.extendScalars.{u, u, max u v} (IsLocalRing.residue R)).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue R)).left_adjoint_additive
    let T := (ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    have hzero (Z : CochainComplex (ModuleCat.{max u v} R) ℤ)
        (hZbound : ∃ b : ℤ, Z.IsStrictlyLE b) (hZK : Nonempty (Q.obj Z ≅ K))
        (hZterms : ∀ i : ℤ,
          Nonempty (Z.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))) :
        ∀ i j : ℤ, (T.obj Z).d i j = 0 := by
      have (i : ℤ) : Module.Free R (Z.X i) :=
        Module.Free.of_equiv (hZterms i).some.toLinearEquiv.symm
      have (i : ℤ) : Projective (Z.X i) := inferInstance
      obtain ⟨bZ, hZb⟩ := hZbound
      have : Z.IsStrictlyLE bZ := hZb
      have : Z.IsKProjective := CochainComplex.isKProjective_of_projective Z bZ
      obtain ⟨eCZ⟩ := nonempty_homotopyEquiv_of_derivedIso C Z (eCK ≪≫ hZK.some.symm)
      let e := (ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomotopyEquiv eCZ
      have : QuasiIso e.hom := inferInstance
      apply differential_eq_zero_of_finrank_homology (T.obj Z)
      · intro i
        exact (residue_finite_finrank (Z.X i) (d i) (hZterms i)).1
      · intro i
        have hi := (isoOfQuasiIsoAt e.hom i).toLinearEquiv.finrank_eq
        rw [← hi, ← hd i]
        exact (residue_finite_finrank (Z.X i) (d i) (hZterms i)).2.symm
    have (i : ℤ) : Module.Free R (F.X i) :=
      Module.Free.of_equiv (hFterms i).some.toLinearEquiv.symm
    have (i : ℤ) : Module.Free R (G.X i) :=
      Module.Free.of_equiv (hGterms i).some.toLinearEquiv.symm
    have (i : ℤ) : Projective (F.X i) := inferInstance
    have (i : ℤ) : Projective (G.X i) := inferInstance
    obtain ⟨bF, hFb⟩ := hFbound
    obtain ⟨bG, hGb⟩ := hGbound
    have : F.IsStrictlyLE bF := hFb
    have : G.IsStrictlyLE bG := hGb
    have : F.IsKProjective := CochainComplex.isKProjective_of_projective F bF
    have : G.IsKProjective := CochainComplex.isKProjective_of_projective G bG
    obtain ⟨eFG⟩ := nonempty_homotopyEquiv_of_derivedIso F G (hF.some ≪≫ hG.some.symm)
    let e := (ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomotopyEquiv eFG
    have : QuasiIso e.hom := inferInstance
    refine ⟨eFG.hom, fun i ↦ ?_⟩
    exact component_isIso_of_zeroDifferential
      (hzero F ⟨bF, hFb⟩ hF hFterms) (hzero G ⟨bG, hGb⟩ hG hGterms) e.hom i

end DerivedCategory
