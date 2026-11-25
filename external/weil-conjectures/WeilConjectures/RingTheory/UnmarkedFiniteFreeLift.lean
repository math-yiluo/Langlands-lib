/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.RingTheory.StablyFreeComplexLift
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal
import all WeilConjectures.RingTheory.NilpotentProjectiveComplexLift

@[expose] public section
set_option autoImplicit false
universe u v w w'
open CategoryTheory
namespace DerivedCategory

set_option linter.unusedVariables false in
/-- The unmarked finite-free lifting data needed before checking the prescribed marking.
Source: Stacks Project, More on Algebra, Tags 0H76 and 0BCB.
(auxiliary; not a blueprint node)
The construction first lifts a bounded-above finite-free model through the nilpotent
quotient, retaining the upper bound and finite freeness. The remaining compatibility
with the prescribed derived marking is a separate comparison argument.
-/
theorem exists_unmarked_finiteFree_lift_of_nilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) := by
  classical
  -- Use the bounded finite-free representative supplied by pseudo-coherence.
  let E := Classical.choose hK
  obtain ⟨c, hc, hEterms, ⟨γ⟩⟩ := Classical.choose_spec hK
  let : E.IsStrictlyLE c := hc
  have hEproj (i : ℤ) : Module.Projective R (E.X i) := by
    have : Module.Free R (E.X i) := (hEterms i).1
    infer_instance
  obtain ⟨ecomp⟩ := CochainComplex.projective_reduction_comparison
    (Ideal.Quotient.mk I) L ε E c hEproj
  have hred : Nonempty (Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj E) ≅ Q.obj F) :=
    ⟨ecomp.symm ≪≫ L.mapIso γ ≪≫ α⟩
  have hFstable (i : ℤ) :
      Module.Finite (R ⧸ I) (F.X i) ∧ Module.IsStablyFree (R ⧸ I) (F.X i) := by
    have : Module.Free (R ⧸ I) (F.X i) := (hFterms i).1
    exact ⟨(hFterms i).2, inferInstance⟩
  -- Tag 0BCB lifts the complex and detects freeness of every term.
  obtain ⟨P, _, hPterms, ⟨β⟩, ⟨θ⟩, hPfree⟩ :=
    exists_stablyFree_lift_mod_ideal I hunits K hK F ⟨b, hFbound⟩ hFstable hred
  refine ⟨P, β, θ, (P.isStrictlyLE_iff b).2 ?_, ?_⟩
  · intro i hi
    -- A finite module with zero reduction is zero by Nakayama.
    have hzero := ((F.isStrictlyLE_iff b).1 hFbound i hi).of_iso
      ((HomologicalComplex.eval _ _ i).mapIso θ)
    have : Subsingleton ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (P.X i)) :=
      ModuleCat.subsingleton_of_isZero hzero
    have : Module.Finite R (P.X i) := (hPterms i).1
    have hs : Function.Surjective (0 : P.X i ⟶ P.X i) :=
      ModuleCat.surjective_of_extendScalars_mod_ideal I hunits (P.X i) (P.X i) 0
        (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
    have : Subsingleton (P.X i) := ⟨fun x y ↦ by
      obtain ⟨a, ha⟩ := hs x
      obtain ⟨a', ha'⟩ := hs y
      exact ha.symm.trans ha'⟩
    exact ModuleCat.isZero_of_subsingleton _
  · intro i
    exact ⟨hPfree i (hFterms i).1, (hPterms i).1⟩

end DerivedCategory
