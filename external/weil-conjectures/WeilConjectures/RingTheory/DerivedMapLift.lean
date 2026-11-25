/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Algebra.Homology.PreciseVanishing
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Lifting maps from bounded projective complexes

Source: Stacks Project, derived.tex, Tag 064E (blueprint: lem-pc-ring-derived-map-lift).
-/

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

namespace RingTheory

/-- (blueprint: lem-pc-ring-derived-map-lift)
Let `R` be a ring and `n : ℤ`.  A bounded complex `P` of projective
`R`-modules which vanishes below `n` lifts maps through a derived morphism
which is an isomorphism above `n` and an epimorphism in degree `n`.
The proof follows the Stacks Project Tag 064E argument.  First complete
`α` to a distinguished triangle by (TR1), represent its cone by a complex,
and use the long exact cohomology sequence (`lem-sf-derived-homology-long-exact`)
to show that the cone has zero cohomology in every degree at least `n`.
Next apply precise vanishing (`lem-pc-ring-precise-vanishing`) to conclude
that the composite from `P` to the cone is zero.  Exactness of Hom into the
triangle (`lem-weil-pbc-hom-into-triangle-exact`) then gives a lift
`δ : Q.obj P ⟶ Q.obj E` of `β`.  Finally, the representative theorem
(`lem-pc-ring-derived-map-representative`) supplies a chain map `γ : P ⟶ E`
with `Q.map γ = δ`, yielding the displayed equality.
-/
theorem derived_map_lift
    (R : Type u) [Ring R]
    (n : ℤ)
    (P E L : CochainComplex (ModuleCat R) ℤ)
    (hbounded : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hprojective : ∀ i : ℤ, Projective (P.X i))
    (hbelow : ∀ i : ℤ, i < n → IsZero (P.X i))
    [HasDerivedCategory.{w} (ModuleCat R)]
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj L)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
    (hα_iso : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α))
    (hα_epi : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) n).map α)) :
    ∃ γ : P ⟶ E, DerivedCategory.Q.map γ ≫ α = β := by
  classical
  obtain ⟨a, b, ha, hb⟩ := hbounded
  have : P.IsStrictlyGE a := ha
  have : P.IsStrictlyLE b := hb
  have : ∀ i : ℤ, Projective (P.X i) := hprojective
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨C, g, d, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle α
  let T := Pretriangulated.Triangle.mk α g d
  have hC : ∀ i : ℤ, n ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj C) := by
    intro i hi
    have hEpi : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α) := by
      rcases eq_or_lt_of_le hi with rfl | hi
      · exact hα_epi
      · have := hα_iso i hi
        infer_instance
    have hIso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) (i + 1)).map α) :=
      hα_iso (i + 1) (by omega)
    apply (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂_iff.mpr
    constructor
    · exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mp hEpi
    · exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT i (i + 1)).mp (by
          change Mono ((DerivedCategory.homologyFunctor (ModuleCat R) (i + 1)).map α)
          infer_instance)
  let K := DerivedCategory.Q.objPreimage C
  let e : DerivedCategory.Q.obj K ≅ C := DerivedCategory.Q.objObjPreimageIso C
  have hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i) := by
    intro i hi
    exact (hC i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e)
  have hzero : β ≫ g = 0 := by
    have hz := precise_vanishing (ModuleCat R) P K n
      ⟨a, b, fun i hi ↦ P.isZero_of_isStrictlyGE a i hi,
        fun i hi ↦ P.isZero_of_isStrictlyLE b i hi⟩ hprojective hbelow hK
      (β ≫ g ≫ e.inv)
    simpa using congrArg (fun f ↦ f ≫ e.hom) hz
  obtain ⟨δ, hδ⟩ := T.coyoneda_exact₂ hT β hzero
  obtain ⟨γ, hγ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P E δ
  exact ⟨γ, by rw [hγ]; exact hδ.symm⟩

end RingTheory
