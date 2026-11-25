/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Stabilizing towers of cochain approximations

Source: Stacks Project, Tag 064U, passage from descending approximations to a complex.
(blueprint: lem-pc-ring-stabilizing-cone-tower).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- All composites after an index at which the individual maps are invertible are
invertible. -/
private theorem sequence_eventuallyConstant {D : Type*} [Category D]
    {P : ℕ → D} (j : ∀ k, P k ⟶ P (k + 1)) (k : ℕ)
    (h : ∀ l : ℕ, k ≤ l → IsIso (j l)) :
    (Functor.ofSequence j).IsEventuallyConstantFrom k := by
  intro l φ
  have hl := leOfHom φ
  obtain rfl : φ = homOfLE hl := Subsingleton.elim _ _
  induction l, hl using Nat.le_induction with
  | base =>
    rw [show homOfLE (Nat.le_refl k) = 𝟙 k from rfl, CategoryTheory.Functor.map_id]
    infer_instance
  | succ l hl ih =>
    have : IsIso (j l) := h l hl
    have heq : (Functor.ofSequence j).map (homOfLE (by omega : k ≤ l + 1)) =
        (Functor.ofSequence j).map (homOfLE hl) ≫ j l := by
      rw [← Functor.ofSequence_map_homOfLE_succ j l, ← Functor.map_comp]
      rfl
    rw [heq]
    infer_instance

/-- A degreewise stabilizing sequence of increasingly accurate approximations gives
an actual quasi-isomorphism, with each term isomorphic to a term of a finite stage.
No finiteness or support hypothesis on the stages is needed for this assembly step.

Source: Stacks Project, More on Algebra, Tag 064U, proof of (2) implies (1), assembly
of the descending construction.
(blueprint: lem-pc-ring-stabilizing-cone-tower).

Proof: Form the sequential diagram with objects `P k` and maps `j k`. Use Mathlib's
`HomologicalComplex.coconeOfHasColimitEval`: its term in degree i is the colimit
of the degree-i modules, and its differential is induced by the stage differentials.
This is a real construction from module colimits; their universal property uniquely
determines the objects up to the isomorphisms used here. The equations in hcomm
give a cocone with point C and therefore a chain map g from the constructed complex.
For any k with b+1-k ≤ i, all degree-i transitions after k are invertible. Prove by
induction on the target index that their composites are invertible. Mathlib's
`Functor.IsEventuallyConstantFrom.isIso_ι_of_isColimit` then makes the degree-i
colimit inclusion from stage k invertible.
To check cohomology in degree i take k = max(0,b+2-i), implemented with Int.toNat.
The three inclusions in degrees i-1,i,i+1 are invertible; the corresponding map of
short complexes is a quasi-isomorphism, by
`ShortComplex.quasiIso_of_epi_of_isIso_of_mono`. The stage cone is zero in
cohomology in degrees i-1 and i. In the long exact sequence this makes H^i(f k)
mono and epi, hence invertible. Factor f k as the stage inclusion followed by g
and use cancellation of degree-i quasi-isomorphisms. Thus g is a quasi-isomorphism
in every degree. For the term comparison use k = max(0,b+1-i) and the inverse
of the degree-i colimit inclusion. This requires neither finite generation nor
support bounds on the stages. Zero complexes and the zero ring work as well. -/
theorem exists_model_of_stabilizing_cone_tower (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    (P : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (f : ∀ k : ℕ, P k ⟶ C) (j : ∀ k : ℕ, P k ⟶ P (k + 1))
    (hcomm : ∀ k : ℕ, j k ≫ f (k + 1) = f k)
    (hstable : ∀ (k : ℕ) (i : ℤ), b + 1 - (k : ℤ) ≤ i → IsIso ((j k).f i))
    (hvan : ∀ (k : ℕ) (i : ℤ), b + 1 - (k : ℤ) ≤ i → IsZero
      ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone (f k))))) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ) (g : F ⟶ C), QuasiIso g ∧
      ∀ i : ℤ, ∃ k : ℕ, Nonempty (F.X i ≅ (P k).X i) := by
  classical
  let D := Functor.ofSequence j
  let c := HomologicalComplex.coconeOfHasColimitEval D
  let hc := HomologicalComplex.isColimitCoconeOfHasColimitEval D
  let s : Cocone D :=
    { pt := C
      ι := NatTrans.ofSequence f (fun k => by simpa [D] using hcomm k) }
  let g : c.pt ⟶ C := hc.desc s
  have hfac (k : ℕ) : c.ι.app k ≫ g = f k := hc.fac s k
  have hι (k : ℕ) (i : ℤ) (hi : b + 1 - (k : ℤ) ≤ i) :
      IsIso ((c.ι.app k).f i) := by
    have he : Functor.IsEventuallyConstantFrom
        (D ⋙ HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i) k := by
      let q (l : ℕ) : (P l).X i ⟶ (P (l + 1)).X i := (j l).f i
      have H := sequence_eventuallyConstant q k (fun l hl => hstable l i (by omega))
      intro l φ
      have hm : (Functor.ofSequence q).map φ =
          (D ⋙ HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map φ := by
        have hn := leOfHom φ
        obtain rfl : φ = homOfLE hn := Subsingleton.elim _ _
        induction l, hn using Nat.le_induction with
        | base => simp; rfl
        | succ l hl ih =>
          rw [show homOfLE (by omega : k ≤ l + 1) =
            homOfLE hl ≫ homOfLE (Nat.le_add_right l 1) from rfl]
          simp only [Functor.map_comp, ih]
          congr 1
          simp [D, q]
      rw [← hm]
      exact H φ
    exact he.isIso_ι_of_isColimit (colimit.isColimit _)
  refine ⟨c.pt, g, ?_, ?_⟩
  · rw [quasiIso_iff]
    intro i
    let k := (b + 2 - i).toNat
    have hk : b + 1 - (k : ℤ) ≤ i - 1 := by
      dsimp [k]
      omega
    have hprev : (ComplexShape.up ℤ).prev i = i - 1 := by
      exact ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (i - 1) i by
        change i - 1 + 1 = i
        omega)
    have hnext : (ComplexShape.up ℤ).next i = i + 1 :=
      ComplexShape.next_eq' _ rfl
    have : IsIso ((c.ι.app k).f (i - 1)) := hι k (i - 1) hk
    have : IsIso ((c.ι.app k).f i) := hι k i (by omega)
    have : IsIso ((c.ι.app k).f (i + 1)) := hι k (i + 1) (by omega)
    have hqι : QuasiIsoAt (c.ι.app k) i := by
      rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) hprev hnext]
      let t := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
        (ComplexShape.up ℤ) (i - 1) i (i + 1)).map (c.ι.app k)
      have : Epi t.τ₁ := by
        change Epi ((c.ι.app k).f (i - 1))
        infer_instance
      have : IsIso t.τ₂ := by
        change IsIso ((c.ι.app k).f i)
        infer_instance
      have : Mono t.τ₃ := by
        change Mono ((c.ι.app k).f (i + 1))
        infer_instance
      exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono t
    have hqf : QuasiIsoAt (f k) i := by
      let T := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f k))
      have hT := mappingCone_triangle_distinguished (f k)
      have hm : Mono ((homologyFunctor (ModuleCat.{v} R) i).map (Q.map (f k))) :=
        (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
          ((hvan k (i - 1) hk).eq_of_src _ _)
      have he : Epi ((homologyFunctor (ModuleCat.{v} R) i).map (Q.map (f k))) :=
        (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
          ((hvan k i (by omega)).eq_of_tgt _ _)
      have hq : IsIso ((homologyFunctor (ModuleCat.{v} R) i).map (Q.map (f k))) :=
        isIso_of_mono_of_epi _
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (NatIso.isIso_map_iff (homologyFunctorFactors (ModuleCat.{v} R) i) (f k)).1 hq
    have : QuasiIsoAt (c.ι.app k ≫ g) i := by rw [hfac]; exact hqf
    exact quasiIsoAt_of_comp_left (c.ι.app k) g i
  · intro i
    let k := (b + 1 - i).toNat
    have hi : b + 1 - (k : ℤ) ≤ i := by dsimp [k]; omega
    have := hι k i hi
    exact ⟨k, ⟨(asIso ((c.ι.app k).f i)).symm⟩⟩

end DerivedCategory
